(** Confirm-by-mutation for the engine_queue family. Each of the three gates on
    the engine's single execution slot is deleted on its own, and the suite
    asserts the FULL 3x3 verdict matrix - which statement flips and, just as
    importantly, which ones do not. A pin that passed only because some other
    statement in the family flipped cannot hide behind a "some proof failed"
    assertion here.

    - {!Engine_queue_model.No_slot_exclusion} deletes the
      [self.pending_task.is_none() &&] conjunct at engine/lib.rs:227, keeping
      [!self.queued.is_empty()], so the loop spawns a second blocking task while
      the first is still running. Both clone the same [self.parent_header]
      (:126), and [self.pending_task = Some(...)] (:229) drops the first
      receiver, so the first task's blocks are committed while :268 never
      installs its header. No sibling repairs it: state lookup is by parent hash
      and a duplicate parent is still a valid state root
      (tn-reth/lib.rs:736-739); [save_blocks]/[commit] applies no contiguity or
      duplicate-height check (:941-944); [push_latest] appends with no dedup and
      no monotonic round check (recent_blocks.rs:40-60); the only other writer of
      [pending_task] is the release arm at :266; and the only identity-keyed
      guard is startup-only, its doc conceding "replaying output the engine
      already applied causes double execution" (node/start_epoch.rs:60-64,
      :71-93). The engine's own comment at :135-136 says the single [Option] IS
      the semaphore. Refutes S1 (both conjuncts, one step apart). Leaves S2 and
      S3 intact.
    - {!Engine_queue_model.No_queue_bound} deletes
      [self.queued.len() < MAX_QUEUED_OUTPUTS] from the select arm at
      engine/lib.rs:245, so the engine keeps draining the [to_engine] channel
      while a task is in flight. No sibling bound re-establishes it:
      [TO_ENGINE_CAPACITY = 64] (node.rs:60-68, :838) bounds the hop upstream and
      becomes a supply once the engine stops refusing - its own doc says a deep
      channel "would defeat the engine's bound by buffering the backlog one hop
      upstream" - and crates/engine/src/lib.rs has no eviction, no [truncate] and
      no second capacity check; the only writers of [queued] are the [push_back]
      at :249, the [pop_front] at :124 and a [cfg(test)] helper at :179-182.
      Refutes S2 (its bound and backpressure conjuncts). Leaves S1 and S3 intact.
    - {!Engine_queue_model.Reexecute_head} deletes the removal from
      [self.queued.pop_front()] at engine/lib.rs:124, so the head is re-granted on
      every loop iteration and everything behind it starves. No sibling notices a
      re-execution: no already-executed check keyed on the consensus digest in
      [execute_consensus_output] (payload_builder.rs:22-36), no duplicate
      rejection in [finish_executing_output] (tn-reth/lib.rs:941-944), no dedup
      or monotonic round check in [push_latest] (recent_blocks.rs:40-60), and
      [replay_missed_consensus] (node/start_epoch.rs:71-93) is startup-only.
      Refutes S3 (both its safety conjuncts) and, honestly reported, ALSO S2's
      gate-reopens conjunct: a backlog whose head is never removed never
      shortens, so the gate stays shut. That collateral is asserted as its own
      case rather than hidden, and it is why S2's pin is
      {!Engine_queue_model.No_queue_bound} - the gate S2 is actually about.
      Leaves S1 intact. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Engine_queue_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Engine_queue_model.Checker.make (Engine_queue_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Engine_queue_statements.name name))
    Engine_queue_statements.all

(** Assert one statement's verdict under one mutation. *)
let verdict_under mut name want () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ if want then " proves" else " flips to refuted")
            want
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Engine_queue_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name = verdict_under mut name false

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name = verdict_under Engine_queue_model.Pristine name true

(** The control half of the matrix: this mutation leaves this statement alone,
    so the flip above is attributable to the gate and not to collateral damage
    in the reachable set. *)
let survives_under mut name = verdict_under mut name true

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The unaffected rows of one mutation's column. *)
let controls mut names =
  List.map
    (fun n -> Alcotest.test_case (n ^ ":survives") `Quick (survives_under mut n))
    names

(** S1. *)
let s1 = "single-execution-slot-chains-each-output-onto-the-committed-head"

(** S2. *)
let s2 = "engine-backlog-bound-backpressures-upstream-and-reopens"

(** S3. *)
let s3 = "execution-slot-is-a-one-shot-grant-no-output-monopolises-it"

let () =
  Alcotest.run "engine_queue_mutation"
    [
      ( "deleted slot exclusion races two tasks onto one parent",
        pin Engine_queue_model.No_slot_exclusion s1
        @ controls Engine_queue_model.No_slot_exclusion [ s2; s3 ] );
      ( "deleted queue bound buffers instead of backpressuring",
        pin Engine_queue_model.No_queue_bound s2
        @ controls Engine_queue_model.No_queue_bound [ s1; s3 ] );
      ( "non-consuming grant lets one output hold the slot forever",
        pin Engine_queue_model.Reexecute_head s3
        @ [
            Alcotest.test_case (s2 ^ ":also-flips") `Quick
              (refuted_under Engine_queue_model.Reexecute_head s2);
          ]
        @ controls Engine_queue_model.Reexecute_head [ s1 ] );
    ]
