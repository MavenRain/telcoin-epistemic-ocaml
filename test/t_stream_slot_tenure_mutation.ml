(** Confirm-by-mutation for the stream_slot_tenure family. Each of the three
    gates on one [(peer, request_digest)] admission entry is deleted on its own,
    and the suite asserts the FULL 3x3 verdict matrix - which statement flips
    and, just as importantly, which ones do not. A pin that passed only because
    some other statement in the family flipped cannot hide behind a "some proof
    failed" assertion here.

    - {!Stream_slot_tenure_model.No_stale_prune} deletes the retain body of
      [cleanup_stale_pending_requests] (mod.rs:1453-1455), keeping the interval
      tick (mod.rs:1442-1444) so time still passes. The abandoned reservation is
      then held on every path. No sibling repairs it: the only other removal is
      the consuming lookup at mod.rs:1843-1845, which needs the peer to open the
      correlated stream - precisely what the refuting branch's peer never does -
      and the permit has no timeout of its own, being a field of the map value
      (mod.rs:206-208). Refutes S1 (its release conjunct) and, honestly
      reported, also S2's release conjunct: eviction and non-rearming are
      jointly necessary for release, and S2's weak-until conjunct is what
      separates the two gates. Leaves S3 intact.
    - {!Stream_slot_tenure_model.Rearm_created_at} deletes the timestamp
      preservation at mod.rs:1683-1686, so every repeat RPC mints a fresh
      [created_at]. A peer re-requesting once per interval holds the slot
      forever. No sibling bounds tenure: the cleanup predicate reads only
      [created_at], the per-peer cap (mod.rs:1664-1667) bounds damage without
      freeing anything, and the global semaphore cannot revoke a held permit.
      Refutes S2 only - the abandoned branch of S1 never re-requests, and the
      consume-on-open gate of S3 is untouched.
    - {!Stream_slot_tenure_model.Non_consuming_open} weakens the lookup at
      mod.rs:1843-1845 from [remove] to [get]. The entry survives its serve, so
      a second open inside the same cleanup interval is served again with no
      penalty. No sibling repairs it: no served-flag in the serve function
      (handler.rs:1151-1199), no per-peer or per-digest gate on the inbound
      stream dispatch (mod.rs:1507-1510), and the cleanup only bounds replays in
      time. Refutes S3 alone. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Stream_slot_tenure_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Stream_slot_tenure_model.Checker.make
       (Stream_slot_tenure_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Stream_slot_tenure_statements.name name))
    Stream_slot_tenure_statements.all

(** Assert one statement's verdict under one mutation. *)
let verdict_under mut name want () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ (if want then " proves" else " flips to refuted"))
            want
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Stream_slot_tenure_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name = verdict_under mut name false

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name =
  verdict_under Stream_slot_tenure_model.Pristine name true

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
let s1 = "abandoned-admission-slot-released-without-peer-cooperation"

(** S2. *)
let s2 = "re-request-never-extends-admission-slot-tenure"

(** S3. *)
let s3 = "admitted-stream-request-serves-at-most-once"

let () =
  Alcotest.run "stream_slot_tenure_mutation"
    [
      ( "deleted timeout eviction strands the abandoned reservation",
        pin Stream_slot_tenure_model.No_stale_prune s1
        @ [
            Alcotest.test_case (s2 ^ ":also-flips") `Quick
              (refuted_under Stream_slot_tenure_model.No_stale_prune s2);
          ]
        @ controls Stream_slot_tenure_model.No_stale_prune [ s3 ] );
      ( "re-armed created_at lets a request loop hold the slot forever",
        pin Stream_slot_tenure_model.Rearm_created_at s2
        @ controls Stream_slot_tenure_model.Rearm_created_at [ s1; s3 ] );
      ( "non-consuming stream lookup lets one admission be served twice",
        pin Stream_slot_tenure_model.Non_consuming_open s3
        @ controls Stream_slot_tenure_model.Non_consuming_open [ s1; s2 ] );
    ]
