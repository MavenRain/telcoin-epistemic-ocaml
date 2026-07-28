(** Confirm-by-mutation pins for the BATCH_QUORUM_TALLY family. Each group
    deletes ONE gate of the quorum waiter's stake arithmetic and asserts the
    per-statement verdict on both sides, so a pin cannot pass because some OTHER
    statement happened to flip.

    - {!Batch_quorum_tally_model.No_author_self_credit} deletes the
      [+ total_stake] of
      crates/consensus/worker/src/quorum_waiter.rs:168-170, dropping the
      rejection budget from (3 + 1) - 3 = 1 to 3 - 3 = 0. No sibling re-imposes
      "two rejections": the availability exit at :241-243 is untripped by one
      rejection (1 + 2 >= 3), the exhausted-peer exit at :220-223 needs every
      task resolved, and the quorum test at :190 pre-empts only under a schedule
      that puts two acks first - schedule-dependence, not a repair, and the
      model has that schedule freedom.
    - {!Batch_quorum_tally_model.No_recoverable_class} deletes the
      [Self::RecoverableError(...)] arm at network/message.rs:135-137. THE RETRY
      LOOP DOES NOT REPAIR IT: quorum_waiter.rs:101-113 retries every error
      EXCEPT [RPCError], which is exactly the arm the deletion routes into, so
      even [Store_fault_then_ack] - the resolution the retry rescues on the
      pristine model - becomes a charge against the budget. There is no second
      producer of the class: [WorkerResponse::into_error_ref]
      (message.rs:125-155) is the only worker-side classifier, called from
      network/mod.rs:496 and :602.
    - {!Batch_quorum_tally_model.Truncated_fanout} truncates the broadcast set
      at quorum_waiter.rs:136-137 to [threshold - 1] = 2 peers. The one real
      sibling repairs POSSESSION and not ack eligibility: after quorum the
      author gossips the digest (worker.rs:316-320) and a peer missing the batch
      prefetches it (network/handler.rs:167-192). The model grants that repair
      unconditionally, and the [sibling-repair] group below asserts it is
      REACHABLE under this mutation - so S3 is refuted in a model that HAS the
      repair, not in one that omits it. Only an inbound [ReportBatch] produces
      the ack the waiter counts (handle.rs:169-190, single caller
      quorum_waiter.rs:92), so possession never becomes eligibility.

    Verified attribution, checked conjunct by conjunct while authoring:
    [No_author_self_credit] breaks S1's (A) two-rejecters and (B) known-honest
    conjuncts and NOTHING else; [No_recoverable_class] breaks all three
    conjuncts of S2 (and, as a side effect, S1 - reclassified stalls reach the
    [QuorumRejected] verdict with an empty rejecters set, which is the same
    defect seen from S1's side); [Truncated_fanout] breaks S3's (A) fan-out
    conjunct (and, as a side effect, S1 - a 2-peer broadcast leaves the budget
    at (2 + 1) - 3 = 0). The two side effects are asserted as pins rather than
    hidden, and S2 and S3 are asserted as survivors wherever they survive. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Batch_quorum_tally_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Batch_quorum_tally_model.Checker.make
       (Batch_quorum_tally_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Batch_quorum_tally_statements.name name))
    Batch_quorum_tally_statements.all

(** Does the named statement prove under this mutation? *)
let proves_under mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false)
               (Batch_quorum_tally_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " flips to refuted under the mutation")
        false proved)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  proves_under Batch_quorum_tally_model.Pristine name (fun proved ->
      Alcotest.(check bool) (name ^ " proves on the pristine model") true proved)

(** A statement the mutation must NOT break: clean attribution means the rest of
    the family still proves under it. *)
let survives_under mut name () =
  proves_under mut name (fun proved ->
      Alcotest.(check bool)
        (name ^ " still proves under the mutation")
        true proved)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** A survivor case: the mutation leaves this statement proved. *)
let survivor mut name =
  [ Alcotest.test_case (name ^ ":survives") `Quick (survives_under mut name) ]

(** The disclosed sibling of {!Truncated_fanout} is REACHABLE under it: the
    batch reaches quorum while one committee peer was never offered it, and the
    post-quorum gossip plus prefetch hands that peer the batch anyway. S3 is
    therefore refuted in a model that carries the repair, and the repair
    provably confers possession without conferring ack eligibility. *)
let gossip_repair_is_live_under_truncation () =
  with_mut Batch_quorum_tally_model.Truncated_fanout (fun sys ->
      Alcotest.(check (pair bool bool))
        "under truncation the unoffered peer still ends up holding the batch, \
         and the fan-out still never completes"
        (true, false)
        ( Batch_quorum_tally_model.Checker.satisfiable sys
            (Formula.Atom
               Batch_quorum_tally_model.Gossip_holder_without_ack_eligibility),
          Batch_quorum_tally_model.Checker.satisfiable sys
            (Formula.Atom Batch_quorum_tally_model.Whole_committee_offered) ))

(** S1's name. *)
let s1_name = "quorum-rejection-needs-two-committee-rejecters-one-known-honest"

(** S2's name. *)
let s2_name = "transient-store-fault-never-charges-the-rejection-budget"

(** S3's name. *)
let s3_name = "every-committee-peer-is-offered-the-batch-at-equal-weight"

let () =
  Alcotest.run "batch_quorum_tally_mutation"
    [
      ( "author-self-credit-in-the-budget (quorum_waiter.rs:168-170)",
        pin Batch_quorum_tally_model.No_author_self_credit s1_name
        @ survivor Batch_quorum_tally_model.No_author_self_credit s2_name
        @ survivor Batch_quorum_tally_model.No_author_self_credit s3_name );
      ( "recoverable-error-classification (network/message.rs:135-137)",
        pin Batch_quorum_tally_model.No_recoverable_class s2_name
        @ pin Batch_quorum_tally_model.No_recoverable_class s1_name
        @ survivor Batch_quorum_tally_model.No_recoverable_class s3_name );
      ( "whole-committee-fan-out (quorum_waiter.rs:136-137)",
        pin Batch_quorum_tally_model.Truncated_fanout s3_name
        @ pin Batch_quorum_tally_model.Truncated_fanout s1_name
        @ survivor Batch_quorum_tally_model.Truncated_fanout s2_name );
      ( "sibling-repair (worker.rs:316-320, network/handler.rs:167-192)",
        [
          Alcotest.test_case "gossip-repair-is-live-under-truncation" `Quick
            gossip_repair_is_live_under_truncation;
        ] );
    ]
