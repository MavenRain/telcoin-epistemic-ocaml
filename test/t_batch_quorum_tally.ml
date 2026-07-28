(** Proof suite for the BATCH_QUORUM_TALLY family: the three statements prove on
    the pristine {!Batch_quorum_tally_model}, the model is as small as claimed,
    the states the stake arithmetic forbids really are unreachable, and - the
    point of the [contingency] group - the family's single positive [K] is
    neither collapsed nor propped up by a singleton view class.

    The [sanity] group pins the exact reachable count and the three states the
    pristine gates forbid, plus one negative: the modelled sibling repair of
    {!Batch_quorum_tally_model.Truncated_fanout} is IDLE on the pristine model,
    so it cannot be quietly doing the work of a gate here.

    The [contingency] group discharges R2 and R3. R2: [K_V0(honest rejecter)] is
    contingent (there are reachable states where the author does not know it),
    and the class at the operative state provably straddles the corruption
    split - at a [QuorumRejected] state with no Byzantine rejecter the author
    still cannot rule one out, which is only possible if a SECOND reachable
    world shares its view. R3: both negative [K]s get a reachable witness pair
    in both directions. *)

open Telcoin_epistemic
open Batch_quorum_tally_model

(** Build the pristine system or fail the test on an impossible [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

(** Render a proof error for the assertion message. *)
let error_to_string = function
  | Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Batch_quorum_tally_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Batch_quorum_tally_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Batch_quorum_tally_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The author, this family's only knowledge agent. *)
let author = Validator.V0

(** The pristine reachable set, counted: 3 states of the fan-out chain
    ([offered] = 0, 1, 2), 1 all-pending state, 6 one-resolution states, 18
    two-resolution states (the 21 multisets of size two over the six causes,
    less the 3 that would need two Byzantine acts), and 26 three-resolution
    states - reachable only through an UNDECIDED two-resolution state, which is
    exactly one ack plus one non-ack, giving 2 * 7 with one ack and 3 * 4 with
    two. 3 + 1 + 6 + 18 + 26 = 54. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check int) "reachable states" 54 (Checker.reachable_count sys))

(** The gate of S1 conjunct (A): the rejection budget of quorum_waiter.rs:170 is
    exactly 1, so no reachable state carries a [QuorumRejected] verdict with
    fewer than two permanent rejections. *)
let one_rejection_is_never_decisive () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "verdict = QuorumRejected /\\ |rejecters| < 2 is unreachable" false
        (Checker.satisfiable sys
           (Formula.And
              (f Permanently_rejected, Formula.Not (f Two_rejecting_peers)))))

(** The gate of S2 conjunct (A): only [WaiterError::Rejected] raises
    [rejected_stake] (quorum_waiter.rs:212-215), so the budget is never charged
    for anything but an explicit permanent rejection. *)
let only_a_rejection_is_ever_charged () =
  with_sys (fun sys ->
      Alcotest.(check bool) "rejected_stake > |rejecters| is unreachable" false
        (Checker.satisfiable sys (f Non_rejection_charged)))

(** The gate of S3 conjunct (B): the author's own credit is one unit
    (quorum_waiter.rs:167, committee.rs:25), so quorum is unreachable without
    two peer acks - the author cannot self-certify a batch. *)
let author_alone_is_no_quorum () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "verdict = Ok /\\ |ackers| < 2 is unreachable" false
        (Checker.satisfiable sys
           (Formula.And (f Quorum_reached, Formula.Not (f Two_peer_acks)))))

(** The modelled sibling repair - post-quorum gossip (worker.rs:316-320) plus
    prefetch (network/handler.rs:167-192) handing the batch to a peer that was
    never offered it - is IDLE on the pristine model, because the pristine
    fan-out leaves no peer unoffered. It becomes reachable only under
    {!Truncated_fanout}, where t_batch_quorum_tally_mutation.ml asserts it. *)
let gossip_repair_is_idle_when_the_fanout_is_whole () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "gossip_holder_not_offered is unreachable on the pristine model" false
        (Checker.satisfiable sys (f Gossip_holder_without_ack_eligibility)))

(** R2, part one - S1's positive [K] is CONTINGENT, not collapsed: at every
    state before a rejection has landed the author does not know that an honest
    committee member rejected its batch. *)
let honest_rejecter_knowledge_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "~K_V0(exists honest rejecter) is satisfiable" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (author, f Honest_rejecter)))))

(** R2, part two - the operative view class is NOT a singleton. Take
    q = [exists byzantine w in rejecters], which is FALSE at the
    two-honest-rejecters state; [~K_V0(~q)] there can only hold if some OTHER
    reachable state shares V0's view and satisfies q, namely the
    one-honest-one-Byzantine state. A singleton class would make this false,
    which is exactly the point of the test. *)
let operative_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "QuorumRejected /\\ ~byzantine_rejecter /\\ ~K_V0(~byzantine_rejecter) \
         is satisfiable"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And
                  (f Permanently_rejected, Formula.Not (f Byzantine_rejecter)),
                Formula.Not
                  (Formula.K (author, Formula.Not (f Byzantine_rejecter))) ))))

(** R3, the other half of S1's ignorance conjunct: at a state where a Byzantine
    peer really is among the rejecters the author cannot know that either, so
    the class straddles both truth values of the corruption atom. *)
let rejecter_ignorance_is_two_sided () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "QuorumRejected /\\ byzantine_rejecter /\\ ~K_V0(byzantine_rejecter) is \
         satisfiable"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( Formula.And (f Permanently_rejected, f Byzantine_rejecter),
                Formula.Not (Formula.K (author, f Byzantine_rejecter)) ))))

(** The concrete disagreeing pair behind S1's ignorance: a [QuorumRejected]
    verdict in which both rejecters refused honestly, and one in which the
    corrupt identity was one of them. Both are reachable, so the ignorance rests
    on real states rather than on a quirk of the encoding. *)
let rejecter_witness_pair_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check (pair bool bool))
        "both (QuorumRejected /\\ byzantine_rejecter) and its negation are \
         reachable"
        (true, true)
        ( Checker.satisfiable sys
            (Formula.And (f Permanently_rejected, f Byzantine_rejecter)),
          Checker.satisfiable sys
            (Formula.And
               (f Permanently_rejected, Formula.Not (f Byzantine_rejecter))) ))

(** R3 for S2's ignorance conjunct, both directions: with one peer unavailable
    the author can neither conclude that a store write failed nor that none
    did - [Self::waiter] handed it the same [WaiterError::Network] either way
    (quorum_waiter.rs:101-115). *)
let store_fault_ignorance_is_two_sided () =
  with_sys (fun sys ->
      Alcotest.(check (pair bool bool))
        "one unavailable peer: neither K_V0(store_write_failed) nor \
         K_V0(~store_write_failed)"
        (true, true)
        ( Checker.satisfiable sys
            (Formula.And
               ( Formula.And (f One_unavailable_peer, f Store_write_failed),
                 Formula.Not (Formula.K (author, f Store_write_failed)) )),
          Checker.satisfiable sys
            (Formula.And
               ( Formula.And
                   ( f One_unavailable_peer,
                     Formula.Not (f Store_write_failed) ),
                 Formula.Not
                   (Formula.K (author, Formula.Not (f Store_write_failed))) ))
        ))

(** The concrete disagreeing pair behind S2's ignorance: one honest peer whose
    [store.insert::<NodeBatchesCache>] kept failing (handler.rs:252-254), and
    one corrupt peer fabricating the same recoverable reply while its store was
    never touched. Both are reachable. *)
let store_fault_witness_pair_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check (pair bool bool))
        "both (one unavailable /\\ store_write_failed) and its negation are \
         reachable"
        (true, true)
        ( Checker.satisfiable sys
            (Formula.And (f One_unavailable_peer, f Store_write_failed)),
          Checker.satisfiable sys
            (Formula.And
               (f One_unavailable_peer, Formula.Not (f Store_write_failed))) ))

let () =
  Alcotest.run "batch_quorum_tally"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Batch_quorum_tally_statements.name `Quick
              (prove_one st))
          Batch_quorum_tally_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "one-rejection-is-never-decisive" `Quick
            one_rejection_is_never_decisive;
          Alcotest.test_case "only-a-rejection-is-ever-charged" `Quick
            only_a_rejection_is_ever_charged;
          Alcotest.test_case "author-alone-is-no-quorum" `Quick
            author_alone_is_no_quorum;
          Alcotest.test_case "gossip-repair-is-idle-when-the-fanout-is-whole"
            `Quick gossip_repair_is_idle_when_the_fanout_is_whole;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "honest-rejecter-knowledge-is-contingent" `Quick
            honest_rejecter_knowledge_is_contingent;
          Alcotest.test_case "operative-class-is-not-a-singleton" `Quick
            operative_class_is_not_a_singleton;
          Alcotest.test_case "rejecter-ignorance-is-two-sided" `Quick
            rejecter_ignorance_is_two_sided;
          Alcotest.test_case "rejecter-witness-pair-is-reachable" `Quick
            rejecter_witness_pair_is_reachable;
          Alcotest.test_case "store-fault-ignorance-is-two-sided" `Quick
            store_fault_ignorance_is_two_sided;
          Alcotest.test_case "store-fault-witness-pair-is-reachable" `Quick
            store_fault_witness_pair_is_reachable;
        ] );
    ]
