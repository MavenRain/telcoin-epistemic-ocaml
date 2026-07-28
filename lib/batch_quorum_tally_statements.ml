(** Statements of the BATCH_QUORUM_TALLY family: what one seal attempt's stake
    arithmetic guarantees, and what the author can and cannot infer from it.

    READING GUIDE FOR THE K OPERANDS. There is exactly one positive [K] in the
    family, S1 conjunct (B): [K_V0(exists honest w in rejecters(b))]. Its
    operand is not a projection of V0's own view - V0's view carries the COUNT
    of permanent-error replies but never the honest/Byzantine split of them
    (crates/consensus/worker/src/quorum_waiter.rs:212-215 adds stake, not
    identity or motive) - and it is not rigid: at every reachable state with at
    most one rejecter, and at every state before the first rejection, the
    operand is false. What makes it known at a [QuorumRejected] state is a
    counting argument the author can run on the numbers it does hold: the
    budget is [(available_stake + total_stake) - threshold] = 1 (:170), so the
    verdict needs two rejecters (:236-240), and f = 1 leaves at most one of them
    corrupt. The class at that state is not a singleton - it contains both the
    two-honest-rejecters world and the one-honest-one-Byzantine world, which is
    exactly what conjunct (C) asserts and what
    test/t_batch_quorum_tally.ml's [operative-class-is-not-a-singleton] case
    proves.

    The two negative [K]s - S1 (C) and S2 (C) - each have a concrete reachable
    witness pair sharing V0's view and disagreeing on the operand; both pairs
    get a [satisfiable] test.

    Statements are about the verdict of ONE attempt. The batch builder treats
    [QuorumRejected] and [AntiQuorum] identically
    (crates/batch-builder/src/lib.rs:194-211), so nothing here claims anything
    about transaction loss. *)

open Batch_quorum_tally_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** The batch author, and the family's only knowledge agent. *)
let author = Validator.V0

(** S1 - quorum-rejection-needs-two-committee-rejecters-one-known-honest
    [security].

    (A) [AG( verdict(b) = QuorumRejected -> |rejecters(b)| >= 2 )]. The author's
    rejection budget is everything available MINUS the quorum threshold, and it
    credits the author's own vote: [let max_rejected_stake = (available_stake +
    total_stake) - threshold] at quorum_waiter.rs:168-170 with [total_stake =
    inner.authority.voting_power()] at :167 (= 1, committee.rs:170-172). With
    four equal-power validators (committee.rs:25, :507-509) and threshold 3
    (committee.rs:243 and :247-252, [2 * total_votes / 3 + 1]) that
    budget is exactly (3 + 1) - 3 = 1, so the decisive test [if rejected_stake >
    max_rejected_stake] at :236-240 cannot fire on one rejection. Only an
    explicit permanent rejection raises [rejected_stake] (:212-215); a network
    outcome merely lowers availability (:216-218).

    (B) [AG( verdict(b) = QuorumRejected -> K_author(exists honest w in
    rejecters(b)) )]. Two rejecters and f = 1 leave at least one honest, and
    every world sharing the author's view at such a state has two rejecters, so
    the author knows it - by counting, never by seeing.

    (C) [AG( verdict(b) = QuorumRejected -> ~K_author(exists byzantine w in
    rejecters(b) is false) )]. The price of (B): the author cannot tell whether
    the rejection was two honest refusals or one honest and one malicious, so it
    can never name the corrupt identity. Witness pair, both reachable and
    sharing V0's view: two [Reject_honest] resolutions, versus one
    [Reject_honest] and one [Reject_byzantine].

    MUTATION PIN. {!No_author_self_credit} deletes the [+ total_stake] of
    quorum_waiter.rs:170, dropping the budget to 0 and adding the transition
    [first permanent rejection -> Rejected_by_quorum]. (A) then fails at that
    one-rejecter state, and so does (B): the view class there contains the
    all-honest world and the single-Byzantine world, and the operand is false in
    the second. No sibling re-imposes two rejections - the availability exit at
    :241-243 is untripped by one rejection (1 + 2 >= 3), the exhausted-peer exit
    at :220-223 needs every task resolved, and the quorum test at :190 pre-empts
    only under a schedule that puts two acks first. *)
let s_1 =
  let two_rejecters =
    Formula.Ag
      (Formula.Implies (atom Permanently_rejected, atom Two_rejecting_peers))
  in
  let knows_one_is_honest =
    Formula.Ag
      (Formula.Implies
         ( atom Permanently_rejected,
           Formula.K (author, atom Honest_rejecter) ))
  in
  let cannot_name_the_corrupt =
    Formula.Ag
      (Formula.Implies
         ( atom Permanently_rejected,
           Formula.Not
             (Formula.K (author, Formula.Not (atom Byzantine_rejecter))) ))
  in
  {
    name = "quorum-rejection-needs-two-committee-rejecters-one-known-honest";
    bucket = Statements.Security;
    formula =
      Formula.conj
        [ two_rejecters; knows_one_is_honest; cannot_name_the_corrupt ];
    antecedent = atom Permanently_rejected;
  }

(** S2 - transient-store-fault-never-charges-the-rejection-budget [liveness].

    (A) [AG( rejected_stake = |rejecters(b)| )], written as [AG( ~(rejected_stake
    > |rejecters(b)|) )]. Only an explicit permanent rejection is ever charged
    to the rejection budget. A responder whose batch-store write fails
    (network/handler.rs:252-254) answers [RecoverableError] by
    message.rs:128-137, the requester turns that into
    [NetworkError::RPCRetryable] (handle.rs:186-188), and the waiter's retry arm
    (quorum_waiter.rs:101-113) takes it - so it can only ever reach the loop as
    [WaiterError::Network], which touches availability alone (:216-218).

    (B) [AG( rejecters(b) = {} -> verdict(b) != QuorumRejected )]. The
    consequence that matters: an honest node's disk hiccup, however many nodes
    hiccup, cannot drive the attempt to the permanent verdict. Only a deliberate
    permanent refusal can.

    (C) [AG( |unavailable(b)| = 1 -> ~K_author(store_write_failed(b)) )]. The
    price: [Self::waiter] collapses every non-[RPCError] outcome into
    [WaiterError::Network] (:101-115), so a peer whose store genuinely failed
    three times and a corrupt peer fabricating the same recoverable reply are
    the same value at :216. Witness pair, both reachable and sharing V0's view:
    one [Stall_store_fault], versus one [Stall_byzantine].

    MUTATION PIN. {!No_recoverable_class} deletes the [RecoverableError] arm at
    message.rs:135-137, so a transient responder-side condition arrives as
    [NetworkError::RPCError] (handle.rs:185) and hits the no-retry rejection arm
    at :94-100. (A) fails at the first store fault, and (B) fails at two of them
    - [rejected_stake = 2 > max_rejected_stake = 1] gives [QuorumRejected] with
    an empty rejecters set. The retry loop is the obvious sibling and it does
    NOT repair the deletion: :101-113 retries every error EXCEPT [RPCError],
    which is the arm the deletion routes into, so even the resolution the retry
    rescues in the pristine model ([Store_fault_then_ack]) becomes a charge.
    [WorkerResponse::into_error_ref] (message.rs:125-155) is the only worker-side
    producer of the class, called at network/mod.rs:496 and :602. *)
let s_2 =
  let only_rejections_are_charged =
    Formula.Ag (Formula.Not (atom Non_rejection_charged))
  in
  let no_rejection_no_permanent_verdict =
    Formula.Ag
      (Formula.Implies
         (atom No_peer_rejected, Formula.Not (atom Permanently_rejected)))
  in
  let cannot_tell_fault_from_fabrication =
    Formula.Ag
      (Formula.Implies
         ( atom One_unavailable_peer,
           Formula.Not (Formula.K (author, atom Store_write_failed)) ))
  in
  {
    name = "transient-store-fault-never-charges-the-rejection-budget";
    bucket = Statements.Liveness;
    formula =
      Formula.conj
        [
          only_rejections_are_charged;
          no_rejection_no_permanent_verdict;
          cannot_tell_fault_from_fabrication;
        ];
    antecedent = atom Store_write_failed;
  }

(** S3 - every-committee-peer-is-offered-the-batch-at-equal-weight [fairness].

    (A) [AF( offered(b) = committee \ {author} )]. The author broadcasts to
    EVERY other committee member, not to just enough of them to make a quorum:
    quorum_waiter.rs:136-137 takes [others_keys_except] (committee.rs:561-573,
    every authority whose protocol key differs from the author) and :148-161
    spawns one task per element. The inevitability is honest rather than
    assumed: there is no [.await] between :148 and :161, so the enclosing
    [tokio::time::timeout] (:133) cannot interrupt the fan-out part way.

    (B) [AG( verdict(b) = Ok -> |ackers(b)| >= 2 )]. Every member's ack is worth
    the same single unit ([EQUAL_VOTING_POWER = 1], committee.rs:25, returned for
    any member at :507-509) and the author's own credit is one
    (quorum_waiter.rs:167, committee.rs:170-172), so
    reaching threshold 3 takes two distinct peer acks. No member's ack counts
    double and the author cannot self-certify.

    MUTATION PIN. {!Truncated_fanout} truncates the broadcast set to
    [threshold - 1] = 2 peers; because [others_keys_except] walks a keyed map in
    a deterministic order the same identity is dropped on every attempt, so (A)
    fails permanently. The one real sibling repairs POSSESSION and not ack
    eligibility, and the model grants it unconditionally as
    {!Gossip_holder_without_ack_eligibility}: after quorum the author gossips
    the digest (worker.rs:316-320) and a peer missing the batch prefetches it
    (network/handler.rs:167-192), so the excluded peer ends up HOLDING the
    batch - but only an inbound [ReportBatch] yields the
    [WorkerResponse::ReportBatch] the waiter counts (handle.rs:169-190, single
    caller quorum_waiter.rs:92), and no peer can volunteer one, so the excluded
    identity still cannot contribute stake.
    test/t_batch_quorum_tally_mutation.ml asserts that repaired-possession state
    is reachable under the mutation, so (A) is refuted in a model that HAS the
    repair rather than in one that omits it. *)
let s_3 =
  let whole_committee_reached = Formula.Af (atom Whole_committee_offered) in
  let quorum_needs_two_peers =
    Formula.Ag (Formula.Implies (atom Quorum_reached, atom Two_peer_acks))
  in
  {
    name = "every-committee-peer-is-offered-the-batch-at-equal-weight";
    bucket = Statements.Fairness;
    formula = Formula.And (whole_committee_reached, quorum_needs_two_peers);
    antecedent = atom Quorum_reached;
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st = Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure degrades
    every row to [proved = false] rather than raising. *)
let reports () =
  let row proved st = { Report.name = st.name; bucket = st.bucket; proved } in
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, r) ->
          row (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) r) st)
        (prove_all sys))
    ~error:(fun Checker.Empty_init -> List.map (row false) all)
    (make ())
