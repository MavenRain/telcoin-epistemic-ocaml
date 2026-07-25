(** The seven temporal-epistemic statements about telcoin-network, encoded
    over the {!Tn_model} interpreted system. Each statement was mined from
    the telcoin-network sources, adversarially verified against the code
    (grounding) and against the finite-model semantics (encodability), and
    is stated here in the refined form that survived both skeptics. File
    citations refer to Telcoin-Association/telcoin-network.

    Reading guide: K_i is grounded in the validator's local state (dag,
    batches, votes, committed set) - [Tn_model.Checker] evaluates it by
    indistinguishability of local views over all reachable global states.
    Facts that the protocol makes inevitable are knowable by inference
    (FHMV implicit knowledge), so the epistemically STRICT content lives in
    the statements over contingent hidden facts: the Byzantine branch
    (S3), other validators' possession during the delay window (S5), and
    the availability quorum behind a certificate (S1, S7). *)

open Tn_state
open Tn_model

type bucket = Safety | Liveness | Fairness | Security

let bucket_to_string = function
  | Safety -> "safety"
  | Liveness -> "liveness"
  | Fairness -> "fairness"
  | Security -> "security"

type statement = {
  name : string;
  bucket : bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent *)
}

let atom a = Formula.Atom a

let d_r0 v = { author = v; round = R0; variant = A }

let d_r2 v = { author = v; round = R2; variant = A }

let byz_r0 = d_r0 Validator.V3

(* S1 - stored-cert-implies-known-quorum-and-slot-uniqueness [security].
   A certificate in an honest validator's DAG carries knowledge that 2f+1
   votes for exactly that digest exist (BLS aggregate verification:
   certificate.rs:225-251, is_verified gate cert_manager.rs:88-93), and no
   two certificates ever occupy one (author, round) slot (equivocation
   rejection state.rs:145-157; at f = 1 quorum intersection makes a
   conflicting pair unreachable - the detect-and-halt branch needs two
   Byzantine validators and is out of this model's scope). *)
let s1 =
  let key = [ d_r0 Validator.V1; byz_r0; anchor; d_r2 Validator.V2 ] in
  let known_quorum =
    Formula.conj
      (List.concat_map
         (fun i ->
           List.map
             (fun d ->
               Formula.Implies
                 (atom (In_dag (i, d)), Formula.K (i, atom (Quorum_voted d))))
             key)
         honest)
  in
  {
    name = "stored-cert-implies-known-quorum-and-slot-uniqueness";
    bucket = Security;
    formula =
      Formula.And
        (Formula.Ag known_quorum, Formula.Ag (Formula.Not (atom Conflicting_certs)));
    antecedent = atom (In_dag (Validator.V1, byz_r0));
  }

(* S2 - vote-attests-known-parents-and-payload [security].
   An honest first signature on a peer's header attests that the voter
   holds the referenced batch payload (worker availability gate,
   handler.rs:231-263, sync_header_batches header_validator.rs:98-154) and
   knows every parent is a formed certificate (vote_inner parent checks,
   handler.rs:693-738). *)
let s2 =
  let pairs =
    [
      (Validator.V0, { author = Validator.V1; round = R1; variant = A });
      (Validator.V1, anchor);
      (Validator.V1, d_r2 Validator.V2);
      (Validator.V0, byz_r0);
    ]
  in
  let gated =
    Formula.conj
      (List.map
         (fun (i, d) ->
           Formula.Implies
             ( atom (Voted (i, d)),
               Formula.And
                 ( atom (Holds_batch (i, slot_of d)),
                   Formula.K (i, atom (Parents_certified d)) ) ))
         pairs)
  in
  {
    name = "vote-attests-known-parents-and-payload";
    bucket = Security;
    formula = Formula.Ag gated;
    antecedent = atom (Voted (Validator.V0, byz_r0));
  }

(* S3 - no-conflicting-revote-and-equivocation-detectability [safety].
   The vote-once discipline (read_vote_info digest compare + AlreadyVoted,
   handler.rs:787-847): no honest validator ever signs two variants of one
   slot. Its epistemic face: equivocation is knowable exactly through local
   conflicting evidence - the victim that holds a vote of its own plus a
   conflicting certificate KNOWS the hidden Byzantine branch is
   equivocation, while a validator with no such evidence CANNOT know it
   (its local view is consistent with a cooperative run). *)
let s3 =
  let detect =
    Formula.conj
      (List.map
         (fun i ->
           Formula.Implies
             (atom (Equivocation_evidence i), Formula.K (i, atom Byz_equivocating)))
         honest)
  in
  let opaque =
    Formula.conj
      (List.map
         (fun i ->
           Formula.Implies
             ( Formula.And
                 (atom Byz_equivocating, Formula.Not (atom (Equivocation_evidence i))),
               Formula.Not (Formula.K (i, atom Byz_equivocating)) ))
         [ Validator.V0; Validator.V1 ])
  in
  {
    name = "no-conflicting-revote-and-equivocation-detectability";
    bucket = Safety;
    formula =
      Formula.And
        (Formula.Ag (Formula.Not (atom Honest_double_vote)),
         Formula.And (Formula.Ag detect, Formula.Ag opaque));
    antecedent = atom (Equivocation_evidence Validator.V2);
  }

(* S4 - commit-implies-known-support-quorum [safety].
   A validator directly commits the anchor only off its OWN stored f+1
   supporting R2 certificates (bullshark.rs:192-206, validity_threshold
   committee.rs:254-259), and thereby knows a support quorum exists
   globally - the certificates in its store are unforgeable evidence of
   remote production. *)
let s4 =
  let committed_knows =
    Formula.conj
      (List.map
         (fun i ->
           Formula.Implies
             ( atom (Committed (i, anchor)),
               Formula.And
                 (atom (Own_support_ge i), Formula.K (i, atom Support_quorum)) ))
         honest)
  in
  {
    name = "commit-implies-known-support-quorum";
    bucket = Safety;
    formula = Formula.Ag committed_knows;
    antecedent = atom (Committed (Validator.V1, anchor));
  }

(* S5 - rounds-advance-under-known-distinct-quorum [liveness].
   Under bounded-delay fairness (baked into the model's Deliver phases):
   a validator proposes its next-round header only knowing a distinct-slot
   certificate quorum for the previous round (enough_parents gate,
   proposer.rs:546-553, authorities_seen dedup certificates.rs:82-99);
   once the anchor certificate forms, every honest validator eventually
   KNOWS every honest validator holds it (delivery + synchronizer fetch,
   state-sync - false during the delay window, restored by the forced
   delivery); and the protocol always progresses to completion. *)
let s5 =
  let propose_gate =
    Formula.conj
      (List.map
         (fun i ->
           Formula.Implies
             ( atom (Header_proposed (i, R1)),
               Formula.K (i, atom (Quorum_certs R0)) ))
         honest)
  in
  let all_hold = Formula.conj (List.map (fun j -> atom (In_dag (j, anchor))) honest) in
  let propagation =
    Formula.leads_to (atom (Cert_formed anchor)) (Formula.Everyone (honest, all_hold))
  in
  {
    name = "rounds-advance-under-known-distinct-quorum";
    bucket = Liveness;
    formula =
      Formula.And
        (Formula.Ag propose_gate,
         Formula.And (propagation, Formula.Af (atom At_done)));
    antecedent = atom (Cert_formed anchor);
  }

(* S6 - round-robin-leader-common-knowledge-and-slot-fairness [fairness].
   The anchor slot is a deterministic function of the shared committee
   config (next_leader round-robin, leader_schedule.rs:285-304, stable
   BTreeMap order), so it is common knowledge among honest validators by
   shared-config admissibility - every reachable world agrees on it, and
   the perturbed-committee mutation is what would break it. Inclusion
   fairness: once the anchor and an honest R0 certificate exist, that
   certificate is inevitably in every honest validator's committed sub-DAG
   (order_dag causal closure - no honest certificate is censored). *)
let s6 =
  let schedule_ck = Formula.Ag (Formula.Common (honest, atom Anchor_author_agreed)) in
  let inclusion =
    Formula.conj
      (List.concat_map
         (fun v ->
           List.map
             (fun i ->
               Formula.Ag
                 (Formula.Implies
                    ( Formula.And
                        (atom (Cert_formed anchor), atom (Cert_formed (d_r0 v))),
                      Formula.Af (atom (Committed (i, d_r0 v))) )))
             honest)
         honest)
  in
  {
    name = "round-robin-leader-common-knowledge-and-slot-fairness";
    bucket = Fairness;
    formula = Formula.And (schedule_ck, inclusion);
    antecedent =
      Formula.And (atom (Cert_formed anchor), atom (Cert_formed (d_r0 Validator.V2)));
  }

(* S7 - quorum-ack-implies-honest-batch-availability [security].
   A certificate can only form when its batch reached an honest availability
   quorum: honest workers ack (here: vote) only after validating and
   storing the batch (handler.rs:231-263, validator.rs:39-81,
   quorum_waiter.rs:163-190), so 2f+1 votes minus at most f Byzantine
   leaves f+1 honest holders - and any honest validator holding the
   certificate knows it. The starved-batch branch is the contrapositive
   witness: no honest quorum, no certificate. *)
let s7 =
  let availability d =
    Formula.Ag
      (Formula.Implies
         (atom (Cert_formed d), atom (Honest_holders_ge (slot_of d))))
  in
  let known =
    Formula.conj
      (List.map
         (fun i ->
           Formula.Implies
             ( atom (In_dag (i, byz_r0)),
               Formula.K (i, atom (Honest_holders_ge (slot_of byz_r0))) ))
         honest)
  in
  {
    name = "quorum-ack-implies-honest-batch-availability";
    bucket = Security;
    formula =
      Formula.And
        (availability (d_r0 Validator.V1),
         Formula.And (availability byz_r0, Formula.Ag known));
    antecedent = atom (Cert_formed byz_r0);
  }

let all = [ s1; s2; s3; s4; s5; s6; s7 ]

let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

let prove_all sys = List.map (fun st -> (st, prove sys st)) all
