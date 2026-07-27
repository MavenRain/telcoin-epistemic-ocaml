(** The re-vote discipline for one equivocating slot, abstracted from
    telcoin-network's vote handler (DESIGN family CONSENSUS-EXT #11,
    revote-only-under-global-cert-ignorance).

    The modeled mechanism: when a header author submits a SECOND, conflicting
    header for an (author, round) slot an honest validator already voted on,
    the validator re-votes only after checking its OWN certificate store for
    a certificate on that slot - the local cert-evidence guard, the
    conflicting-digest branch of [vote_inner]
    (crates/consensus/primary/src/network/handler.rs:807-847, the
    [cert_exists] check at handler.rs:824-839, reading
    crates/storage/src/stores/certificate_store.rs:219-228 by (author,
    round)). A certificate in the store means the old vote contributed to a
    real aggregate, so a second signature would be equivocation
    ([AlreadyVoted]); an empty store permits the re-vote.

    Restart-premise collapse: in telcoin-network the in-memory
    [auth_last_vote] cache (handler.rs:510-596, [AuthEquivocationMap]
    handler.rs:55-58) rejects a conflicting same-round request BEFORE the
    cert check runs; the cert-evidence branch is reached only after the
    voter restarts and the durable [VoteInfo]
    (crates/storage/src/stores/vote_digest_store.rs:15-30, consulted at
    handler.rs:772-786) survives to expose the digest conflict. The model
    collapses that premise: its Revote step IS the post-restart
    conflicting-digest path, so the cert-evidence guard is the SOLE live
    gate on the re-vote - which is exactly why deleting it (the mutation)
    is not silently repaired by any sibling path.

    The run: V3 equivocates on slot (V3, R0). Phase [Vote]: the honest
    quorum signs V3's first header h1. Phase [Certify]: a hidden Byzantine
    3-way sub-choice resolves - [Skip_aggregate] (V3 never aggregates the
    votes; no certificate exists), [Aggregate_withhold] (V3 assembles the
    certificate but keeps it in a private slot; it exists, invisibly), or
    [Aggregate_deliver] (V3 assembles and broadcasts it into every dag).
    Phase [Revote]: V3 requests V1's vote on the conflicting h2; V1
    re-votes iff its own dag holds no certificate for the slot, latching a
    monotone [v1_revoted] flag. The skip/withhold branches are
    honest-view-identical (V3's private act is the only difference), which
    is what makes [K (V1, Cert_exists)] contingent rather than collapsed:
    a re-voting V1 cannot rule out that the certificate exists.

    Role mapping of the four kernel validator slots for this family:
    - V1: the honest voter whose re-vote discipline is at issue - the ONLY
      knowledge agent; its view is (votes cast, own-dag certificate
      possession, re-vote latch).
    - V3: the Byzantine author/aggregator of slot (V3, R0); a State-fields
      party only (private certificate slot), constant blank view, never
      under K.
    - V0, V2: the rest of the honest committee, abstracted into the vote
      quorum behind the aggregate branches; constant blank views, never
      under K.

    Certificates are unforgeable by construction: the aggregate branches
    produce the certificate value only from the phase where the honest
    quorum (including V1's recorded h1 vote) has signed. *)

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(* The two conflicting headers V3 issues for slot (V3, R0): h1 first, the
   equivocating h2 at the Revote step. *)

(** The equivocation pair for slot (V3, R0): [H1] is V3's first header (the
    one the honest quorum signs), [H2] the conflicting second header whose
    vote request triggers the re-vote branch (handler.rs:807-847). *)
type header = H1 | H2

(** Total order index for {!header}. *)
let header_index = function H1 -> 0 | H2 -> 1

(** Total order on {!header} via {!header_index}. *)
let header_compare a b = Int.compare (header_index a) (header_index b)

(** Render a {!header} for atom strings. *)
let header_to_string = function H1 -> "h1" | H2 -> "h2"

(** Sets of headers: V1's vote record, keyed the way the durable
    per-author [VoteInfo] exposes the digest conflict
    (vote_digest_store.rs:15-30). *)
module Header_set = Set.Make (struct
  type t = header

  let compare = header_compare
end)

(** Sets of validators: which dags hold the slot's certificate - the
    "union of all dags" side of [Cert_exists]. *)
module Validator_set = Set.Make (Validator)

(** The one certificate value the model can assemble: the aggregate over
    the honest quorum's h1 votes for slot (V3, R0). It exists only where a
    transition constructed it (certificate.rs-style unforgeability by
    construction, read back via certificate_store.rs:219-228). *)
type cert = Cert_v3_r0

(** Total (trivial) order on the one-constructor {!cert}. *)
let cert_compare Cert_v3_r0 Cert_v3_r0 = 0

(** The hidden Byzantine sub-choice at Certify, [Choice_unchosen] in the
    initial state and resolved into ALL THREE branches by the Certify
    transition - after V1's view is already fixed, so honest views collide
    across branches. [Skip_aggregate] manufactures the no-certificate run
    that is honest-view-identical to [Aggregate_withhold]'s
    certificate-exists run: that collision is the entire epistemic content
    of the statement (the card's false witness). [Aggregate_deliver] is the
    branch where the cert-evidence guard actually fires - and the branch
    the mutation needs in order to bite. *)
type choice =
  | Choice_unchosen
  | Skip_aggregate  (** V3 never aggregates: no certificate exists at all *)
  | Aggregate_withhold
      (** V3 assembles the certificate but keeps it private: it exists,
          invisible to every honest dag *)
  | Aggregate_deliver
      (** V3 assembles and broadcasts: the certificate lands in every dag,
          including V1's own *)

(** Total order index for {!choice}. *)
let choice_index = function
  | Choice_unchosen -> 0
  | Skip_aggregate -> 1
  | Aggregate_withhold -> 2
  | Aggregate_deliver -> 3

(** Total order on {!choice} via {!choice_index}. *)
let choice_compare a b = Int.compare (choice_index a) (choice_index b)

(** The phase machine: V1 signs h1, the hidden aggregation sub-choice
    resolves, V3 requests a vote on the conflicting h2 (the collapsed
    post-restart conflicting-digest path, handler.rs:807-847), then the
    terminal stutter. *)
type phase = Vote | Certify | Revote | Done

(** Total order index for {!phase}. *)
let phase_index = function Vote -> 0 | Certify -> 1 | Revote -> 2 | Done -> 3

(** Total order on {!phase} via {!phase_index}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The global state: the phase, the hidden sub-choice, V1's vote record,
    the set of validators whose dag holds the slot's certificate, V3's
    private certificate slot (the withheld aggregate), and V1's latched
    re-vote flag. Everything except [v1_voted], V1's own membership in
    [cert_holders], and [v1_revoted] is invisible to V1. *)
type state = {
  phase : phase;
  choice : choice;
  v1_voted : Header_set.t;
  cert_holders : Validator_set.t;
  v3_private : cert option;
  v1_revoted : bool;
}

(** Total deterministic order over ALL state fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = choice_compare s1.choice s2.choice in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Header_set.compare s1.v1_voted s2.v1_voted in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Validator_set.compare s1.cert_holders s2.cert_holders in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Option.compare cert_compare s1.v3_private s2.v3_private in
          if Bool.not (Int.equal c4 0) then c4
          else Bool.compare s1.v1_revoted s2.v1_revoted

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** V1's local view - the knowledge ground for [K (V1, _)]: the votes it
    has cast (its durable VoteInfo record), whether its OWN dag holds the
    slot's certificate (exactly what the cert-evidence guard at
    handler.rs:824-839 consults), and its re-vote latch. The hidden
    sub-choice, V3's private slot, and other dags are absent: V1 knows
    only what it locally holds. *)
type view_local = {
  w_voted : Header_set.t;
  w_own_cert : bool;
  w_revoted : bool;
}

(** Total deterministic order over ALL view fields. *)
let view_compare v1 v2 =
  let c = Header_set.compare v1.w_voted v2.w_voted in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Bool.compare v1.w_own_cert v2.w_own_cert in
    if Bool.not (Int.equal c1 0) then c1
    else Bool.compare v1.w_revoted v2.w_revoted

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view_local

  let compare = view_compare
end

(** V1's view projection: vote record, own-dag certificate possession,
    re-vote latch. *)
let view_v1 s =
  {
    w_voted = s.v1_voted;
    w_own_cert = Validator_set.mem Validator.V1 s.cert_holders;
    w_revoted = s.v1_revoted;
  }

(** The constant blank view of the non-agent validators (V0, V2, V3): they
    are State-fields parties in this family and never appear under K, so
    their projection carries no information. *)
let view_blank =
  { w_voted = Header_set.empty; w_own_cert = false; w_revoted = false }

(** The total view function: V1 is the sole knowledge agent; V0, V2, V3
    project to the constant blank view. *)
let view v s =
  match v with
  | Validator.V1 -> view_v1 s
  | Validator.V0 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      view_blank

(** The initial state: Vote phase, sub-choice unresolved, nothing voted,
    no certificate anywhere. *)
let initial =
  {
    phase = Vote;
    choice = Choice_unchosen;
    v1_voted = Header_set.empty;
    cert_holders = Validator_set.empty;
    v3_private = None;
    v1_revoted = false;
  }

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_cert_evidence_guard
      (** delete the local cert-evidence guard (handler.rs:824-839): V1
          re-votes on the conflicting h2 WITHOUT checking its own dag for
          the slot's certificate, so in the [Aggregate_deliver] branch it
          re-votes while holding the certificate - there [K (V1,
          Cert_exists)] is true, refuting the AG conjunct *)

(** All four validators as a holder set: the broadcast target of
    [Aggregate_deliver]. *)
let all_holders =
  List.fold_left
    (fun acc v -> Validator_set.add v acc)
    Validator_set.empty roster

(** Vote step: V1 signs V3's first header h1 (the no-previous-vote path of
    [vote_inner], handler.rs:772-786); V0/V2's quorum signatures are
    abstracted into the phase. *)
let vote_step s =
  [ { s with phase = Certify; v1_voted = Header_set.add H1 s.v1_voted } ]

(** Certify step: the hidden sub-choice resolves into ALL THREE branches.
    The certificate value is assembled only if the honest quorum signed h1
    (unforgeability by construction); [Aggregate_withhold] parks it in
    V3's private slot, [Aggregate_deliver] additionally broadcasts it into
    every dag, [Skip_aggregate] never assembles it. *)
let certify_step s =
  let aggregated =
    if Header_set.mem H1 s.v1_voted then Some Cert_v3_r0 else None
  in
  [
    { s with phase = Revote; choice = Skip_aggregate };
    { s with phase = Revote; choice = Aggregate_withhold; v3_private = aggregated };
    {
      s with
      phase = Revote;
      choice = Aggregate_deliver;
      v3_private = aggregated;
      cert_holders =
        Option.fold ~none:s.cert_holders
          ~some:(fun Cert_v3_r0 -> all_holders)
          aggregated;
    };
  ]

(** The cert-evidence guard: pristine, V1 re-votes only when its OWN dag
    holds no certificate for slot (V3, R0) - the [cert_exists] check at
    handler.rs:824-839 over certificate_store.rs:219-228. The mutation
    deletes the check, and no sibling gate remains: the model's Revote
    step is already the post-restart path past the [auth_last_vote] cache
    (handler.rs:510-596), so this guard is the sole gate on the re-vote. *)
let revote_gate mut s =
  match mut with
  | Pristine -> Bool.not (Validator_set.mem Validator.V1 s.cert_holders)
  | No_cert_evidence_guard -> true

(** Revote step: V3 requests V1's vote on the conflicting h2. If the
    cert-evidence guard passes, V1 signs h2 and latches the monotone
    re-vote flag; otherwise [AlreadyVoted] - a no-op transition to the
    terminal phase (handler.rs:830-839). *)
let revote_step mut s =
  if revote_gate mut s then
    [
      {
        s with
        phase = Done;
        v1_voted = Header_set.add H2 s.v1_voted;
        v1_revoted = true;
      };
    ]
  else [ { s with phase = Done } ]

(** The transition relation, parameterized by the mutation; [Done] is
    terminal and stutter-closed by the kernel. *)
let next_with mut s =
  match s.phase with
  | Vote -> vote_step s
  | Certify -> certify_step s
  | Revote -> revote_step mut s
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The atom vocabulary: exactly what the statement quantifies over, plus
    the terminal probe for the sanity suite. *)
type atom =
  | Revoted
      (** V1's latched re-vote on slot (V3, R0) - the fall-through at
          handler.rs:840-847 fired *)
  | Cert_exists
      (** a certificate for slot (V3, R0) exists ANYWHERE: in the union of
          all dags or in V3's private slot *)
  | Cert_in_v1_dag
      (** V1's OWN dag holds the slot's certificate - the exact evidence
          the guard at handler.rs:824-839 consults *)
  | At_done  (** terminal phase reached *)

(** Atom valuation over global states. *)
let label a s =
  match a with
  | Revoted -> s.v1_revoted
  | Cert_exists ->
      Option.is_some s.v3_private
      || Bool.not (Validator_set.is_empty s.cert_holders)
  | Cert_in_v1_dag -> Validator_set.mem Validator.V1 s.cert_holders
  | At_done -> (
      match s.phase with
      | Done -> true
      | Vote | Certify | Revote -> false)

(** Render an atom for test/diagnostic output. *)
let atom_to_string = function
  | Revoted -> "revote(v1,v3/r0," ^ header_to_string H2 ^ ")"
  | Cert_exists -> "cert-exists(v3/r0)"
  | Cert_in_v1_dag -> "cert-in-v1-dag(v3/r0)"
  | At_done -> "done"

(** The checker instance on the shared LCF kernel. *)
module Checker = System.Make (State) (View)

(** The spec under a mutation: single initial state, mutation-parameterized
    transitions, the V1-only view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
