(** Family CONSENSUS-EXT #3: the interpreted system behind
    [unresolved-author-reject-skips-penalty-and-liveness-recovers].

    Abstraction. One honest observer (V2) receives R0 certificate gossip. A
    gossip frame whose author cannot be resolved to a committee member is
    rejected by gossip verification (network-libp2p consensus.rs:1499-1513)
    and the reject is routed through [RejectReason::penalty]
    (consensus.rs:2087-2097) via the reject-handling path
    (consensus.rs:1007-1026, 1049-1099); the author_resolved guard
    (consensus.rs:2094-2095) SKIPS the penalty - an unattributable frame
    charges nobody. The observer records only the attribute-free fact that
    an unresolved-author frame was rejected: the gossipsub cache never
    redelivers, so no digest, content, or author of the frame is ever
    retained locally. The dropped honest certificate is recovered by the
    proposer-sourced MissingParents fetch at vote time (primary network
    handler.rs:653-668, 930-954), so liveness survives the reject.

    Hidden branching ([unres], resolved into all three live branches at the
    first transition - the {!Tn_model} pattern):
    - [Unres_none]: every frame arrives resolved; nothing is rejected;
    - [Unres_lag_v1]: honest V1's frame reaches V2 author-unresolved
      (resolution lag) and is rejected - the rejected frame's author is
      HONEST;
    - [Unres_junk_drop]: V3 injects one unattributable junk frame at V2
      (rejected) while V1's frame is lost in transit - the rejected frame's
      author is BYZANTINE.
    Both degraded branches recover V1's certificate through the SAME
    fetch-on-vote step out of [Vote_r1], and the reject flag stores no
    attribution, so V2's local view is identical across [Unres_lag_v1] and
    [Unres_junk_drop] at every phase from the reject through [Done]. That
    collision is the card's false witness: at a flagged lag state the fact
    "the rejected author was Byzantine" is false while a view-identical
    junk state makes it true (and symmetrically for "honest"), so neither
    K_V2 conjunct can hold - the Skip is exactly the
    punish-only-what-you-know rule.

    Role mapping of the validator slots (knowledge agents must be
    {!Validator.t} values): V2 is the SOLE knowledge agent, the observer
    that rejects the unresolved frame. V0 is an honest peer whose
    certificate always arrives; V1 is the honest author whose frame lags or
    drops; V3 is the Byzantine junk injector, silent on the consensus path
    (it forms no R0 certificate). V0, V1, and V3 carry the constant empty
    view and never appear under [K]/[Everyone]/[Common].

    Faithfulness notes:
    - an R0 certificate is collapsed to its author's identity (one round,
      one variant; the statement quantifies over no digest structure);
    - V3 forms no certificate, so the producers are exactly {V0, V1, V2}
      and the 2f+1 = 3 completion quorum needs ALL three - which is why a
      severed V1 -> V2 path is fatal under the mutation;
    - direct gossip delivery FROM a peer is severed by a V2-side ban of
      that peer (a Fatal charge applies a ban, peers/all_peers.rs:853-873,
      peers/peer.rs:213-237; the ban severs the connection,
      peers/all_peers.rs:261-303, and admission is denied,
      peers/behavior.rs:102-105); but the vote-time recovery of a missing
      certificate is PROPOSER-sourced - the MissingParents flow
      (primary network handler.rs:653-668, 930-954) has the header's
      proposer re-send the missing parent certificates, stored with no
      gate on whether the parent's AUTHOR is locally banned, so banning an
      author does NOT block a third party (an unbanned proposer/peer) from
      supplying that author's certificate to V2.

    [mutation] is the confirm-by-mutation harness:
    [No_author_resolved_guard] deletes the author_resolved guard
    (consensus.rs:2094-2095) so the unresolved-author reject
    unconditionally Fatal-charges its propagation source. In the lag branch
    that bans honest V1 at V2, and because the ban gates the fetch path
    too, V2 never reassembles the quorum: [Af done] is refuted alongside
    the no-ban / no-penalty conjuncts. *)

(** The hidden environment choice behind the rejected frame: no unresolved
    frame at all, honest V1's frame arriving author-unresolved, or V3's
    unattributable junk injection paired with the in-transit loss of V1's
    frame. [Unres_unchosen] is the pre-branch initial value, resolved into
    the three live branches at the first transition. *)
type unres = Unres_unchosen | Unres_none | Unres_lag_v1 | Unres_junk_drop

(** Fixed index underlying the total order on {!unres}. *)
let unres_index = function
  | Unres_unchosen -> 0
  | Unres_none -> 1
  | Unres_lag_v1 -> 2
  | Unres_junk_drop -> 3

(** Total deterministic comparator for {!unres}. *)
let unres_compare a b = Int.compare (unres_index a) (unres_index b)

(** Renderer for {!unres}. *)
let unres_to_string = function
  | Unres_unchosen -> "unchosen"
  | Unres_none -> "none"
  | Unres_lag_v1 -> "lag-v1"
  | Unres_junk_drop -> "junk-drop"

(** The four-step phase machine: certificates form and the hidden branch
    resolves out of [Start]; R0 gossip (and the reject,
    consensus.rs:1499-1513) lands at [Deliver_r0]; the missing-parent
    fetch (handler.rs:225-230) and the quorum-gated completion happen out
    of [Vote_r1]; [Done] is terminal (stutter-closed by the kernel). *)
type phase = Start | Deliver_r0 | Vote_r1 | Done

(** Fixed index underlying the total order on {!phase}. *)
let phase_index = function Start -> 0 | Deliver_r0 -> 1 | Vote_r1 -> 2 | Done -> 3

(** Total deterministic comparator for {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** Renderer for {!phase}. *)
let phase_to_string = function
  | Start -> "start"
  | Deliver_r0 -> "deliver:r0"
  | Vote_r1 -> "vote:r1"
  | Done -> "done"

(** Validator sets: certificate possession keyed by author, and V2-side
    bans. *)
module Validator_set = Set.Make (Validator)

(** V2's local state - the knowledge ground for [K_V2]. [saw_unres] is the
    persistent ATTRIBUTE-FREE reject flag (the rejected frame leaves no
    digest/content/author behind, and the no-redelivery gossipsub cache
    means late resolution of V1's identity never retro-attributes it);
    [held] the R0 certificates V2 holds, keyed by author; [banned] the
    peers V2 has fatally banned (empty in every pristine run - the
    author_resolved guard, consensus.rs:2094-2095, is precisely what keeps
    it empty); [penalized] whether V2 charged any peer for the reject. *)
type local = {
  saw_unres : bool;
  held : Validator_set.t;
  banned : Validator_set.t;
  penalized : bool;
}

(** The empty local: V2 before any delivery. Also the constant view of the
    non-agent slots V0, V1, V3. *)
let local_empty =
  {
    saw_unres = false;
    held = Validator_set.empty;
    banned = Validator_set.empty;
    penalized = false;
  }

(** Total deterministic comparator over every field of {!local}. *)
let local_compare l1 l2 =
  let c = Bool.compare l1.saw_unres l2.saw_unres in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Validator_set.compare l1.held l2.held in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Validator_set.compare l1.banned l2.banned in
      if Bool.not (Int.equal c2 0) then c2
      else Bool.compare l1.penalized l2.penalized

(** The global state: the phase, the hidden branch, and V2's local state.
    Certificate existence is deterministic (the producers {V0, V1, V2}
    certify out of [Start] in every branch), so it needs no field; V0, V1,
    and V3 hold no statement-relevant local state at all. *)
type state = { phase : phase; unres : unres; v2 : local }

(** Total deterministic comparator over every field of {!state}. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = unres_compare s1.unres s2.unres in
    if Bool.not (Int.equal c1 0) then c1
    else local_compare s1.v2 s2.v2

(** Ordered global states for the kernel functor. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** Ordered views for the kernel functor: views are locals, and only V2's
    is ever informative. *)
module View = struct
  type t = local

  let compare = local_compare
end

(** View projection: V2 sees exactly its local state (and nothing global -
    neither the phase nor the hidden [unres] branch); V0, V1, and V3 are
    not knowledge agents in this family and get the constant empty view. *)
(* 4-member committee threshold (f = 1): 2f+1 = 3. The global
   Validator.quorum/support now describe the ten-member tn committee. *)
let quorum = 3

let view v (s : state) =
  match v with
  | Validator.V2 -> s.v2
  | Validator.V0 | Validator.V1 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      local_empty

(** The single initial state: [Start], hidden branch unresolved, V2
    empty. *)
let initial = { phase = Start; unres = Unres_unchosen; v2 = local_empty }

(** The R0 certificate producers: V3 is silent on the consensus path and
    forms none, so the 2f+1 = 3 completion quorum requires all three -
    every producer's certificate must reach V2. *)
let producers =
  Validator_set.of_list [ Validator.V0; Validator.V1; Validator.V2 ]

(** Which authors' certificates reach V2 by direct gossip at [Deliver_r0]:
    V1's frame is withheld in both degraded branches (rejected unresolved
    under lag, lost in transit under junk-drop); V0's and V2's own always
    land. [Unres_unchosen] never reaches [Deliver_r0]; its arm delivers
    nothing. *)
let gossip_sources = function
  | Unres_unchosen -> Validator_set.empty
  | Unres_none -> producers
  | Unres_lag_v1 -> Validator_set.of_list [ Validator.V0; Validator.V2 ]
  | Unres_junk_drop -> Validator_set.of_list [ Validator.V0; Validator.V2 ]

(** The propagation source of the rejected unresolved-author frame, if one
    arrives: honest V1 under resolution lag (it gossips its own header),
    Byzantine V3 under junk injection, nobody otherwise. This is the peer
    the deleted guard would Fatal-charge (RejectReason::penalty,
    consensus.rs:2087-2097). *)
let rejected_source = function
  | Unres_unchosen -> None
  | Unres_none -> None
  | Unres_lag_v1 -> Some Validator.V1
  | Unres_junk_drop -> Some Validator.V3

(** Gate deletion for the confirm-by-mutation pin.
    [No_author_resolved_guard] removes the author_resolved penalty skip
    (consensus.rs:2094-2095): the unresolved-author reject then
    unconditionally Fatal-charges its propagation source, banning honest
    V1 at V2 in the lag branch (peers/all_peers.rs:853-873,
    peers/peer.rs:213-237). This is an UNJUST accountability fault - V2
    bans and penalizes a peer it cannot attribute the frame to - and it
    refutes the statement through the no-ban / no-penalty (skip)
    conjuncts. Liveness is NOT the refuting lever: the vote-time recovery
    is proposer-sourced (handler.rs:653-668), so V1's certificate still
    reaches V2 and the quorum reassembles even under the ban - [Af done]
    holds on the mutated system (asserted by the mutated-liveness-survives
    regression). *)
type mutation = Pristine | No_author_resolved_guard

(** The [Deliver_r0] step: gossip lands (gated by V2-side bans - vacuous in
    pristine runs, where no ban ever forms), the unresolved frame if any is
    rejected setting the attribute-free flag (consensus.rs:1499-1513), and
    the penalty gate runs: pristine skips it (the author_resolved guard),
    the mutation Fatal-charges the propagation source. *)
let deliver mut state =
  let l = state.v2 in
  let held =
    Validator_set.union l.held
      (Validator_set.diff (gossip_sources state.unres) l.banned)
  in
  let flagged =
    {
      l with
      held;
      saw_unres = l.saw_unres || Option.is_some (rejected_source state.unres);
    }
  in
  let charged =
    match mut with
    | Pristine -> flagged
    | No_author_resolved_guard ->
        Option.fold ~none:flagged
          ~some:(fun src ->
            {
              flagged with
              banned = Validator_set.add src flagged.banned;
              penalized = true;
            })
          (rejected_source state.unres)
  in
  [ { state with phase = Vote_r1; v2 = charged } ]

(** The [Vote_r1] step: fetch-on-vote pulls every missing producer
    certificate through the PROPOSER-sourced MissingParents flow
    (primary network handler.rs:653-668, 930-954) - the SAME phase point
    in both degraded branches, which is what keeps V2's views colliding
    through [Done]. The fetch is NOT gated by a ban on the certificate's
    author: a banned author's certificate is still supplied by an unbanned
    proposer/peer, so completion (the full 2f+1 = 3 quorum) reassembles
    even when V2 has fatally banned an author - liveness survives the ban.
    A quorum-less state has no successor and the kernel stutter-closes it. *)
let advance state =
  let l = state.v2 in
  let fetched = Validator_set.diff producers l.held in
  let held = Validator_set.union l.held fetched in
  if quorum <= Validator_set.cardinal held then
    [ { state with phase = Done; v2 = { l with held } } ]
  else []

(** The transition relation, parameterized by the gate deletion. The
    hidden branch resolves into all three live values at the first
    transition (the {!Tn_model} pattern), so V2's honest view collides
    across branches from the reject onward. *)
let next_with mut state =
  match state.phase with
  | Start ->
      List.map
        (fun unres -> { state with phase = Deliver_r0; unres })
        [ Unres_none; Unres_lag_v1; Unres_junk_drop ]
  | Deliver_r0 -> deliver mut state
  | Vote_r1 -> advance state
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The atom vocabulary - exactly what the statement and its tests
    quantify over. *)
type atom =
  | Saw_unres_2
      (** V2's persistent attribute-free flag: an unresolved-author frame
          was rejected (consensus.rs:1499-1513) *)
  | Unres_author_honest
      (** RUN-FACT: the hidden branch is [Unres_lag_v1] - the rejected
          frame was authored by honest V1 *)
  | Unres_author_byz
      (** RUN-FACT: the hidden branch is [Unres_junk_drop] - the rejected
          frame was V3's junk *)
  | Banned_2 of Validator.t
      (** V2 has fatally banned this peer (peers/all_peers.rs:853-873) *)
  | Penalized_by_2  (** V2 charged some peer for the reject *)
  | Holds_cert_2 of Validator.t
      (** this author's R0 certificate is in V2's store *)
  | Quorum_2  (** V2 holds a 2f+1 = 3 certificate quorum *)
  | At_done  (** the terminal phase *)

(** Labeling of atoms over global states; every match spells out its
    constructors. *)
let label a state =
  match a with
  | Saw_unres_2 -> state.v2.saw_unres
  | Unres_author_honest -> (
      match state.unres with
      | Unres_lag_v1 -> true
      | Unres_unchosen | Unres_none | Unres_junk_drop -> false)
  | Unres_author_byz -> (
      match state.unres with
      | Unres_junk_drop -> true
      | Unres_unchosen | Unres_none | Unres_lag_v1 -> false)
  | Banned_2 v -> Validator_set.mem v state.v2.banned
  | Penalized_by_2 -> state.v2.penalized
  | Holds_cert_2 v -> Validator_set.mem v state.v2.held
  | Quorum_2 -> quorum <= Validator_set.cardinal state.v2.held
  | At_done -> (
      match state.phase with
      | Done -> true
      | Start | Deliver_r0 | Vote_r1 -> false)

(** Renderer for {!atom}. *)
let atom_to_string = function
  | Saw_unres_2 -> "saw-unres(v2)"
  | Unres_author_honest -> "unres-author-honest"
  | Unres_author_byz -> "unres-author-byz"
  | Banned_2 v -> "banned(v2," ^ Validator.to_string v ^ ")"
  | Penalized_by_2 -> "penalized-by(v2)"
  | Holds_cert_2 v -> "holds-cert(v2," ^ Validator.to_string v ^ ")"
  | Quorum_2 -> "quorum(v2)"
  | At_done -> "done"

(** The kernel instance for this family. *)
module Checker = System.Make (State) (View)

(** The spec under a given gate deletion. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
