(** Interpreted system for the stalled-commit / timeout-fetch slice of
    telcoin-network consensus: the commit-timeout certificate fetch is
    gated on pending fetch targets - a totally starved validator (no
    certificate received at all) has no targets and stays ignorant, while
    a lagged validator that received a forward-reference certificate
    regains the missing quorum (statement
    stalled-commit-timeout-fetch-gated-by-pending-targets).

    Mechanisms modeled, keyed to Telcoin-Association/telcoin-network:
    - the commit-progress timer, reset on every commit
      (crates/consensus/primary/src/state_sync/gc.rs:42-58);
    - the timeout tick arm of the GarbageCollector select loop
      (gc.rs:66-92, the tick arm at 72-77), which kicks the certificate
      fetcher when no commit landed within the interval - here the
      [Timeout_fetch] micro-step after [Commit_eval];
    - the certificate fetcher: the Kick arm fetches ONLY when no task is
      in flight AND the targets map is non-empty
      (crates/consensus/primary/src/certificate_fetcher.rs:181-190, the
      gate at :184), request bounds (exclusive lower bound = gc round,
      skip = locally written rounds, certificate_fetcher.rs:241-256;
      request shape crates/consensus/primary/src/network/message.rs), and
      the fetch task pulling missing certificates from peers
      (certificate_fetcher.rs:259-286) - abstracted to one deterministic
      copy of every certificate any validator holds into each validator
      with a non-empty pending set, and a no-op for every other validator;
    - the ONLY population sites of the targets map
      (certificate_fetcher.rs:212, inside the [Ancestors] branch): a
      received certificate with missing parents
      (crates/consensus/primary/src/state_sync/cert_manager.rs:169-175)
      or a received too-new certificate
      (crates/consensus/primary/src/state_sync/cert_validator.rs:203) -
      both require RECEIVING a certificate, and round-1 certificates
      short-circuit on genesis parents with no fetch
      (cert_manager.rs:144-153);
    - fetch-on-vote parent synchronization (primary handler.rs:693-738):
      voting on a header retrieves its missing parent certificates - the
      sibling repair path the starvation MUST also suppress (see the
      [Starve_v2] note below);
    - the parent-quorum proposal gate (proposer.rs:546-553): a validator
      proposes round r+1 only when holding 2f+1 round-r parents;
    - quorum certification (votes.rs:42-89, certificate.rs:225-251) and
      the commit rule (bullshark.rs:192-206), both abstracted to
      possession thresholds over the modeled dags.

    Role mapping of the four {!Validator.t} slots: [V2] is the stall
    victim and the ONLY knowledge agent - its view is its full local
    state. [V0], [V1] and [V3] are cooperative peers (the statement needs
    no Byzantine branching, so the model is the cooperative slice); they
    never appear under [K]/[Everyone]/[Common] and their view is the
    constant empty local.

    Abstraction decisions:
    - Certificate possession is delivery-borne: [Certify r] records
      formation in the global [certs] set only (vote aggregation,
      votes.rs:42-89); a certificate enters a validator's dag through
      [Deliver r] or through a fetch. This grounds the statement's false
      witness exactly: the starved victim's local state after [Deliver R1]
      is bit-identical to its state before [Certify R1], so R1-quorum
      existence is epistemically contingent for it.
    - The hidden branch is the delivery choice at [Deliver R1]
      ([Delivery_unchosen] until that transition, the house pattern):
      [Deliver_all] is the fair run; [Starve_v2] suppresses ALL
      [Deliver R1] certificate delivery to [V2], AND [Propose R2] header
      delivery to [V2], AND [Deliver R2] certificate delivery to [V2] -
      total starvation, under which [V2] receives NO certificate, its
      fetch targets stay empty, and the timeout Kick is honestly a no-op
      for it (certificate_fetcher.rs:184); [Lag_v2] suppresses the same
      direct deliveries but [Deliver R2] parks ONE forward-reference R2
      certificate in [V2]'s pending buffer, populating its fetch targets.
      The header suppression is mandatory in both flavors: with R2
      headers visible, fetch-on-vote at [Vote R2] would silently
      re-deliver the withheld R1 parent certificates and repair the
      starvation without the timeout fetch (the Unbounded_delay lesson).
      The pending forward reference is part of [V2]'s view, and an R2
      certificate's formation entails an R1 quorum in every reachable
      state - so the lagged victim's ignorance of quorum EXISTENCE cannot
      honestly be claimed, and the statement claims possession recovery
      there instead; the ignorance clause is scoped to the target-free
      total starvation, which the gated fetch never heals.
    - Round R0, explicit votes, and batch payloads are elided: in the
      cooperative slice every header is proposed and gathers quorum votes,
      so they carry no statement-relevant contingency. The [Propose R1] /
      [Vote R1] phases remain as steps so the pre-certification
      false-witness states exist.
    - [Commit_eval] commits each validator holding a full R1 quorum in its
      OWN dag (bullshark.rs:192-206 abstracted to possession); the starved
      victim cannot commit - exactly the stall the gc timer detects. *)

(** The two modeled Narwhal rounds; R0 is elided (nothing the statement
    quantifies over happens there). *)
type round = R1 | R2

(** Total order index for {!round}. *)
let round_index = function R1 -> 0 | R2 -> 1

(** Total order on {!round}. *)
let round_compare a b = Int.compare (round_index a) (round_index b)

(** A certificate abstracted to its slot: author and round. Variants are
    not needed - the cooperative slice never equivocates
    (certificate.rs:225-251 formation, one per slot). *)
type cert = { author : Validator.t; round : round }

(** Total order on {!cert}: author, then round. *)
let cert_compare c1 c2 =
  let c = Validator.compare c1.author c2.author in
  if Bool.not (Int.equal c 0) then c else round_compare c1.round c2.round

(** Ordered module for certificate sets. *)
module Cert = struct
  type t = cert

  let compare = cert_compare
end

(** Certificate sets: dags and the global formation record. *)
module Cert_set = Set.Make (Cert)

(** Per-validator local-state maps. *)
module Validator_map = Map.Make (Validator)

(** Validator sets: the round-2 proposer set. *)
module Validator_set = Set.Make (Validator)

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(* 4-member committee thresholds (f = 1): 2f+1 = 3, f+1 = 2. The global
   Validator.quorum/support now describe the ten-member tn committee. *)
let quorum = 3

(** The stall victim and sole knowledge agent of this family. *)
let victim = Validator.V2

(** The cooperative peers: every validator except the victim. Delivery
    under [Starve_v2] reaches exactly these. *)
let peers = [ Validator.V0; Validator.V1; Validator.V3 ]

(** Per-validator local state - the knowledge ground for [K]: the
    certificates it holds (its dag / certificate store), the pending
    forward-reference certificates whose parents are missing (the
    cert_manager pending buffer plus the fetcher's targets map,
    crates/consensus/primary/src/state_sync/cert_manager.rs
    [get_missing_parents] and certificate_fetcher.rs:212
    [targets.insert] - a received-but-unaccepted certificate is parked
    here, NOT written to the dag), and whether its consensus has
    committed. Global fields (the formation record, the delivery choice,
    the phase) are invisible to it. *)
type local = { dag : Cert_set.t; pending : Cert_set.t; committed : bool }

(** The empty local: no certificates, no pending fetch targets,
    uncommitted. *)
let local_empty =
  { dag = Cert_set.empty; pending = Cert_set.empty; committed = false }

(** Total order on {!local}: dag, then pending, then committed flag. *)
let local_compare l1 l2 =
  let c = Cert_set.compare l1.dag l2.dag in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Cert_set.compare l1.pending l2.pending in
    if Bool.not (Int.equal c1 0) then c1
    else Bool.compare l1.committed l2.committed

(** The hidden delivery branch, resolved at the [Deliver R1] transition:
    [Deliver_all] is the fair run; [Starve_v2] withholds EVERY delivery to
    the victim from [Deliver R1] onward (certificates at [Deliver R1] and
    [Deliver R2], headers at [Propose R2]) - total starvation, under which
    the victim receives no certificate at all, so the real fetcher's
    targets map stays empty and the gc-timeout Kick is a no-op
    (certificate_fetcher.rs:184); [Lag_v2] withholds the same direct
    deliveries but the victim still receives ONE forward-reference R2
    certificate at [Deliver R2], whose missing R1 parents park it pending
    and populate the fetch targets (cert_manager.rs:169-175,
    certificate_fetcher.rs:212) - the run the gc timeout (gc.rs:51)
    genuinely recovers. *)
type delivery = Delivery_unchosen | Deliver_all | Starve_v2 | Lag_v2

(** Total order index for {!delivery}. *)
let delivery_index = function
  | Delivery_unchosen -> 0
  | Deliver_all -> 1
  | Starve_v2 -> 2
  | Lag_v2 -> 3

(** Total order on {!delivery}. *)
let delivery_compare a b = Int.compare (delivery_index a) (delivery_index b)

(** The phase machine: two Narwhal rounds (propose -> vote -> certify ->
    deliver), commit evaluation, the timeout-fetch micro-step (the gc tick
    arm, gc.rs:72-77), then terminal stutter. Execution is elided - no
    atom of this family quantifies over it. *)
type phase =
  | Propose of round
  | Vote of round
  | Certify of round
  | Deliver of round
  | Commit_eval
  | Timeout_fetch
  | Done

(** Total order index for {!phase}. *)
let phase_index = function
  | Propose r -> 10 + round_index r
  | Vote r -> 20 + round_index r
  | Certify r -> 30 + round_index r
  | Deliver r -> 40 + round_index r
  | Commit_eval -> 50
  | Timeout_fetch -> 51
  | Done -> 52

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The global state: phase, the hidden delivery branch, the round-2
    proposer set (validators that passed the parent-quorum gate,
    proposer.rs:546-553), the global formation record (vote aggregation,
    votes.rs:42-89 - possession is tracked separately in the dags), and
    the per-validator locals. *)
type state = {
  phase : phase;
  delivery : delivery;
  proposed_r2 : Validator_set.t;
  certs : Cert_set.t;
  locals : local Validator_map.t;
}

(** Total, deterministic order on {!state} over ALL fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = delivery_compare s1.delivery s2.delivery in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Validator_set.compare s1.proposed_r2 s2.proposed_r2 in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Cert_set.compare s1.certs s2.certs in
        if Bool.not (Int.equal c3 0) then c3
        else Validator_map.compare local_compare s1.locals s2.locals

(** The single initial state: [Propose R1], delivery unresolved, empty
    dags. *)
let initial =
  {
    phase = Propose R1;
    delivery = Delivery_unchosen;
    proposed_r2 = Validator_set.empty;
    certs = Cert_set.empty;
    locals =
      List.fold_left
        (fun acc v -> Validator_map.add v local_empty acc)
        Validator_map.empty roster;
  }

(** The validator's local state, total over the committee. *)
let local_of state v =
  Option.fold ~none:local_empty ~some:Fun.id
    (Validator_map.find_opt v state.locals)

(** View projection: the victim [V2] sees its full local state; the
    cooperative peers are not knowledge agents in this family and get the
    constant empty view - they must never appear under [K] / [Everyone] /
    [Common]. *)
let view v state =
  match v with
  | Validator.V2 -> local_of state victim
  | Validator.V0 | Validator.V1 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      local_empty

(** Ordered global-state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** Ordered view module for {!System.Make}: a view is a local state. *)
module View = struct
  type t = local

  let compare = local_compare
end

(** Gate deletion for the confirm-by-mutation pin: [No_timeout_fetch]
    deletes the timeout tick arm of [GarbageCollector::ready] (the
    [max_round_timeout.tick()] arm whose handler sends
    [CertificateFetcherCommand::Kick], gc.rs:51) - a stalled validator
    never kicks the fetcher. The pin bites in the [Lag_v2] branch, the
    only branch whose pending targets pass the Kick emptiness gate
    (certificate_fetcher.rs:184): fetch-on-vote is suppressed there (no
    R2 header reaches the victim) and delivery is never force-repaired,
    so without the tick the victim's missing R1 quorum never arrives. *)
type mutation = Pristine | No_timeout_fetch

(* --- helpers over locals --- *)

(** Replace one validator's local through [f]. *)
let update_local v f state =
  { state with locals = Validator_map.add v (f (local_of state v)) state.locals }

(** Replace every validator's local through [f]. *)
let update_all_locals f state =
  List.fold_left (fun acc v -> update_local v (f v) acc) state roster

(** The certificates of one round within a certificate set. *)
let certs_of_round r cs =
  Cert_set.filter (fun c -> Int.equal (round_index c.round) (round_index r)) cs

(** The union of every validator's dag - the possession ground of the
    quorum-existence operand. *)
let dag_union state =
  List.fold_left
    (fun acc v -> Cert_set.union (local_of state v).dag acc)
    Cert_set.empty roster

(** How many round-[r] certificates a local dag holds. *)
let own_round_count r l = Cert_set.cardinal (certs_of_round r l.dag)

(** Whether the resolved branch withholds direct delivery to the victim
    (R1/R2 certificates at [Deliver r], R2 headers at [Propose R2]): both
    starvation flavors do. *)
let withholds_v2 = function
  | Delivery_unchosen -> false
  | Deliver_all -> false
  | Starve_v2 -> true
  | Lag_v2 -> true

(** Whether the resolved branch is the lagged flavor: the victim still
    receives one forward-reference R2 certificate at [Deliver R2]
    (cert_manager.rs:169-175, the received-certificate route that
    populates the fetch targets). *)
let lags_v2 = function
  | Delivery_unchosen -> false
  | Deliver_all -> false
  | Starve_v2 -> false
  | Lag_v2 -> true

(* --- transitions --- *)

(** [Propose R1]: every validator proposes its R1 header. Headers and
    votes are elided (cooperative slice: every header gathers quorum
    votes, votes.rs:42-89), so the step only advances the phase; it exists
    so the pre-certification states of the false witness are distinct
    protocol points. *)
let propose_r1 state = { state with phase = Vote R1 }

(** [Vote R1]: honest voting on R1 headers. Fetch-on-vote
    (handler.rs:693-738) would retrieve R0 parents, which are elided, so
    the step only advances the phase. The post-state (phase [Certify R1])
    is the card's quorum-false collision partner: the victim's local there
    is bit-identical to its local in every starved post-[Deliver R1]
    state. *)
let vote_r1 state = { state with phase = Certify R1 }

(** Round-[r] certificate authors: R1 is proposed by the whole committee;
    R2 only by validators that passed the parent-quorum gate
    (proposer.rs:546-553). *)
let certify_authors r state =
  match r with
  | R1 -> roster
  | R2 -> Validator_set.elements state.proposed_r2

(** [Certify r]: quorum votes aggregate into certificates
    (votes.rs:42-89, certificate.rs:225-251), recorded in the global
    formation set only. Possession is delivery-borne: no dag changes here,
    which is what keeps the starved victim's view collided with the
    pre-certification states. *)
let certify r state =
  let formed = List.map (fun v -> { author = v; round = r }) (certify_authors r state) in
  {
    (List.fold_left
       (fun acc c -> { acc with certs = Cert_set.add c acc.certs })
       state formed)
    with phase = Deliver r;
  }

(** Broadcast every round-[r] certificate to the branch's receivers: all
    validators, or only the peers when direct delivery to the victim is
    withheld. *)
let deliver_round r state =
  let receivers = if withholds_v2 state.delivery then peers else roster in
  Cert_set.fold
    (fun c acc ->
      List.fold_left
        (fun acc' v ->
          update_local v (fun l -> { l with dag = Cert_set.add c l.dag }) acc')
        acc receivers)
    (certs_of_round r state.certs)
    state

(** The lagged branch's forward reference: at [Deliver R2] the victim
    receives exactly one R2 certificate whose R1 parents it lacks. Real
    pipeline: a received certificate with missing parents is parked
    pending, NOT accepted into the dag/store
    (crates/consensus/primary/src/state_sync/cert_manager.rs:169-175,
    [get_missing_parents] sending [CertificateFetcherCommand::Ancestors]),
    and the fetcher records the author/round as a pending target
    (certificate_fetcher.rs:212) - the population step the timeout Kick's
    emptiness gate tests. *)
let deliver_forward_ref state =
  Option.fold ~none:state
    ~some:(fun c ->
      update_local victim
        (fun l -> { l with pending = Cert_set.add c l.pending })
        state)
    (Cert_set.min_elt_opt (certs_of_round R2 state.certs))

(** [Deliver r]: R1 resolves the hidden delivery branch into ALL three
    options (the view of every earlier state is shared, so honest views
    collide across the branches - the ground of [K]'s contingency); R2
    delivers under the branch already chosen, with no forced repair for
    the starved victim - [Lag_v2] additionally parks the forward-reference
    certificate in the victim's pending buffer. *)
let deliver r state =
  match r with
  | R1 ->
      List.map
        (fun delivery ->
          { (deliver_round R1 { state with delivery }) with phase = Propose R2 })
        [ Deliver_all; Starve_v2; Lag_v2 ]
  | R2 ->
      let delivered = deliver_round R2 state in
      let lagged =
        if lags_v2 state.delivery then deliver_forward_ref delivered
        else delivered
      in
      [ { lagged with phase = Commit_eval } ]

(** [Propose R2]: the parent-quorum gate (proposer.rs:546-553) - only
    validators holding 2f+1 R1 certificates in their OWN dag propose. The
    starved victim holds none and cannot propose. *)
let propose_r2 state =
  let proposers =
    List.filter
      (fun v -> quorum <= own_round_count R1 (local_of state v))
      roster
  in
  {
    state with
    proposed_r2 =
      List.fold_left
        (fun acc v -> Validator_set.add v acc)
        Validator_set.empty proposers;
    phase = Vote R2;
  }

(** Whether an R2 header reaches this validator: under both starvation
    flavors header delivery to the victim is suppressed - the mandatory
    second clause of the starvation, without which fetch-on-vote at
    [Vote R2] would repair it silently. *)
let header_visible_to v state =
  Bool.not (withholds_v2 state.delivery && Validator.equal v victim)

(** [Vote R2]: each validator votes on the R2 headers it received, and
    voting runs fetch-on-vote (handler.rs:693-738): the header's R1 parent
    certificates - read from its author's dag - are copied into the
    voter's dag. This is the sibling repair path the starvation blocks:
    the victim receives no R2 header, so it never votes and never
    fetches. *)
let vote_r2 state =
  let fetch_parents a v acc =
    let parents = certs_of_round R1 (local_of acc a).dag in
    update_local v (fun l -> { l with dag = Cert_set.union parents l.dag }) acc
  in
  let voted =
    List.fold_left
      (fun acc v ->
        if header_visible_to v acc then
          List.fold_left
            (fun acc' a -> fetch_parents a v acc')
            acc
            (Validator_set.elements acc.proposed_r2)
        else acc)
      state roster
  in
  { voted with phase = Certify R2 }

(** [Commit_eval]: each validator holding a full R1 quorum in its OWN dag
    commits (bullshark.rs:192-206 abstracted to possession). The starved
    victim holds nothing and stays uncommitted - the stall the
    commit-progress timer (gc.rs:42-58) detects. *)
let commit state =
  let commit_one _ l =
    if quorum <= own_round_count R1 l then { l with committed = true }
    else l
  in
  { (update_all_locals commit_one state) with phase = Timeout_fetch }

(** [Timeout_fetch]: the gc timeout tick ([GarbageCollector::ready] ->
    [process_max_round_timeout], gc.rs:51) sends [Kick], and the Kick arm
    fetches ONLY when a pending target exists (certificate_fetcher.rs:184,
    [fetch_task.is_none() && !targets.is_empty()]): each validator with a
    non-empty pending set copies every certificate any validator holds
    into its own dag and accepts its pending certificates (parents now
    present; request bounds certificate_fetcher.rs:241-256, fetch
    certificate_fetcher.rs:259-286). A validator with NO pending target
    fetches nothing - the Kick is a no-op for it, which is why total
    starvation is never healed here. [No_timeout_fetch] deletes the tick
    arm: the phase advances with no copy. *)
let timeout_fetch mut state =
  let fetched =
    match mut with
    | No_timeout_fetch -> state
    | Pristine ->
        let pool = dag_union state in
        update_all_locals
          (fun _ l ->
            if Cert_set.is_empty l.pending then l
            else
              {
                l with
                dag = Cert_set.union (Cert_set.union pool l.pending) l.dag;
                pending = Cert_set.empty;
              })
          state
  in
  { fetched with phase = Done }

(** The mutation-parameterized transition relation; terminal states return
    [[]] and are stutter-closed by {!Checker.make}. *)
let next_with mut state =
  match state.phase with
  | Propose R1 -> [ propose_r1 state ]
  | Propose R2 -> [ propose_r2 state ]
  | Vote R1 -> [ vote_r1 state ]
  | Vote R2 -> [ vote_r2 state ]
  | Certify r -> [ certify r state ]
  | Deliver r -> deliver r state
  | Commit_eval -> [ commit state ]
  | Timeout_fetch -> [ timeout_fetch mut state ]
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(* --- atoms --- *)

(** The atom vocabulary - exactly what the statement and its tests
    quantify over. *)
type atom =
  | Stalled_v2
      (** commit evaluation has been reached and the victim is
          uncommitted *)
  | Cert_quorum_r1
      (** at least 2f+1 = 3 distinct R1 certificates exist in the UNION of
          all validators' dags *)
  | V2_holds_r1_quorum
      (** the victim's OWN dag holds at least 2f+1 R1 certificates *)
  | V2_starved  (** the victim's dag holds NO R1 certificate *)
  | V2_has_fetch_targets
      (** the victim's certificate fetcher holds a pending target - a
          received forward-reference certificate parked with missing
          parents (certificate_fetcher.rs:212), the emptiness gate of the
          Kick arm (certificate_fetcher.rs:184) *)
  | V2_committed  (** the victim's consensus has committed *)
  | At_done  (** terminal phase *)

(** Whether the phase machine has reached commit evaluation - the phase
    half of the stall predicate. *)
let commit_phase_reached = function
  | Propose _ | Vote _ | Certify _ | Deliver _ -> false
  | Commit_eval | Timeout_fetch | Done -> true

(** Atom valuation over global states. *)
let label a state =
  match a with
  | Stalled_v2 ->
      commit_phase_reached state.phase
      && Bool.not (local_of state victim).committed
  | Cert_quorum_r1 ->
      quorum <= Cert_set.cardinal (certs_of_round R1 (dag_union state))
  | V2_holds_r1_quorum ->
      quorum <= own_round_count R1 (local_of state victim)
  | V2_starved -> Cert_set.is_empty (certs_of_round R1 (local_of state victim).dag)
  | V2_has_fetch_targets ->
      Bool.not (Cert_set.is_empty (local_of state victim).pending)
  | V2_committed -> (local_of state victim).committed
  | At_done -> (
      match state.phase with
      | Done -> true
      | Propose _ | Vote _ | Certify _ | Deliver _ | Commit_eval | Timeout_fetch
        ->
          false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Stalled_v2 -> "stalled(v2)"
  | Cert_quorum_r1 -> "cert-quorum(r1)"
  | V2_holds_r1_quorum -> "own-quorum(v2,r1)"
  | V2_starved -> "starved(v2)"
  | V2_has_fetch_targets -> "has-fetch-targets(v2)"
  | V2_committed -> "committed(v2)"
  | At_done -> "done"

(* --- checker instance --- *)

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The spec under a mutation: single initial state, mutation-parameterized
    transitions, victim-only views, the atom valuation. *)
let spec_of mut = { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine system. *)
let make () = Checker.make spec
