(** Ahead-certificate round catch-up: the lean CONSENSUS-EXT interpreted
    system behind [ahead-certificate-implies-round-catchup]
    ({!Catchup_statements}).

    Abstraction. A well-signed round-r certificate is transferable evidence
    of network progress: its 2f+1 signers could not have produced it without
    first holding every parent round, so at least f+1 of them are honest
    validators that processed the whole sub-r prefix (signature verification
    precedes any forwarding, state_sync/cert_validator.rs:100-108 and
    114-130; vote handlers block on parent possession,
    network/handler.rs:602-693; certificate acceptance requires parents in
    storage, state_sync/cert_manager.rs:103-118). telcoin-network extracts
    that evidence without waiting for the certificate's contents:
    [forward_verified_certs] sends [(vec![], r - 1)] as
    [minimal_round_for_parents] (cert_validator.rs:133-158, the send at
    157-158) and [Proposer::process_parents] jumps [self.round] forward on
    its Greater arm (proposer.rs:392-426, entry 642-652), so a lagging
    proposer stops emitting obsolete headers.

    Model. Three rounds of propose -> certify -> deliver, then a [Catch_up]
    micro-phase between [Deliver R2] and [Commit_eval] - the model analog of
    the 157-158 send feeding [process_parents]. The micro-phase MUST be its
    own step: if repair delivery and the round jump were one transition, the
    statement's antecedent (holding an R2 certificate while still at
    proposer round R0) would hold at no reachable state and
    [prove_nonvacuous] would refuse the proof. Votes are collapsed into
    certification: every modeled branch is vote-deterministic, and the lag
    victim's missing vote still leaves exactly the 2f+1 = 3 signers a
    certificate needs (aggregators/certificates.rs:24-44). The hidden
    branching is a network event resolved at the Deliver R0 transition:
    [No_lag] (fault-free) or [Lag_v2] (V2 is excluded from R1/R2 proposing,
    certification, and delivery, then force-repaired IN FULL at Deliver R2
    under the house bounded-delay fairness). The lag branch is what makes
    the statement's antecedent reachable: it creates a validator that holds
    an ahead (R2) certificate while its own proposer round is still R0.

    Role mapping of the four kernel slots: V2 is the lag victim - its view
    is its local record (certificate possession plus proposer round), the
    projection {!System.Make} requires even though no statement of this
    family uses K (the family is pure temporal liveness: any K over quorum
    progress at the one antecedent-true state would sit on a singleton view
    class AND be entailed by V2's own R2 holding, so it was dropped - see
    {!Catchup_statements}). V0 and V1 are the honest peers whose
    certificates repair V2; V3 fills the fourth committee slot and is
    protocol-obedient here (the lag composes with a cooperative committee,
    the same <= f discipline as the frozen model's [Leader_crash]). *)

(** Rounds R0..R2, local to this model so the family stays isolated from
    the frozen {!Tn_state}. *)
type round = R0 | R1 | R2

(** Injective index for ordering and arithmetic comparisons over rounds. *)
let round_index = function R0 -> 0 | R1 -> 1 | R2 -> 2

(** Total order on rounds via {!round_index}. *)
let round_compare a b = Int.compare (round_index a) (round_index b)

(** Render a round as in the frozen model ("r0".."r2"). *)
let round_to_string r = "r" ^ Int.to_string (round_index r)

(** Predecessor round: the catch-up jump target for a round-r certificate is
    r - 1 (proposer.rs:392-426 consuming cert_validator.rs:157-158). *)
let round_pred = function R0 -> None | R1 -> Some R0 | R2 -> Some R1

(** A certificate identifier: author and round. No equivocation variant -
    every branch of this family is protocol-obedient, so one slot holds at
    most one certificate. *)
type digest = { author : Validator.t; round : round }

(** Lexicographic total order on digests (author, then round). *)
let digest_compare d1 d2 =
  let c = Validator.compare d1.author d2.author in
  if Int.equal c 0 then round_compare d1.round d2.round else c

(** Render a digest as "author/round". *)
let digest_to_string d =
  Validator.to_string d.author ^ "/" ^ round_to_string d.round

(** Certificate sets, the dag/possession representation. *)
module Digest_set = Set.Make (struct
  type t = digest

  let compare = digest_compare
end)

(** Per-validator storage. *)
module Validator_map = Map.Make (Validator)

(** The hidden branch, resolved at the Deliver R0 transition: [No_lag] is
    the fault-free run; [Lag_v2] excludes V2 from all R1/R2 traffic
    (proposing, certification, delivery) until the forced full repair at
    Deliver R2. Chosen at Deliver R0 rather than the first transition
    because the two branches are behaviorally identical through round R0 -
    sharing the prefix keeps the reachable set minimal without weakening the
    view collision (divergence only begins at R1). *)
type lag_choice = Lag_unchosen | No_lag | Lag_v2

(** Injective index for ordering lag choices. *)
let lag_index = function Lag_unchosen -> 0 | No_lag -> 1 | Lag_v2 -> 2

(** Total order on lag choices via {!lag_index}. *)
let lag_compare a b = Int.compare (lag_index a) (lag_index b)

(** The phase machine: propose -> certify -> deliver per round (votes
    collapsed into certification, see the module header), then the
    [Catch_up] micro-phase between [Deliver R2] and [Commit_eval], then the
    terminal stutter at [Done]. *)
type phase =
  | Propose of round
  | Certify of round
  | Deliver of round
  | Catch_up
  | Commit_eval
  | Done

(** Injective index for ordering phases. *)
let phase_index = function
  | Propose r -> 10 + round_index r
  | Certify r -> 20 + round_index r
  | Deliver r -> 30 + round_index r
  | Catch_up -> 40
  | Commit_eval -> 41
  | Done -> 42

(** Total order on phases via {!phase_index}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** Per-validator local state, the knowledge ground for the lag victim:
    [dag] is the set of certificates the validator holds (its certificate
    store), [proposer_round] the round its own proposer last worked
    (Proposer::round, proposer.rs:392-426). Global fields - the hidden lag
    branch, other validators' stores, the phase - are invisible to it. *)
type local = { dag : Digest_set.t; proposer_round : round }

(** The pre-participation local: empty store, proposer at R0. *)
let local_empty = { dag = Digest_set.empty; proposer_round = R0 }

(** Total order on locals (dag, then proposer round). *)
let local_compare l1 l2 =
  let c = Digest_set.compare l1.dag l2.dag in
  if Int.equal c 0 then round_compare l1.proposer_round l2.proposer_round
  else c

(** The global state: phase machine position, hidden lag branch, formed
    certificates (unforgeability by construction: a value is in [certs] only
    when the model assembled its quorum), and per-validator locals. *)
type state = {
  phase : phase;
  lag : lag_choice;
  certs : Digest_set.t;
  locals : local Validator_map.t;
}

(** Total order on global states (phase, lag, certs, locals). *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = lag_compare s1.lag s2.lag in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Digest_set.compare s1.certs s2.certs in
      if Bool.not (Int.equal c2 0) then c2
      else Validator_map.compare local_compare s1.locals s2.locals

(** The ordered global-state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** The ordered view module for {!System.Make}: a view is a local record -
    the lag victim's own, or the constant {!local_empty} for the three
    non-agent slots. *)
module View = struct
  type t = local

  let compare = local_compare
end

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(** The lag victim V2: the only knowledge agent of this family. *)
let victim = Validator.V2

(** The validator's local record, defaulting to {!local_empty}. *)
let local_of state v =
  Option.fold ~none:local_empty ~some:Fun.id
    (Validator_map.find_opt v state.locals)

(** View projection: the victim sees exactly its local record; every other
    validator gets the constant empty view (not a knowledge agent - it never
    appears under K, and a constant view makes its K degenerate by
    construction). *)
let view v s = if Validator.equal v victim then local_of s v else local_empty

(** Replace one validator's local by applying [f]. *)
let update_local v f state =
  { state with locals = Validator_map.add v (f (local_of state v)) state.locals }

(** The initial state: Propose R0, lag unresolved, nothing formed. *)
let initial =
  {
    phase = Propose R0;
    lag = Lag_unchosen;
    certs = Digest_set.empty;
    locals =
      List.fold_left
        (fun acc v -> Validator_map.add v local_empty acc)
        Validator_map.empty roster;
  }

(** Gate deletion for the confirm-by-mutation pin. [Drop_catch_up] deletes
    the round jump performed by the [Catch_up] micro-phase - the model
    analog of removing the [minimal_round_for_parents] send at
    cert_validator.rs:157-158. No sibling path repairs the deletion: the
    only other writer of [proposer_round] is [propose], which in the
    [Lag_v2] branch never lists V2 after R0 and never runs again after
    Deliver R2 (in the real system the only other parents sender is the
    certificate aggregator, aggregators/certificates.rs:24-44, which needs a
    2f+1 same-round quorum the starved node cannot assemble). Under the
    mutation the terminal [Done] state is reached with V2 still at proposer
    round R0 while holding an R2 certificate, refuting the catch-up
    leads-to conjunct. *)
type mutation = Pristine | Drop_catch_up

(** Round-r proposers: everyone in R0; from R1 on, the [Lag_v2] branch
    excludes the victim (its proposer is partitioned off and stays at R0 -
    exactly the lagging-proposer condition of proposer.rs:392-426). The
    [Lag_unchosen] arm is unreachable at R1/R2 (the branch resolves at the
    Deliver R0 transition) and conservatively lists everyone. *)
let proposers_of r lag =
  match r with
  | R0 -> roster
  | R1 | R2 -> (
      match lag with
      | Lag_unchosen -> roster
      | No_lag -> roster
      | Lag_v2 ->
          List.filter (fun v -> Bool.not (Validator.equal v victim)) roster)

(** Propose round [r]: each proposer's [proposer_round] advances to [r]
    (Proposer emitting its next header, proposer.rs:642-652). *)
let propose r state =
  let advanced =
    List.fold_left
      (fun acc v -> update_local v (fun l -> { l with proposer_round = r }) acc)
      state (proposers_of r state.lag)
  in
  { advanced with phase = Certify r }

(** Certify round [r]: one certificate forms per round-r proposer (the vote
    quorum is deterministic - even without the lagging victim, the three
    remaining validators are exactly the 2f+1 = 3 signers needed,
    aggregators/certificates.rs:24-44) and each aggregating author stores
    its own certificate; broadcast delivery to the others is the next
    phase. *)
let certify r state =
  let formed = List.map (fun v -> { author = v; round = r }) (proposers_of r state.lag) in
  let with_certs =
    List.fold_left
      (fun acc d ->
        update_local d.author
          (fun l -> { l with dag = Digest_set.add d l.dag })
          { acc with certs = Digest_set.add d acc.certs })
      state formed
  in
  { with_certs with phase = Deliver r }

(** The formed certificates of one round. *)
let round_certs r state =
  Digest_set.filter
    (fun d -> Int.equal (round_index d.round) (round_index r))
    state.certs

(** Add every certificate in [ds] to each receiver's store. *)
let deliver_to receivers ds state =
  List.fold_left
    (fun acc v ->
      update_local v (fun l -> { l with dag = Digest_set.union ds l.dag }) acc)
    state receivers

(** Deliver round [r]. R0: full broadcast, and the hidden lag branch
    resolves here (both branches receive identical R0 traffic - the honest
    view collision this family's knowledge contingency rests on). R1: full
    broadcast, except the [Lag_v2] branch suppresses the victim's copy. R2:
    full broadcast, and the [Lag_v2] branch force-repairs the victim IN
    FULL (every certificate it missed) - the house bounded-delay fairness,
    modeling state-sync catching the partitioned node up. *)
let deliver r state =
  match r with
  | R0 ->
      List.map
        (fun lag ->
          {
            (deliver_to roster (round_certs R0 state) state) with
            lag;
            phase = Propose R1;
          })
        [ No_lag; Lag_v2 ]
  | R1 ->
      let receivers =
        match state.lag with
        | Lag_unchosen -> roster
        | No_lag -> roster
        | Lag_v2 ->
            List.filter (fun v -> Bool.not (Validator.equal v victim)) roster
      in
      [ { (deliver_to receivers (round_certs R1 state) state) with phase = Propose R2 } ]
  | R2 ->
      let broadcast =
        { (deliver_to roster (round_certs R2 state) state) with phase = Catch_up }
      in
      let repaired =
        match broadcast.lag with
        | Lag_unchosen -> broadcast
        | No_lag -> broadcast
        | Lag_v2 ->
            update_local victim
              (fun l -> { l with dag = Digest_set.union broadcast.certs l.dag })
              broadcast
      in
      [ repaired ]

(** The highest round among a set of certificates, [None] when empty. *)
let max_round ds =
  Digest_set.fold
    (fun d acc ->
      Option.fold ~none:(Some d.round)
        ~some:(fun r -> Some (if 0 < round_compare d.round r then d.round else r))
        acc)
    ds None

(** One validator's catch-up: holding a certificate of round r strictly
    ahead of [proposer_round + 1] jumps the proposer to r - 1 - the
    [minimal_round_for_parents] hint (cert_validator.rs:133-158) consumed by
    [process_parents]' Greater arm (proposer.rs:392-426). *)
let catch_up_local l =
  Option.fold ~none:l
    ~some:(fun m ->
      if round_index l.proposer_round + 1 < round_index m then
        Option.fold ~none:l
          ~some:(fun target -> { l with proposer_round = target })
          (round_pred m)
      else l)
    (max_round l.dag)

(** The [Catch_up] micro-phase: every validator applies {!catch_up_local}.
    [Drop_catch_up] deletes exactly the jump (the step still advances the
    phase, so the mutated graph differs only in the deleted repair). *)
let catch_up mut state =
  let jumped =
    match mut with
    | Pristine ->
        List.fold_left (fun acc v -> update_local v catch_up_local acc) state roster
    | Drop_catch_up -> state
  in
  [ { jumped with phase = Commit_eval } ]

(** The mutation-parameterized transition relation; [Done] is terminal and
    stutter-closed by the kernel. *)
let next_with mut state =
  match state.phase with
  | Propose r -> [ propose r state ]
  | Certify r -> [ certify r state ]
  | Deliver r -> deliver r state
  | Catch_up -> catch_up mut state
  | Commit_eval -> [ { state with phase = Done } ]
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The atom vocabulary: exactly what the statement quantifies over.
    [Cert_formed d] - the certificate exists globally; [In_dag (v, d)] - v
    holds it; [Proposer_round_le]/[Proposer_round_ge] - bounds on a
    validator's own proposer round; [At_done] - terminal phase (sanity
    tests). *)
type atom =
  | Cert_formed of digest
  | In_dag of Validator.t * digest
  | Proposer_round_le of Validator.t * round
  | Proposer_round_ge of Validator.t * round
  | At_done

(** Atom valuation over global states. *)
let label a state =
  match a with
  | Cert_formed d -> Digest_set.mem d state.certs
  | In_dag (v, d) -> Digest_set.mem d (local_of state v).dag
  | Proposer_round_le (v, r) ->
      round_index (local_of state v).proposer_round <= round_index r
  | Proposer_round_ge (v, r) ->
      round_index r <= round_index (local_of state v).proposer_round
  | At_done -> (
      match state.phase with
      | Done -> true
      | Propose _ | Certify _ | Deliver _ | Catch_up | Commit_eval -> false)

(** Render an atom for formula pretty-printing. *)
let atom_to_string = function
  | Cert_formed d -> "cert(" ^ digest_to_string d ^ ")"
  | In_dag (v, d) ->
      "dag(" ^ Validator.to_string v ^ "," ^ digest_to_string d ^ ")"
  | Proposer_round_le (v, r) ->
      "proposer-round(" ^ Validator.to_string v ^ ")<=" ^ round_to_string r
  | Proposer_round_ge (v, r) ->
      "proposer-round(" ^ Validator.to_string v ^ ")>=" ^ round_to_string r
  | At_done -> "done"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The spec under one mutation. *)
let spec_of mut = { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine system. *)
let make () = Checker.make spec
