(** Leader-swap schedule agreement from committed reputation scores: the
    isolated interpreted system for the CONSENSUS-EXT statement
    [leader-swap-schedule-agreement-from-committed-scores].

    Mechanism modeled (Telcoin-Association/telcoin-network): Bullshark keeps
    per-authority reputation scores as a pure function of the committed
    sub-dag sequence (crates/consensus/primary/src/consensus/
    bullshark.rs:81-97); when a validator commits the sub-dag closing a
    schedule window (the boundary is round-keyed through the header nonce,
    crates/types/src/primary/header.rs:164-166), the single runtime caller
    [update_leader_swap_table], gated on [final_of_schedule]
    (bullshark.rs:333-351), rebuilds that validator's [LeaderSwapTable] from
    the committed scores: the good/bad partition is deterministic given the
    scores (leader_schedule.rs:209-230, tie-break
    crates/types/src/primary/reputation.rs:49-68), the replacement good node
    is drawn with a seed keyed ONLY by [leader_round]
    (leader_schedule.rs:211-213), and every subsequent leader lookup routes
    the round-robin choice (leader_schedule.rs:285-304) through the table
    (leader_schedule.rs:253-271). Same committed boundary + same shared seed
    means every honest validator installs the SAME swapped schedule. The
    install is a purely local act with no broadcast, which is what makes a
    peer's table state a hidden fact.

    Abstraction: one schedule window whose committed sequence carries two
    score-bearing commits, each supported by one certificate per honest
    author and none by V3 - so the accumulated score tally is 2/2/2/0
    (add_score(origin, 1) per supporting certificate, bullshark.rs:81-89),
    the smallest profile whose integer 2-sigma dispersion arms the gate (a
    multiplicity-1 tally 1/1/1/0 truncates standard_dev to 0 and installs
    nothing, leader_schedule.rs:101-103), and V3's next leader slot is
    reassigned. Role mapping for the four validator slots:
    - V0, V1, V2: the honest committee and the ONLY knowledge agents; V0
      doubles as [a_good], the node the shared-seed draw installs into the
      bad slot.
    - V3: the reputation-flagged bad leader (window score 0). It is NOT a
      knowledge agent: its view is constantly empty and it never appears
      under K / Everyone / Common.

    Hidden branching: [lag] - which honest validator commits the boundary
    late - is resolved invisibly into all three branches at the Commit_eval
    transition and force-repaired inside Execute, so every Done state is
    all-swapped. A lagging peer's uncommitted table is invisible to the
    others, so at the No_lag Execute state the operand "every honest
    next-leader is [a_good]" is TRUE while no honest validator can exclude
    the lag branches - knowledge of the operand stays contingent until the
    Execute step marks every local as executed, and common knowledge is
    first attained at Done.

    [swap_installed], [boundary_committed], [leader_next] and the score
    tally are all DERIVED functions of a validator's committed closure -
    the state carries no free fields for them, mirroring the code where the
    table is a deterministic function of the committed sequence. *)

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let roster = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

(** The honest committee, the family's knowledge agents. *)
let honest = [ Validator.V0; Validator.V1; Validator.V2 ]

(** The reputation-flagged bad leader whose next slot the schedule swaps
    out (leader_schedule.rs:209-230); never a knowledge agent here. *)
let bad_leader = Validator.V3

(** The good node the shared leader_round-keyed seed draws as V3's
    replacement (leader_schedule.rs:209-227): the StdRng draw over the
    deterministic good-node list lands on the SAME good node at every
    validator, and the model names that shared pick V0 - its identity is
    immaterial, agreement on it is what the statement asserts. *)
let a_good = Validator.V0

(** Per-validator keyed maps: the honest locals, and the committed score
    tallies. *)
module Validator_map = Map.Make (Validator)

(** A committed score tally: per-author support-certificate counts, the
    projection of a committed window sequence that add_score(origin, 1)
    accumulates (bullshark.rs:81-89); an absent author reads as score 0,
    mirroring the zero pre-population of ReputationScores::new
    (reputation.rs:20-28). *)
type tally = int Validator_map.t

(** The hidden commit-lag branch: which honest validator's boundary commit
    is deferred past Commit_eval. Resolved invisibly at the Commit_eval
    transition, force-repaired inside Execute (mirroring
    Tn_state.delay_choice; V0, the window's committing leader, is never the
    laggard - two lag targets already give every honest agent its view
    collision). *)
type lag = Lag_unchosen | No_lag | Lag_v1 | Lag_v2

(** Total order index for [lag]. *)
let lag_index = function
  | Lag_unchosen -> 0
  | No_lag -> 1
  | Lag_v1 -> 2
  | Lag_v2 -> 3

(** Total deterministic comparison for [lag]. *)
let lag_compare a b = Int.compare (lag_index a) (lag_index b)

(** The validator whose commit the lag branch defers, if any. *)
let lagger_of = function
  | Lag_unchosen -> None
  | No_lag -> None
  | Lag_v1 -> Some Validator.V1
  | Lag_v2 -> Some Validator.V2

(** Outcome of the per-validator replacement draws. Pristine, the shared
    leader_round-keyed seed (leader_schedule.rs:211-213) forces every
    validator's draw to coincide: only [Draws_shared] is produced. The
    [No_shared_seed] mutation deletes that shared-seed gate - each
    validator's table derivation then draws from an independent private
    RNG, so the divergent resolution [Draws_split] (V1's draw lands on V2
    while V0/V2 land on [a_good]) becomes reachable alongside the
    coincidental [Draws_shared]. *)
type draws = Draws_unresolved | Draws_shared | Draws_split

(** Total order index for [draws]. *)
let draws_index = function
  | Draws_unresolved -> 0
  | Draws_shared -> 1
  | Draws_split -> 2

(** Total deterministic comparison for [draws]. *)
let draws_compare a b = Int.compare (draws_index a) (draws_index b)

(** The phase machine: the schedule window closes (Window), each honest
    validator evaluates the boundary commit (Commit_eval, where the hidden
    lag resolves), the lagging commit is repaired and execution marks every
    local (Execute), then terminal stutter (Done). *)
type phase = Window | Commit_eval | Execute | Done

(** Total order index for [phase]. *)
let phase_index = function
  | Window -> 0
  | Commit_eval -> 1
  | Execute -> 2
  | Done -> 3

(** Total deterministic comparison for [phase]. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** Per-validator local state, the knowledge ground for K_i: [closure] is
    the accumulated score tally of the boundary window it has committed
    (empty until its own commit fires - each Bullshark instance updates its
    own table only when IT commits, bullshark.rs:333-351), [executed]
    whether the post-boundary execution step has run. Everything else in
    the global state (the lag branch, the draw resolution, peers' locals)
    is invisible to it. *)
type local = { closure : tally; executed : bool }

(** The pre-commit local. *)
let local_empty = { closure = Validator_map.empty; executed = false }

(** Total deterministic comparison for [local] over ALL fields. *)
let local_compare l1 l2 =
  let c = Validator_map.compare Int.compare l1.closure l2.closure in
  if Bool.not (Int.equal c 0) then c else Bool.compare l1.executed l2.executed

(** The global state: phase, the two hidden resolutions, the formed
    boundary window (accumulated score tally), and the honest locals. *)
type state = {
  phase : phase;
  lag : lag;
  draws : draws;
  boundary : tally;
  locals : local Validator_map.t;
}

(** Total deterministic comparison for [state] over ALL fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = lag_compare s1.lag s2.lag in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = draws_compare s1.draws s2.draws in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Validator_map.compare Int.compare s1.boundary s2.boundary in
        if Bool.not (Int.equal c3 0) then c3
        else Validator_map.compare local_compare s1.locals s2.locals

(** The ordered state module for the kernel functor. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** The ordered view module: a validator's view is its local state. *)
module View = struct
  type t = local

  let compare = local_compare
end

(** Total lookup of a validator's local; validators outside [locals]
    (V3, which the model never grants a local) read as [local_empty]. *)
let local_of state v =
  Option.fold ~none:local_empty ~some:Fun.id
    (Validator_map.find_opt v state.locals)

(** The view projection: honest validators see exactly their local state;
    V3 is not a knowledge agent, so its view is the CONSTANT empty local -
    it never appears under K / Everyone / Common in this family. *)
let view v state =
  match v with
  | Validator.V0 | Validator.V1 | Validator.V2 -> local_of state v
  | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 ->
      local_empty

(** The committed score read-back, a pure function of a committed closure
    (bullshark.rs:81-89): the accumulated support-certificate count for the
    author, absence totalized to the zero score ReputationScores::new
    pre-populates (reputation.rs:20-28). *)
let score closure v =
  Option.fold ~none:0 ~some:Fun.id (Validator_map.find_opt v closure)

(** Truncated integer square root: the value Rust's
    [(standard_dev as f64).sqrt() as u64] takes on the small exact tallies
    this model reaches (leader_schedule.rs:94). *)
let isqrt n =
  let rec grow k = if (k + 1) * (k + 1) <= n then grow (k + 1) else k in
  if n <= 0 then 0 else grow 0

(** Whether the table derived from a committed closure swaps the bad slot:
    a faithful integer transcription of the LeaderSwapTable::new dispersion
    gate (leader_schedule.rs:62-131) over the committee of four. The mean
    is the truncating u64 division of the score sum (:80-85), the standard
    deviation the truncated square root of the mean squared deviation
    (:86-94), and NO node is flagged bad when the deviation is 0 or the
    lowest reputation clears [highest - 2 * standard_dev] (:101-103).
    Otherwise the bad list collects the authorities at or under that
    2-sigma ceiling, lowering the ceiling by [standard_dev] while the list
    exceeds the threshold [max 1 (4 * bad_nodes_percent_threshold / 100)],
    which is 1 for four authorities at every threshold in [0, 33] (:66-73,
    :106-131); the slot swaps exactly when [bad_leader] lands on the bad
    list (swap, :209-230). The descending sort's tie-break
    (reputation.rs:49-68) fixes only the shared good-node order the seeded
    draw consults, never bad/good membership. An all-zero (uncommitted)
    tally truncates the deviation to 0, so no table is installed. *)
let swapped closure =
  let scores = List.map (score closure) roster in
  let n = List.length scores in
  let highest = List.fold_left Int.max 0 scores in
  let lowest = List.fold_left Int.min highest scores in
  let mean = List.fold_left ( + ) 0 scores / n in
  let sq_dev_sum =
    List.fold_left (fun acc s -> acc + ((s - mean) * (s - mean))) 0 scores
  in
  let standard_dev = isqrt (sq_dev_sum / n) in
  let list_threshold = 1 in
  let bad_ceil = Int.max 0 (highest - (2 * standard_dev)) in
  let rec bad_below ceil =
    let bad = List.filter (fun v -> score closure v <= ceil) roster in
    if List.length bad <= list_threshold then bad
    else
      let lowered = Int.max 0 (ceil - standard_dev) in
      if Int.equal lowered ceil then bad else bad_below lowered
  in
  if Int.equal standard_dev 0 || lowest > bad_ceil then false
  else List.exists (Validator.equal bad_leader) (bad_below bad_ceil)

(** Whether the validator has committed the schedule-boundary sub-dag: its
    closure is exactly the boundary's accumulated score tally once the
    commit fires, so containment is non-emptiness. *)
let boundary_committed state v =
  Bool.not (Validator_map.is_empty (local_of state v).closure)

(** DERIVED: the validator's swap table is installed with the bad slot
    swapped out - [update_leader_swap_table]'s single caller is gated on
    committing the boundary (bullshark.rs:333-351), and the window's
    accumulated 2/2/2/0 tally arms the transcribed dispersion gate. *)
let swap_installed state v = swapped (local_of state v).closure

(** The replacement node a validator's table derivation draws for the bad
    slot. [Draws_shared]: the shared leader_round-keyed seed
    (leader_schedule.rs:211-213) lands every draw on [a_good].
    [Draws_split]: the mutated independent RNGs diverge - V1 draws V2, the
    rest draw [a_good]. [Draws_unresolved] is consulted only under an empty
    closure (no pre-commit state has one); it is totalized to the shared
    pick. *)
let pick_of draws v =
  match draws with
  | Draws_unresolved -> a_good
  | Draws_shared -> a_good
  | Draws_split -> (
      match v with
      | Validator.V1 -> Validator.V2
      | Validator.V0 | Validator.V2 | Validator.V3 | Validator.V4
      | Validator.V5 | Validator.V6 | Validator.V7 | Validator.V8
      | Validator.V9 ->
          a_good)

(** DERIVED: the validator's next leader for the bad slot - the round-robin
    choice V3 (next_leader, leader_schedule.rs:285-304) unless its
    committed closure installs the swap, in which case the table lookup
    (leader_schedule.rs:253-271) returns its drawn good node. *)
let leader_next state v =
  if swapped (local_of state v).closure then pick_of state.draws v
  else bad_leader

(* --- atoms --- *)

(** The atom vocabulary - exactly what the statement quantifies over. *)
type atom =
  | Swap_installed of Validator.t
      (** the validator's derived swap table has the bad slot swapped out *)
  | Boundary_committed of Validator.t
      (** the validator has committed the schedule-boundary sub-dag *)
  | Leader_next_good of Validator.t
      (** the validator's derived next leader for the bad slot is [a_good] *)

(** Labeling function: every atom is a derived reading of the state. *)
let label a state =
  match a with
  | Swap_installed v -> swap_installed state v
  | Boundary_committed v -> boundary_committed state v
  | Leader_next_good v -> Validator.equal (leader_next state v) a_good

(** Render an atom with the surface notation used in the statement docs. *)
let atom_to_string = function
  | Swap_installed v -> "swap-installed(" ^ Validator.to_string v ^ ")"
  | Boundary_committed v -> "boundary-committed(" ^ Validator.to_string v ^ ")"
  | Leader_next_good v -> "leader-next-good(" ^ Validator.to_string v ^ ")"

(* --- mutation + transitions --- *)

(** Gate deletion for the confirm-by-mutation pin. [No_shared_seed] deletes
    the shared leader_round-keyed swap seed (leader_schedule.rs:211-213):
    each validator's replacement draw becomes an independent private
    choice, so the divergent resolution [Draws_split] is produced alongside
    [Draws_shared] at Commit_eval. Honest tables then disagree at Done even
    though every honest validator committed the SAME boundary - the Done
    state is terminal, no later step revisits the draw, so common knowledge
    of schedule agreement is refuted (not silently repaired by any sibling
    path). *)
type mutation = Pristine | No_shared_seed

(** Rebuild one validator's local through [f]. *)
let update_local v f state =
  { state with locals = Validator_map.add v (f (local_of state v)) state.locals }

(** The boundary window's accumulated score tally: two score-bearing
    commits, each supported by one certificate per honest author and none
    by [bad_leader] (add_score(origin, 1), bullshark.rs:81-89) - the
    committed tally 2/2/2/0, the smallest profile the real dispersion gate
    accepts (1/1/1/0 truncates standard_dev to 0 and is rejected,
    leader_schedule.rs:101-103). *)
let boundary_full =
  List.fold_left
    (fun acc v -> Validator_map.add v 2 acc)
    Validator_map.empty honest

(** One validator commits the boundary: its closure becomes the boundary's
    accumulated score tally (its table install is the derived consequence -
    bullshark.rs:333-351 rebuilds the table from exactly this commit). *)
let commit_one v state =
  update_local v (fun l -> { l with closure = state.boundary }) state

(** Window -> Commit_eval: the schedule window closes and the boundary
    sub-dag forms (round-keyed via the header nonce, header.rs:164-166). *)
let close_window state =
  [ { state with boundary = boundary_full; phase = Commit_eval } ]

(** Commit_eval -> Execute: the hidden lag branch resolves into ALL of
    {No_lag, Lag_v1, Lag_v2} - every honest validator except the laggard
    commits the boundary and thereby installs its swap table. Pristine, the
    shared seed forces [Draws_shared]; under [No_shared_seed] the
    independent draws also resolve into [Draws_split]. *)
let commit_eval mut state =
  let resolutions =
    match mut with
    | Pristine -> [ Draws_shared ]
    | No_shared_seed -> [ Draws_shared; Draws_split ]
  in
  List.concat_map
    (fun lag ->
      List.map
        (fun draws ->
          let committers =
            List.filter
              (fun v ->
                Bool.not
                  (Option.fold ~none:false ~some:(Validator.equal v)
                     (lagger_of lag)))
              honest
          in
          {
            (List.fold_left
               (fun acc v -> commit_one v acc)
               { state with lag; draws } committers)
            with phase = Execute;
          })
        resolutions)
    [ No_lag; Lag_v1; Lag_v2 ]

(** Execute -> Done: the lagging commit is force-repaired (the laggard
    commits the boundary closure and installs its table) BEFORE execution
    marks every honest local, so every Done state is all-swapped and the
    executed bit is what lets Done views pin the phase. *)
let execute state =
  let repaired =
    Option.fold ~none:state ~some:(fun v -> commit_one v state)
      (lagger_of state.lag)
  in
  [
    {
      (List.fold_left
         (fun acc v -> update_local v (fun l -> { l with executed = true }) acc)
         repaired honest)
      with phase = Done;
    };
  ]

(** The mutation-parameterized transition relation; Done is terminal
    (stutter-closed by the kernel). *)
let next_with mut state =
  match state.phase with
  | Window -> close_window state
  | Commit_eval -> commit_eval mut state
  | Execute -> execute state
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: window open, boundary unformed, both hidden choices
    unresolved, every honest local empty. *)
let initial =
  {
    phase = Window;
    lag = Lag_unchosen;
    draws = Draws_unresolved;
    boundary = Validator_map.empty;
    locals =
      List.fold_left
        (fun acc v -> Validator_map.add v local_empty acc)
        Validator_map.empty honest;
  }

(* --- checker instance --- *)

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The spec under a mutation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine system. *)
let make () = Checker.make spec
