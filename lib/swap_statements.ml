(** The leader-swap-schedule family over the {!Swap_model} interpreted
    system (DESIGN family CONSENSUS-EXT #12). Mined from telcoin-network,
    adversarially verified against the code (grounding) and against the
    finite-model semantics (encodability), and stated in the form that
    survived both skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    Reading guide: the epistemic content lives entirely in the common-
    knowledge conjunct. A validator installs its swapped [LeaderSwapTable]
    from its OWN committed boundary sub-dag with no broadcast
    (crates/consensus/primary/src/consensus/bullshark.rs:333-351), so a
    peer's table state is a hidden fact. Because the shared draw seed is
    keyed only by [leader_round] (leader_schedule.rs:211-213), every honest
    validator that commits the same boundary derives the SAME swapped
    schedule - but a lagging peer whose commit is deferred still holds an
    un-swapped table invisibly, so at the No_lag Execute state the operand
    "every honest next-leader is [a_good]" is true while no honest validator
    can yet exclude the lag branches. Common knowledge of schedule
    agreement is therefore contingent, first attained at Done, and would
    collapse to plain truth were the operand extensionally local - which the
    hidden lag branch is exactly what prevents. *)

open Swap_model

(** A statement over the swap model: name, bucket (the shared vocabulary
    from {!Statements}), formula, and the reachability witness required by
    [prove_nonvacuous] - the proof is refused if the antecedent never
    holds, so no statement is certified on the strength of a false
    antecedent. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S12 - leader-swap-schedule-agreement-from-committed-scores [fairness].
    Two conjuncts. (1) A non-epistemic install invariant: a validator's
    swap table is installed exactly when it has committed the schedule-
    boundary sub-dag - AG(swap_installed_i <-> boundary_committed_i) for
    every honest i - because [update_leader_swap_table]'s single caller is
    gated on committing the boundary (bullshark.rs:333-351) and this
    window's accumulated 2/2/2/0 score tally (add_score per supporting
    certificate, bullshark.rs:81-89) arms the integer 2-sigma dispersion
    gate transcribed in {!Swap_model.swapped} (LeaderSwapTable::new,
    leader_schedule.rs:62-131; a multiplicity-1 window would truncate
    standard_dev to 0 and install nothing); the [<->] is encoded as the
    pair of implications.
    (2) The common-knowledge payoff: once every honest validator has
    installed its swap table, the honest committee attains common knowledge
    that every honest next-leader for the bad slot is [a_good] -
    (all swap_installed) ~> C_honest(all leader_next_j = a_good) - because
    the replacement draw is seeded only by [leader_round]
    (leader_schedule.rs:211-213), so the round-robin table lookup
    (leader_schedule.rs:253-271, next_leader leader_schedule.rs:285-304)
    resolves identically for every validator on the same committed
    boundary (round-keyed via the header nonce, header.rs:164-166).

    The C-operand is the explicit conjunction over ALL honest validators'
    per-validator derived [Leader_next_good] atoms, never the knower's own
    atom alone: a self-conjunct would be i-local and collapse. Common
    knowledge is first attained at Done, where every honest local is
    committed-and-executed; before Done the No_lag Execute state has the
    operand TRUE yet not even [Everyone] holds, since an honest validator's
    committed-but-not-executed view cannot exclude a lag branch in which a
    peer's table is still un-swapped. Mutation pin:
    {!Swap_model.No_shared_seed} deletes the shared draw seed - each
    validator's replacement becomes an independent hidden choice, honest
    tables disagree at Done even on the same committed boundary, and the
    common-knowledge conjunct is refuted. *)
let s12 =
  let iff a b = Formula.And (Formula.Implies (a, b), Formula.Implies (b, a)) in
  let install_invariant =
    Formula.conj
      (List.map
         (fun i -> iff (atom (Swap_installed i)) (atom (Boundary_committed i)))
         honest)
  in
  let all_swapped =
    Formula.conj (List.map (fun i -> atom (Swap_installed i)) honest)
  in
  let all_leader_good =
    Formula.conj (List.map (fun j -> atom (Leader_next_good j)) honest)
  in
  {
    name = "leader-swap-schedule-agreement-from-committed-scores";
    bucket = Statements.Fairness;
    formula =
      Formula.And
        ( Formula.Ag install_invariant,
          Formula.leads_to all_swapped
            (Formula.Common (honest, all_leader_good)) );
    antecedent = all_swapped;
  }

(** All statements of this family. *)
let all = [ s12 ]

(** Prove one statement on a system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every statement of the family, pairing each with its outcome. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** The uniform cross-model projection for the meta-tests: build the
    pristine system and report per-statement proved flags; a [make] error
    maps every row to [proved = false]. *)
let reports () =
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, outcome) ->
          {
            Report.name = st.name;
            bucket = st.bucket;
            proved =
              Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) outcome;
          })
        (prove_all sys))
    ~error:(fun Checker.Empty_init ->
      List.map
        (fun st -> { Report.name = st.name; bucket = st.bucket; proved = false })
        all)
    (make ())
