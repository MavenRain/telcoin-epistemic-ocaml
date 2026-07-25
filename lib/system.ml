module type ORDERED = sig
  type t

  val compare : t -> t -> int
end

module Make (State : ORDERED) (View : ORDERED) = struct
  module State_set = Set.Make (State)
  module View_map = Map.Make (View)

  type 'a spec = {
    init : State.t list;
    next : State.t -> State.t list;
    view : Validator.t -> State.t -> View.t;
    label : 'a -> State.t -> bool;
  }

  type 'a t = { spec : 'a spec; reach : State_set.t }

  type make_error = Empty_init

  (* Totalize: a terminal state stutters, so every path is infinite and
     Af/Au have their standard fixpoint semantics. *)
  let step spec s =
    match spec.next s with [] -> [ s ] | _ :: _ as succs -> succs

  let reachable spec =
    let rec go frontier seen =
      match frontier with
      | [] -> seen
      | s :: rest ->
          let fresh =
            List.filter
              (fun s' -> Bool.not (State_set.mem s' seen))
              (step spec s)
          in
          go
            (List.rev_append fresh rest)
            (List.fold_left (fun acc s' -> State_set.add s' acc) seen fresh)
    in
    go spec.init (State_set.of_list spec.init)

  let make spec =
    match spec.init with
    | [] -> Error Empty_init
    | _ :: _ -> Ok { spec; reach = reachable spec }

  let reachable_count sys = State_set.cardinal sys.reach

  (* Monotone fixpoint over the finite powerset lattice. *)
  let rec fix f z =
    let z' = f z in
    if State_set.equal z z' then z else fix f z'

  (* pre_all z = states ALL of whose successors lie in z;
     pre_some z = states with SOME successor in z. *)
  let pre_all sys z =
    State_set.filter
      (fun s -> List.for_all (fun s' -> State_set.mem s' z) (step sys.spec s))
      sys.reach

  let pre_some sys z =
    State_set.filter
      (fun s -> List.exists (fun s' -> State_set.mem s' z) (step sys.spec s))
      sys.reach

  (* Partition the reachable set into i-view equivalence classes; a state
     satisfies K_i phi iff its whole class does. *)
  let knows sys v phi_set =
    let classes =
      State_set.fold
        (fun s acc ->
          let key = sys.spec.view v s in
          View_map.update key
            (fun prior ->
              Option.some
                (Option.fold ~none:(State_set.singleton s)
                   ~some:(State_set.add s) prior))
            acc)
        sys.reach View_map.empty
    in
    State_set.filter
      (fun s ->
        Option.fold ~none:false
          ~some:(fun cls -> State_set.subset cls phi_set)
          (View_map.find_opt (sys.spec.view v s) classes))
      sys.reach

  let everyone sys g phi_set =
    List.fold_left
      (fun acc v -> State_set.inter acc (knows sys v phi_set))
      sys.reach g

  (* C_G phi = gfp (fun z -> E_G (phi /\ z)). *)
  let common sys g phi_set =
    fix (fun z -> everyone sys g (State_set.inter phi_set z)) sys.reach

  let rec sat sys f =
    match f with
    | Formula.Atom a -> State_set.filter (sys.spec.label a) sys.reach
    | Formula.Top -> sys.reach
    | Formula.Bot -> State_set.empty
    | Formula.Not p -> State_set.diff sys.reach (sat sys p)
    | Formula.And (l, r) -> State_set.inter (sat sys l) (sat sys r)
    | Formula.Or (l, r) -> State_set.union (sat sys l) (sat sys r)
    | Formula.Implies (l, r) ->
        State_set.union (State_set.diff sys.reach (sat sys l)) (sat sys r)
    | Formula.Ax p -> pre_all sys (sat sys p)
    | Formula.Ex p -> pre_some sys (sat sys p)
    | Formula.Ag p ->
        let base = sat sys p in
        fix (fun z -> State_set.inter base (pre_all sys z)) sys.reach
    | Formula.Eg p ->
        let base = sat sys p in
        fix (fun z -> State_set.inter base (pre_some sys z)) sys.reach
    | Formula.Af p ->
        let base = sat sys p in
        fix (fun z -> State_set.union base (pre_all sys z)) State_set.empty
    | Formula.Ef p ->
        let base = sat sys p in
        fix (fun z -> State_set.union base (pre_some sys z)) State_set.empty
    | Formula.Au (l, r) ->
        let hold = sat sys l and goal = sat sys r in
        fix
          (fun z ->
            State_set.union goal (State_set.inter hold (pre_all sys z)))
          State_set.empty
    | Formula.Eu (l, r) ->
        let hold = sat sys l and goal = sat sys r in
        fix
          (fun z ->
            State_set.union goal (State_set.inter hold (pre_some sys z)))
          State_set.empty
    | Formula.K (v, p) -> knows sys v (sat sys p)
    | Formula.Everyone (g, p) -> everyone sys g (sat sys p)
    | Formula.Common (g, p) -> common sys g (sat sys p)

  let failing_inits sys f =
    let holds = sat sys f in
    List.length
      (List.filter
         (fun s -> Bool.not (State_set.mem s holds))
         sys.spec.init)

  let valid sys f = Int.equal (failing_inits sys f) 0

  let satisfiable sys f = Bool.not (State_set.is_empty (sat sys f))

  module Theorem = struct
    type 'a thm = { thm_formula : 'a Formula.t }

    let formula t = t.thm_formula
  end

  type proof_error =
    | Refuted of { failing_inits : int }
    | Vacuous_antecedent

  let prove sys f =
    let failures = failing_inits sys f in
    if Int.equal failures 0 then Ok { Theorem.thm_formula = f }
    else Error (Refuted { failing_inits = failures })

  let prove_nonvacuous sys ~antecedent goal =
    if satisfiable sys antecedent then prove sys goal
    else Error Vacuous_antecedent
end
