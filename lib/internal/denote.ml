(** Graded denotation of {!Formula} and the LCF kernel (DESIGN sec.4). The
    Boolean [sat] recomputes [system.ml:98-136] on the bespoke internal layer;
    [grade] is the Alexandrov graded evaluator with classical reflection at
    [Not]/[Implies]. *)

module Make (State : System.ORDERED) (View : System.ORDERED) = struct
  module F = Frame.Make (State) (View)
  module Sv = Sieve.Make (F)
  module Sb = Sub.Make (F)
  module Bc = Basechange.Make (F)
  module Fx = Fix.Make (F)
  module Kn = Knows.Make (F)
  module Rf = Reflect.Make (F)

  module State_set = F.State_set

  type 'a spec = 'a F.spec = {
    init : State.t list;
    next : State.t -> State.t list;
    view : Validator.t -> State.t -> View.t;
    label : 'a -> State.t -> bool;
  }

  type 'a t = 'a F.t
  type make_error = F.build_error = Empty_init

  let make = F.make
  let reachable_count = F.reachable_count
  let reach = F.reach
  let states = F.states

  type sieve = State_set.t

  let is_true t s v = Sv.is_true t s v

  (* The Boolean satisfaction set: system.ml:98-136 on the internal layer. *)
  let rec bset t f =
    match f with
    | Formula.Atom a ->
        F.State_set.filter (fun s -> (F.spec t).label a s) (F.reach t)
    | Formula.Top -> F.reach t
    | Formula.Bot -> F.State_set.empty
    | Formula.Not p -> F.State_set.diff (F.reach t) (bset t p)
    | Formula.And (l, r) -> F.State_set.inter (bset t l) (bset t r)
    | Formula.Or (l, r) -> F.State_set.union (bset t l) (bset t r)
    | Formula.Implies (l, r) ->
        F.State_set.union (F.State_set.diff (F.reach t) (bset t l)) (bset t r)
    | Formula.Ax p -> Bc.pre_all t (bset t p)
    | Formula.Ex p -> Bc.pre_some t (bset t p)
    | Formula.Ag p ->
        let b = bset t p in
        Fx.gfp t (fun z -> F.State_set.inter b (Bc.pre_all t z))
    | Formula.Eg p ->
        let b = bset t p in
        Fx.gfp t (fun z -> F.State_set.inter b (Bc.pre_some t z))
    | Formula.Af p ->
        let b = bset t p in
        Fx.lfp t (fun z -> F.State_set.union b (Bc.pre_all t z))
    | Formula.Ef p ->
        let b = bset t p in
        Fx.lfp t (fun z -> F.State_set.union b (Bc.pre_some t z))
    | Formula.Au (l, r) ->
        let h = bset t l and g = bset t r in
        Fx.lfp t (fun z ->
            F.State_set.union g (F.State_set.inter h (Bc.pre_all t z)))
    | Formula.Eu (l, r) ->
        let h = bset t l and g = bset t r in
        Fx.lfp t (fun z ->
            F.State_set.union g (F.State_set.inter h (Bc.pre_some t z)))
    | Formula.K (v, p) -> Kn.knows t v (bset t p)
    | Formula.Everyone (g, p) -> Kn.everyone t g (bset t p)
    | Formula.Common (g, p) -> Kn.common t g (bset t p)

  let sat = bset

  (* The graded evaluator (DESIGN sec.4). [reflect] is the classical bridge
     at [Not]/[Implies]; exposing it lets the reflection non-vacuity pin swap
     in the identity. Each modal [bset] is computed once in the closure. *)
  let grade_with ~reflect t f =
    let rec g f =
      match f with
      | Formula.Atom _ ->
          let b = bset t f in
          fun s -> Sb.character t b s
      | Formula.Top -> fun s -> Sv.truth t s
      | Formula.Bot -> fun _ -> Sv.bot
      | Formula.And (l, r) ->
          let gl = g l and gr = g r in
          fun s -> Sv.meet (gl s) (gr s)
      | Formula.Or (l, r) ->
          let gl = g l and gr = g r in
          fun s -> Sv.join (gl s) (gr s)
      | Formula.Not p ->
          let gp = g p in
          fun s -> Sv.neg t s (reflect t s (gp s))
      | Formula.Implies (l, r) ->
          let gl = g l and gr = g r in
          fun s -> Sv.imp t s (reflect t s (gl s)) (gr s)
      | Formula.Ag _ ->
          (* AG's native graded Sub(1_E) reading (DESIGN sec.1, sec.2). *)
          let b = bset t f in
          fun s -> Sb.character t b s
      | Formula.Ax _ | Formula.Ex _ | Formula.Eg _ | Formula.Af _
      | Formula.Ef _ | Formula.Au _ | Formula.Eu _ | Formula.K _
      | Formula.Everyone _ | Formula.Common _ ->
          (* The modal fragment is valued in B (DESIGN sec.2, sec.3): a
             two-valued injection of the Boolean truth into Ω(s). *)
          let b = bset t f in
          fun s -> if F.State_set.mem s b then Sv.truth t s else Sv.bot
    in
    g f

  let grade t f = grade_with ~reflect:(fun tt s v -> Rf.classical tt s v) t f
  let grade_noreflect t f = grade_with ~reflect:(fun _ _ v -> v) t f
  let holds_at t f s = is_true t s (grade t f s)

  let failing_inits t f =
    let holds = grade t f in
    List.length
      (List.filter (fun s -> Bool.not (is_true t s (holds s))) (F.spec t).init)

  let valid t f = Int.equal (failing_inits t f) 0

  let satisfiable t f =
    let holds = grade t f in
    List.exists (fun s -> is_true t s (holds s)) (F.states t)

  module Theorem = struct
    type 'a thm = { thm_formula : 'a Formula.t }

    let formula t = t.thm_formula
  end

  type proof_error =
    | Refuted of { failing_inits : int }
    | Vacuous_antecedent

  let prove t f =
    let failures = failing_inits t f in
    if Int.equal failures 0 then Ok { Theorem.thm_formula = f }
    else Error (Refuted { failing_inits = failures })

  let prove_nonvacuous t ~antecedent goal =
    if satisfiable t antecedent then prove t goal
    else Error Vacuous_antecedent
end
