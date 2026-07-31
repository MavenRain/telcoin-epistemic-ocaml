(** The reusable per-family topos gate: the evidence that a family model's
    [Checker] really is the presheaf-topos internal-logic denotation
    ({!Telcoin_epistemic.Denote}, lib/internal/DESIGN.md) and not merely
    declared to be.

    Every model in the library now instantiates its checker as
    [Denote.Make (State) (View)]. A re-point by itself proves nothing: what
    makes it meaningful is that the denotation computes what the original
    exact checker ({!Telcoin_epistemic.System}) computes, at every reachable
    world. This module packages the three per-family obligations that make
    the claim checkable, in the same shape for all 69 models:

    - {b poset}: [Frame.certify_functorial] on the family's own reachable
      graph: [⊑] reflexive, transitive and ANTISYMMETRIC (DESIGN sec.1). This
      is a CLASSIFICATION, not a precondition. 57 of the 69 frames certify;
      12 are preorders because they model mechanisms that undo themselves,
      and a preorder is still a thin category, so parallel [W]-arrows are
      still unique and presheaf restriction is still path-independent. Those
      twelve pin this case NEGATIVELY instead (each carries a
      [preorder-not-poset] case asserting [v.G.poset = false]), and the whole
      split is pinned by test/t_topos_frames.ml.
    - {b reduction}: the executable differential gate of DESIGN sec.6 gate 2,
      [is_true (grade φ s) = (s ∈ System.sat φ)] at every reachable world, for
      every subformula of every statement of the family plus a spanning
      constructor battery. This is the same gate test/t_reduction.ml runs for
      {!Telcoin_epistemic.Tn_model}, generalised so each family carries its
      own instance over its own mutants.
    - {b reflection non-vacuity}: the classical bridge ({!Reflect}) must be
      load-bearing on this family, witnessed by confirm-by-mutation:
      [grade_noreflect] (the same denotation with the bridge deleted) must
      disagree with [grade] on at least one battery formula at some world.
      Without this the reduction gate could pass for a family on which the
      intuitionistic and classical readings never diverge, which would make
      the [Not]/[Implies] arm of the denotation untested here.

    The gate runs against the model's raw spec fields rather than a built
    [Checker.t], so it instantiates both checkers itself and can never be
    handed a system built by the checker it is trying to audit. *)

open Telcoin_epistemic

(** Every subformula of [f], with [f] itself included. *)
let rec subformulas f =
  f
  ::
  (match f with
  | Formula.Atom _ | Formula.Top | Formula.Bot -> []
  | Formula.Not p
  | Formula.Ax p
  | Formula.Ex p
  | Formula.Ag p
  | Formula.Eg p
  | Formula.Af p
  | Formula.Ef p
  | Formula.K (_, p)
  | Formula.Everyone (_, p)
  | Formula.Common (_, p) ->
      subformulas p
  | Formula.And (l, r)
  | Formula.Or (l, r)
  | Formula.Implies (l, r)
  | Formula.Au (l, r)
  | Formula.Eu (l, r) ->
      subformulas l @ subformulas r)

(** Is this formula a bare atom (exhaustive, no catch-all). *)
let is_atom f =
  match f with
  | Formula.Atom _ -> true
  | Formula.Top | Formula.Bot | Formula.Not _ | Formula.Ax _ | Formula.Ex _
  | Formula.Ag _ | Formula.Eg _ | Formula.Af _ | Formula.Ef _ | Formula.K _
  | Formula.Everyone _ | Formula.Common _ | Formula.And _ | Formula.Or _
  | Formula.Implies _ | Formula.Au _ | Formula.Eu _ ->
      false

(** Up to three distinct atoms occurring in the given formulas. Lets a family
    derive its battery seeds from its own statements instead of naming atoms
    by hand; a family that wants specifically chosen contingent seeds should
    still name them explicitly, as test/t_ban_topos.ml does. *)
let seeds fs =
  List.filteri
    (fun i _ -> i < 3)
    (List.sort_uniq compare
       (List.filter is_atom (List.concat_map subformulas fs)))

(** A spanning battery over the caller's seed atoms: every {!Formula.t}
    constructor occurs at least once, including the possibility modalities
    [Ex]/[Ef]/[Eg] that no statement uses positively, the nested [Not (Ag (Not
    _))] that pins the persistence direction (DESIGN sec.0.1.2), and the
    [Not]/[Implies]-over-modal shapes on which the classical reflection is
    NOT a no-op. [atoms] should be three contingent atoms of the family (both
    truth values reachable); missing entries degrade to [Top] rather than
    raising, so a family with fewer atoms still gets a total battery. *)
let battery ~atoms ~agent ~group =
  let open Formula in
  let pick i = Option.value ~default:Top (List.nth_opt atoms i) in
  let a1 = pick 0 and a2 = pick 1 and a3 = pick 2 in
  [
    a1;
    a2;
    a3;
    Top;
    Bot;
    Not a1;
    Not a2;
    Not (Not a3);
    And (a1, a2);
    Or (a1, a2);
    Implies (a1, a2);
    Implies (a2, a3);
    Ax a1;
    Ex a1;
    Ag a1;
    Eg a1;
    Af a2;
    Ef a1;
    Au (a1, a2);
    Eu (a1, a2);
    K (agent, a1);
    Everyone (group, a1);
    Common (group, a1);
    Ag (Implies (a1, K (agent, a2)));
    Ag (Not a3);
    Not (Ag (Not a3));
    Implies (Af a2, a1);
    Implies (Ag a1, Ef a2);
    Not (Ef a3);
    Ax (Ax a2);
    Eg (Not a2);
    Ef (K (agent, a1));
    Af (Or (a1, Not a1));
    Common (group, Implies (a1, a2));
  ]

module Make (State : System.ORDERED) (View : System.ORDERED) = struct
  (** The reduction oracle: the original exact checker (lib/system.ml), kept
      per DESIGN sec.5 as the independent ground truth. *)
  module Oracle = System.Make (State) (View)

  (** The base category [W] of this family, for the poset certificate. *)
  module Fr = Frame.Make (State) (View)

  (** The denotation under audit: the very functor every family [Checker] is
      now an instance of. *)
  module Topos = Denote.Make (State) (View)

  type verdict = {
    poset : bool;  (** [Frame.certify_functorial] returned [Ok]. *)
    worlds : int;  (** [|reach|] of this model under this mutation. *)
    checked : int;  (** How many distinct formulas the reduction covered. *)
    mismatch : int option;
        (** Index into the checked formulas of the first world at which
            [is_true ∘ grade] and [System.sat] disagree; [None] is the gate
            passing. *)
    reflection_load_bearing : bool;
        (** Deleting the classical bridge changes a verdict here, so the
            [Not]/[Implies] arm of the denotation is genuinely exercised. *)
  }

  type error = Empty_init

  (** Returns [None] on agreement, or [Some index] of the first offending
      formula so a failure is diagnosable. [List.find_map] short-circuits. *)
  let first_mismatch osys dsys formulas =
    let states = Topos.states dsys in
    List.find_map
      (fun (idx, f) ->
        let g = Topos.grade dsys f in
        let osat = Oracle.sat osys f in
        let agrees s =
          Bool.equal (Topos.is_true dsys s (g s)) (Oracle.State_set.mem s osat)
        in
        if List.for_all agrees states then None else Some idx)
      (List.mapi (fun i f -> (i, f)) formulas)

  (** The confirm-by-mutation witness for {!Reflect}: does deleting the
      classical bridge flip any verdict on this family? *)
  let noreflect_differs dsys formulas =
    let states = Topos.states dsys in
    List.exists
      (fun f ->
        let g = Topos.grade dsys f in
        let gn = Topos.grade_noreflect dsys f in
        List.exists
          (fun s ->
            Bool.not
              (Bool.equal (Topos.is_true dsys s (g s))
                 (Topos.is_true dsys s (gn s))))
          states)
      formulas

  (** Run all three obligations for one spec (i.e. one model under one
      mutation). [formulas] is deduplicated structurally before checking;
      atoms are first-order, so polymorphic compare is total. *)
  let run ~init ~next ~view ~label ~formulas =
    let formulas = List.sort_uniq compare formulas in
    let ospec = { Oracle.init; next; view; label } in
    let fspec = { Fr.init; next; view; label } in
    let dspec = { Topos.init; next; view; label } in
    Result.bind
      (Result.map_error (fun Oracle.Empty_init -> Empty_init)
         (Oracle.make ospec))
      (fun osys ->
        Result.bind
          (Result.map_error (fun Fr.Empty_init -> Empty_init) (Fr.make fspec))
          (fun fsys ->
            Result.map
              (fun dsys ->
                {
                  poset =
                    Result.fold ~ok:(fun () -> true)
                      ~error:(fun _ -> false)
                      (Fr.certify_functorial fsys);
                  worlds = Topos.reachable_count dsys;
                  checked = List.length formulas;
                  mismatch = first_mismatch osys dsys formulas;
                  reflection_load_bearing = noreflect_differs dsys formulas;
                })
              (Result.map_error
                 (fun Topos.Empty_init -> Empty_init)
                 (Topos.make dspec))))
end
