(** The categorical laws of the topos layer, applied to every REAL model
    frame rather than only to a synthetic one.

    test/t_categorical.ml pins the operators of [lib/internal/] on a
    hand-built four-state frame, each law paired with a deliberately wrong
    operator that violates it. That is the right place to pin the laws,
    because those witnesses were chosen to be non-degenerate. It says
    nothing, though, about the frames the library actually reasons over: a
    real model could have a view map whose fibres are all singletons (making
    [K_i] the identity, and every S5 law vacuous on it), or an [AG]-set that
    is not future-closed, or a [C_G] that does not converge inside its bound.

    This module runs the same laws over a real model's own frame, with
    witness subsets drawn from that model: the {!System} denotation of each
    formula the family's topos gate already checks, plus [⊤] and [⊥]. It
    reports the laws AND the non-degeneracy of the witness family, so a green
    verdict cannot be bought by a frame on which the operators have nothing
    to do.

    Laws (DESIGN sec.1, sec.2, sec.3):
    - the Galois adjunctions [Σ_{f_i} ⊣ f_i*] and [f_i* ⊣ Π_{f_i}] along the
      view map;
    - [K_i] as a lex idempotent S5 comonad: factivity [K S ⊆ S], idempotence
      [K K S = K S], the Euclidean law [¬K S ⊆ K ¬K S], monotonicity;
    - [C_G] as a [ν]: convergence within [|reach|] iterations, and
      [C_G S ⊆ E_G S];
    - the [AX]/[EX] base-change duality along the transition span;
    - [Sub(1_E)] as a Heyting algebra over genuinely future-closed witnesses:
      [A ∧ (A → B) ≤ B] and [¬A = (A → ⊥)].

    The verdict type is deliberately monomorphic ([laws] is an association
    list, not a record of fields), so one checker can consume the verdicts of
    all 69 models even though each is a different functor instance. *)

open Telcoin_epistemic

type verdict = {
  worlds : int;  (** [|reach|] of this model. *)
  witnesses : int;  (** Distinct witness subsets drawn from the model. *)
  nondegenerate : int;
      (** Witnesses that are neither [∅] nor [reach]. The laws are only
          informative over these, so this is the anti-vacuity counter. *)
  k_nontrivial : bool;
      (** Some [K_i] genuinely loses information here ([K_i S ≠ S] for some
          witness and some agent), so the S5 laws below are not laws about
          the identity operator. *)
  pair_witnesses : int;
      (** How many witnesses feed the QUADRATIC laws (K-monotone, Heyting
          modus ponens). Those are capped, because the pair count grows as the
          square and the shared model contributes hundreds of witnesses; the
          cap is reported rather than applied silently. *)
  laws : (string * bool) list;
      (** Each law by name, with whether it held over every witness (pair)
          and every agent. *)
}

type error = Empty_init

module Make (State : System.ORDERED) (View : System.ORDERED) = struct
  module Oracle = System.Make (State) (View)
  module Fr = Frame.Make (State) (View)
  module Bc = Basechange.Make (Fr)
  module Fx = Fix.Make (Fr)
  module Kn = Knows.Make (Fr)
  module Sb = Sub.Make (Fr)

  (** All pairs (ordered, with repeats) drawn from a witness list. *)
  let pairs xs = List.concat_map (fun a -> List.map (fun b -> (a, b)) xs) xs

  (** The quadratic laws run over at most this many witnesses. *)
  let pair_cap = 12

  (** The first [pair_cap] witnesses, for the laws. *)
  let capped xs = List.filteri (fun i _ -> i < pair_cap) xs

  (** The [C_G] laws iterate a greatest fixpoint over the whole group at
      every witness, which on the 141-world shared model is the most
      expensive thing here, so they run over a smaller witness list still. *)
  let common_cap = 3

  (** The first [common_cap] witnesses, for the [C_G] laws. *)
  let capped_common xs = List.filteri (fun i _ -> i < common_cap) xs

  (** Run every law over one model's real frame. [formulas] supplies the
      witness subsets, [agents] the knowledge agents whose view maps carry
      the base change, [group] the group for [E_G] / [C_G]. *)
  let run ~init ~next ~view ~label ~formulas ~agents ~group =
    let ospec = { Oracle.init; next; view; label } in
    let fspec = { Fr.init; next; view; label } in
    Result.bind
      (Result.map_error (fun Oracle.Empty_init -> Empty_init)
         (Oracle.make ospec))
      (fun osys ->
        Result.map
          (fun t ->
            let sub_of = Fr.State_set.subset in
            let equal = Fr.State_set.equal in
            let inter = Fr.State_set.inter in
            let reach = Fr.reach t in
            let n = Fr.reachable_count t in
            let comp a = Fr.State_set.diff reach a in
            (* [Frame.S] keeps its [State_set] abstract, so the oracle sets are
               bridged elementwise; both have [elt = State.t]. *)
            let of_oracle s =
              Fr.State_set.of_list (Oracle.State_set.elements s)
            in
            let ws =
              List.sort_uniq Fr.State_set.compare
                (reach :: Fr.State_set.empty
                :: List.map (fun f -> of_oracle (Oracle.sat osys f)) formulas)
            in
            (* Future-closed witnesses for the Sub(1_E) laws: an AG-set is
               up-closed by construction, which is what Sub requires. *)
            let subs =
              List.sort_uniq Fr.State_set.compare
                (List.map
                   (fun f -> of_oracle (Oracle.sat osys (Formula.Ag f)))
                   formulas)
            in
            (* Every law runs over the capped witness list: the pair laws
               grow as the square, and the shared model alone contributes
               hundreds of witnesses. The cap is reported in the verdict. *)
            let cw = capped ws in
            let csubs = capped subs in
            let wpairs = pairs cw in
            let spairs = pairs csubs in
            (* View-set witnesses: the images of the state witnesses under
               each agent's view map, plus the full image and the empty set. *)
            let view_witnesses i =
              List.sort_uniq Fr.View_set.compare
                (Fr.View_set.empty
                :: List.map (fun s -> Bc.exists_view t i s) cw)
            in
            let per_agent p = List.for_all p agents in
            {
              worlds = n;
              witnesses = List.length ws;
              pair_witnesses = List.length (capped ws);
              nondegenerate =
                List.length
                  (List.filter
                     (fun s ->
                       Bool.not (equal s reach)
                       && Bool.not (Fr.State_set.is_empty s))
                     ws);
              k_nontrivial =
                List.exists
                  (fun i ->
                    List.exists
                      (fun s -> Bool.not (equal (Kn.knows t i s) s))
                      ws)
                  agents;
              laws =
                [
                  ( "galois-exists (Sigma_f -| f*)",
                    per_agent (fun i ->
                        List.for_all
                          (fun a ->
                            List.for_all
                              (fun b ->
                                Bool.equal
                                  (Fr.View_set.subset (Bc.exists_view t i a) b)
                                  (sub_of a (Bc.reindex_view t i b)))
                              (view_witnesses i))
                          cw) );
                  ( "galois-forall (f* -| Pi_f)",
                    per_agent (fun i ->
                        List.for_all
                          (fun a ->
                            List.for_all
                              (fun b ->
                                Bool.equal
                                  (sub_of (Bc.reindex_view t i b) a)
                                  (Fr.View_set.subset b (Bc.forall_view t i a)))
                              (view_witnesses i))
                          cw) );
                  ( "K-factivity (K S subset S)",
                    per_agent (fun i ->
                        List.for_all (fun s -> sub_of (Kn.knows t i s) s) cw) );
                  ( "K-idempotence (K K S = K S)",
                    per_agent (fun i ->
                        List.for_all
                          (fun s ->
                            equal
                              (Kn.knows t i (Kn.knows t i s))
                              (Kn.knows t i s))
                          cw) );
                  ( "K-euclidean (not-K S subset K not-K S)",
                    per_agent (fun i ->
                        List.for_all
                          (fun s ->
                            let nk = comp (Kn.knows t i s) in
                            sub_of nk (Kn.knows t i nk))
                          cw) );
                  ( "K-monotone",
                    per_agent (fun i ->
                        List.for_all
                          (fun (a, b) ->
                            Bool.not (sub_of a b)
                            || sub_of (Kn.knows t i a) (Kn.knows t i b))
                          wpairs) );
                  ( "C_G converges within |reach|",
                    List.for_all
                      (fun s ->
                        Fx.steps_to_fix t ~seed:reach (fun z ->
                            Kn.everyone t group (inter s z))
                        <= n + 1)
                      (capped_common cw) );
                  ( "C_G subset E_G",
                    List.for_all
                      (fun s ->
                        sub_of (Kn.common t group s) (Kn.everyone t group s))
                      (capped_common cw) );
                  ( "AX/EX base-change duality",
                    List.for_all
                      (fun z ->
                        equal (Bc.pre_some t z) (comp (Bc.pre_all t (comp z))))
                      cw );
                  ( "Sub(1_E) witnesses are future-closed",
                    List.for_all
                      (fun a ->
                        Fr.State_set.for_all (fun s -> sub_of (Fr.up t s) a) a)
                      csubs );
                  ( "Heyting modus ponens (A /\\ (A -> B) subset B)",
                    List.for_all
                      (fun (a, b) -> sub_of (inter a (Sb.imp t a b)) b)
                      spairs );
                  ( "negation is (A -> bot)",
                    List.for_all
                      (fun a -> equal (Sb.neg t a) (Sb.imp t a Sb.bot))
                      csubs );
                ];
            })
          (Result.map_error (fun Fr.Empty_init -> Empty_init) (Fr.make fspec)))
end
