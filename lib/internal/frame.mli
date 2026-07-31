(** The base category [W] and the reachability skeleton of the presheaf topos
    [E = \[W^op, Set\]] (DESIGN sec.1).

    [W = (reach, ⊑)] with [⊑] the REVERSED reachability order: a [W]-arrow
    [t → s] exists iff [s →* t], so presheaf restriction over [W^op] runs
    past→future and [Sub(1_E)] is the FUTURE-closed (⊑-up-closed) subsets of
    [reach]. This is the opposite of the topos of trees, where truth decays
    forward; here invariants must PERSIST forward (DESIGN sec.0.1.2).

    The states, one-step span and reachable set mirror {!System} exactly
    ([system.ml:24-46]); [Frame] reuses [System]'s spec and set types so a
    single spec value drives both the bespoke checker and the reduction
    oracle. *)

module type S = sig
  type state
  type view

  module State_set : Set.S with type elt = state
  module View_set : Set.S with type elt = view

  type 'a spec = {
    init : state list;
    next : state -> state list;
    view : Validator.t -> state -> view;
    label : 'a -> state -> bool;
  }
  (** Same shape as {!System.Make.spec}: [init] states, transition [next]
      (terminals stutter-close), per-validator [view] projection (the ground
      for [K_i]), and the atom [label]. *)

  type 'a t
  (** A spec together with the precomputed reachable set and the reflexive
      transitive closure [↑] of the one-step relation. *)

  type build_error = Empty_init

  val make : 'a spec -> ('a t, build_error) result
  (** Build [W]: compute [reach] by the [system.ml:27-41] worklist and the
      future cones [↑s] by per-state closure. *)

  val spec : 'a t -> 'a spec
  (** The originating [System]-shaped spec (init/next/view/label) of [W]. *)

  val reach : 'a t -> State_set.t
  (** The objects of [W]: the reachable global states ([system.ml:27-46]). *)

  val states : 'a t -> state list
  (** [reach] as a list, for iteration. *)

  val reachable_count : 'a t -> int
  (** [|reach|], the number of objects of [W]. *)

  val mem : 'a t -> state -> bool
  (** Is the state reachable (an object of [W]). *)

  val step : 'a t -> state -> state list
  (** The one-step span [N] successors, terminals stutter-closed
      ([system.ml:24-25]); carried independently of [⊑] (DESIGN sec.1). *)

  val leq : 'a t -> state -> state -> bool
  (** [leq t s u]: [s ⊑ u], i.e. [u] is reachable from [s] (future). The
      order of [W] reversed from reachability - a partial order on the 57
      poset models, a preorder on the 12 whose reachability has a genuine
      cycle (DESIGN sec.1). *)

  val up : 'a t -> state -> State_set.t
  (** [↑s = {u | s ⊑ u}], the finite future cone; the carrier of [Ω(s)]
      (DESIGN sec.1, [omega_val] linear analogue's [{n,n+1,…}]). *)

  val view_of : 'a t -> Validator.t -> state -> view
  (** [f_i(s) = local_of s i] ([tn_model.ml:567]): the projection onto
      validator [i]'s local state. *)

  val fibre : 'a t -> Validator.t -> state -> State_set.t
  (** The [~_i]-equivalence class of [s]: reachable states with the same
      [i]-view (the kernel of [f_i], DESIGN sec.3). *)

  type 'x obj = {
    sections : state -> 'x list;
    restrict : state -> state -> 'x -> 'x;
  }
  (** A [W^op]-presheaf presented by its sections and restriction along
      [s ⊑ s'] (branching analogue of [temporal/trees.ml:5]). *)

  val terminal : 'a t -> unit obj
  (** [1_E]: [sections s = \[()\]] (DESIGN sec.1). *)

  val certify_functorial : 'a t -> unit Comp_cat.Res.t
  (** The [temporal/trees.ml:13] [commutes ~upto] analogue: certifies that
      [⊑] is a genuine finite poset (reflexive, transitive and
      antisymmetric), so all parallel [W]-arrows are equal and every
      presheaf's restriction is path-independent.
      [Comp_cat.Err.Not_universal] if it is not. *)
end

module Make (State : System.ORDERED) (View : System.ORDERED) :
  S with type state = State.t and type view = View.t
