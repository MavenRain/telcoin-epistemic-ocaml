(** The graded denotation of {!Formula} in the presheaf topos, and the LCF
    proof kernel (DESIGN sec.4). This is the new checker boundary: it exposes
    the SAME interface as {!System.Make} (so a model module re-points at it by
    changing one line, with no change to the statement or test wiring) plus
    the topos-internal graded surface.

    ALL 27 models in the library are instances of this functor, and each is
    differentially gated against {!System} at every reachable world:
    test/t_reduction.ml for the shared model, test/t_<family>_topos.ml for
    each family.

    [grade φ s ∈ Ω(s)] is the bottom-up Alexandrov evaluation; [Not] and both
    arguments of [Implies] carry the classical {!Reflect} bridge; the temporal and
    epistemic fragments read the Boolean base [B] ({!Basechange}, {!Fix},
    {!Knows}); [AG] additionally exposes its native graded [Sub(1_E)] reading.
    By the reduction theorem (DESIGN sec.0.1.3) [is_true (grade φ s) =
    (s ∈ sat φ)] for the {!System} [sat], so [valid]/[prove] agree with the
    original kernel operator-by-operator. *)

module Make (State : System.ORDERED) (View : System.ORDERED) : sig
  module State_set : Set.S with type elt = State.t

  type 'a spec = {
    init : State.t list;
    next : State.t -> State.t list;
    view : Validator.t -> State.t -> View.t;
    label : 'a -> State.t -> bool;
  }
  (** Same shape as {!System.Make.spec}. *)

  type 'a t

  type make_error = Empty_init

  val make : 'a spec -> ('a t, make_error) result
  (** Build the checker over [W] ({!Frame.make}); [Empty_init] if [init = []]. *)

  val reachable_count : 'a t -> int
  (** [|reach|] ({!Frame.reachable_count}). *)

  val reach : 'a t -> State_set.t
  (** The objects of [W] ({!Frame}); the reachable states. *)

  val states : 'a t -> State.t list
  (** [reach] as a list, for iteration ({!Frame.states}). *)

  val sat : 'a t -> 'a Formula.t -> State_set.t
  (** The Boolean satisfaction set [{s | is_true (grade φ s)}], computed in
      [B] exactly as [system.ml:98-136]. *)

  val valid : 'a t -> 'a Formula.t -> bool
  (** [valid_E φ := is_true (grade φ w0)] at every initial world (DESIGN
      sec.4); equals [System.valid]. *)

  val satisfiable : 'a t -> 'a Formula.t -> bool
  (** Holds at some reachable state — the vacuity probe. *)

  type sieve = State_set.t
  (** An [Ω(s)]-value; a future-closed subset of [↑s]. *)

  val grade : 'a t -> 'a Formula.t -> State.t -> sieve
  (** The graded evaluator [grade : Formula.t → state → Ω] WITH the classical
      reflection (DESIGN sec.4). Partially apply [grade t f] to build the
      bottom-up closure once and reuse it across worlds. *)

  val grade_noreflect : 'a t -> 'a Formula.t -> State.t -> sieve
  (** [grade] with the {!Reflect} classical bridge DELETED (reflection
      replaced by the identity) — the confirm-by-mutation witness of the
      reflection non-vacuity probe (DESIGN sec.6 gate 3). *)

  val is_true : 'a t -> State.t -> sieve -> bool
  (** [is_true σ ⟺ σ = ↑s] ({!Sieve}); the [Ω → bool] homomorphism. *)

  val holds_at : 'a t -> 'a Formula.t -> State.t -> bool
  (** [is_true (grade φ s)]; the left-hand side of the reduction gate
      (DESIGN sec.6 gate 2). *)

  module Theorem : sig
    type 'a thm

    val formula : 'a thm -> 'a Formula.t
    (** The formula a theorem certifies (the LCF boundary, DESIGN sec.4). *)
  end

  type proof_error =
    | Refuted of { failing_inits : int }
    | Vacuous_antecedent

  val prove : 'a t -> 'a Formula.t -> ('a Theorem.thm, proof_error) result
  (** [Ok] iff [valid]; the only theorem constructor besides
      [prove_nonvacuous] (LCF boundary). *)

  val prove_nonvacuous :
    'a t ->
    antecedent:'a Formula.t ->
    'a Formula.t ->
    ('a Theorem.thm, proof_error) result
  (** [prove] guarded by reachability of the antecedent. *)
end
