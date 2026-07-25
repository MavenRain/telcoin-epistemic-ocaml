(** Finite interpreted systems and the exact CTLK model checker, plus the
    LCF-style proof kernel.

    An interpreted system is a finite transition graph over global states
    together with, for each validator, a {e view}: the projection of the
    global state onto what that validator locally possesses. [K (i, phi)]
    holds at state [s] iff [phi] holds at every reachable state with the same
    i-view - knowledge is grounded in local state, never in data the node
    does not hold.

    The checker is exact on the finite reachable graph: temporal operators by
    monotone fixpoint iteration over the powerset lattice, knowledge operators
    by partitioning the reachable set on views. The transition relation is
    made total by stutter-closing terminal states, so [Af]/[Au] are
    well-defined; consequently liveness verdicts encode whatever fairness the
    model builder baked into [next] (a model with a livelock cycle will
    honestly refute [Af]).

    [Theorem.t] is the kernel boundary: the only constructors are [prove] and
    [prove_nonvacuous], so possessing a theorem value is possession of a
    checked proof. *)

module type ORDERED = sig
  type t

  val compare : t -> t -> int
end

module Make (State : ORDERED) (View : ORDERED) : sig
  module State_set : Set.S with type elt = State.t

  type 'a spec = {
    init : State.t list;
    next : State.t -> State.t list;
    view : Validator.t -> State.t -> View.t;
    label : 'a -> State.t -> bool;
  }
  (** ['a] is the statement module's atom vocabulary. [next] may return [[]]
      for terminal states; [make] stutter-closes them. *)

  type 'a t
  (** A spec together with its precomputed reachable set. *)

  type make_error = Empty_init

  val make : 'a spec -> ('a t, make_error) result

  val reachable_count : 'a t -> int

  val sat : 'a t -> 'a Formula.t -> State_set.t
  (** The set of reachable states satisfying the formula. *)

  val valid : 'a t -> 'a Formula.t -> bool
  (** Holds at every initial state. *)

  val satisfiable : 'a t -> 'a Formula.t -> bool
  (** Holds at some reachable state - the vacuity probe. *)

  module Theorem : sig
    type 'a thm

    val formula : 'a thm -> 'a Formula.t
  end

  type proof_error =
    | Refuted of { failing_inits : int }
        (** The formula fails at this many initial states. *)
    | Vacuous_antecedent
        (** [prove_nonvacuous]: the antecedent holds at no reachable state,
            so the implication would be true for the wrong reason. *)

  val prove : 'a t -> 'a Formula.t -> ('a Theorem.thm, proof_error) result
  (** [Ok] iff [valid]: the formula holds at every initial state (for
      [Ag]-rooted formulas this is equivalence to holding everywhere
      reachable). *)

  val prove_nonvacuous :
    'a t ->
    antecedent:'a Formula.t ->
    'a Formula.t ->
    ('a Theorem.thm, proof_error) result
  (** [prove] guarded by reachability of the antecedent: refuses to certify
      an implication whose hypothesis never occurs in the model. *)
end
