(** The classical (¬¬-)reflection bridge from the intuitionistic [Ω] to the
    Boolean base [B] (DESIGN sec.4; [temporal/temporal_eval.ml:29-30]
    analogue).

    Applied to the [Ω]-value of the argument during per-world graded
    evaluation, at every [Not] node and at BOTH arguments of every [Implies].
    Reflecting only the antecedent is not enough: [Sub.imp] would then read
    [p -> q] at [s] as "if p at s then q at every world of [↑s]", which is the
    classical reading only when [q] denotes a future-closed set. That holds for
    every atom of the shared model and fails on family models whose atoms can
    go false again (DESIGN sec.4 correction). This is
    the standard classical/[is_true]-reflection: a NO-OP on a two-valued
    argument (so it coincides with the Heyting operation on the crisp fragment
    of DESIGN sec.0.1.3), and it gives the correct classical reading on a
    genuinely sieve-graded modal argument. It is NOT [¬¬] (which reflects the
    wrong way) and NOT a subobject-level operator (which would be a no-op on
    persistent atoms). *)

module Make (F : Frame.S) : sig
  val classical : 'a F.t -> F.state -> F.State_set.t -> F.State_set.t
  (** [classical v = if is_true v then ⊤ else ⊥] at the world [s], i.e.
      [↑s] when [s ∈ v] and [∅] otherwise (DESIGN sec.4). *)
end
