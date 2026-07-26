(** The sieve-graded subobject classifier [Ω] of the presheaf topos
    [E = \[W^op, Set\]] (DESIGN sec.1), built BY HAND (comp-cat's
    [omega_via_ran]/[power]/[exists] are [Err.Unsupported],
    [subobject.ml:310/275/288]).

    [Ω(s)] is the set of sieves on [s] in [W] = the future-closed subsets of
    the finite cone [↑s]. This is the branching generalization of
    [temporal/omega_val.ml]'s linear validity-depth chain (there a sieve is a
    truncation depth [{n,n+1,…}]; here it is an arbitrary up-set of [↑s]).
    The Heyting operations are the Alexandrov ones. *)

module Make (F : Frame.S) : sig
  type sieve = F.State_set.t
  (** An element of [Ω(s)]: a future-closed subset of [↑s]. *)

  val truth : 'a F.t -> F.state -> sieve
  (** [⊤ = ↑s], the maximal sieve ([omega_val.top] analogue;
      [temporal/trees_omega.ml:14] [truth]). *)

  val bot : sieve
  (** [⊥ = ∅], the empty sieve ([omega_val.bot]). *)

  val meet : sieve -> sieve -> sieve
  (** [σ ∧ τ = σ ∩ τ] (Alexandrov meet, [omega_val.meet]). *)

  val join : sieve -> sieve -> sieve
  (** [σ ∨ τ = σ ∪ τ] (the only presheaf cover on [W] is maximal, so join is
      pointwise union, [omega_val.join]). *)

  val imp : 'a F.t -> F.state -> sieve -> sieve -> sieve
  (** [σ → τ = {t ∈ ↑s | ∀ u ⊒ t, u ∈ σ ⟹ u ∈ τ}], the Heyting residual
      ([omega_val.imp] / [temporal/trees_omega.ml:42] analogue). *)

  val neg : 'a F.t -> F.state -> sieve -> sieve
  (** [¬σ = (σ → ⊥) = {t ∈ ↑s | ↑t ∩ σ = ∅}] ([omega_val.neg]). *)

  val is_true : 'a F.t -> F.state -> sieve -> bool
  (** [is_true σ ⟺ σ = ↑s] (DESIGN sec.1). For a genuine sieve on [s] this is
      exactly [s ∈ σ] (the minimum of [↑s] belongs iff the up-set is all of
      [↑s]); it is the bounded-lattice + normal-modal homomorphism
      [Ω → bool] of the reduction theorem (DESIGN sec.0.1.3). *)
end
