(** [Sub(1_E)], the Heyting algebra of subobjects of the terminal in
    [E = \[W^op, Set\]] (DESIGN sec.1), built BY HAND. Its elements are the
    future-closed (⊑-up-closed) subsets of [reach], ordered by [⊆]; this is
    the object-level companion of the per-world {!Sieve} (the
    [temporal/trees_omega.ml:17] [sub] analogue over the branching base).

    [AG] and all invariant content are NATIVE subobjects here (DESIGN
    sec.0.1.2); general formulas do NOT all live in [Sub(1_E)] (e.g.
    [Not At_done] is past-closed) and are read in the Boolean base [B]
    ({!Basechange}). *)

module Make (F : Frame.S) : sig
  type sub = F.State_set.t
  (** A future-closed subset of [reach]. *)

  val top : 'a F.t -> sub
  (** [⊤ = reach] ([system.ml:102]). *)

  val bot : sub
  (** [⊥ = ∅] ([system.ml:103]). *)

  val of_pred : 'a F.t -> (F.state -> bool) -> sub
  (** [{s ∈ reach | p s}] — the denotation of a monotone atom ([system.ml:100]);
      all 18 [tn_model] atoms denote genuine up-sets ([label] monotone). *)

  val meet : sub -> sub -> sub
  (** [A ∧ B = A ∩ B] ([system.ml:104]). *)

  val join : sub -> sub -> sub
  (** [A ∨ B = A ∪ B]; the only presheaf cover is maximal so join is pointwise
      union, matching [system.ml:105] (NO reflection). *)

  val imp : 'a F.t -> sub -> sub -> sub
  (** [A → B = {s | ∀ t ⊒ s, t ∈ A ⟹ t ∈ B}], the Alexandrov
      future-hereditary implication (DESIGN sec.1). *)

  val neg : 'a F.t -> sub -> sub
  (** [¬A = {s | ↑s ∩ A = ∅}] (DESIGN sec.1). *)

  val equal : sub -> sub -> bool
  (** Equality of subobjects in [Sub(1_E)] (extensional on the underlying
      future-closed sets; ⊆-antisymmetry). *)

  val mem : F.state -> sub -> bool
  (** [s ∈ S], equivalently [character S s = ↑s] (DESIGN sec.1). *)

  val character : 'a F.t -> sub -> F.state -> F.State_set.t
  (** [character S s = S ∩ ↑s], the classifying sieve of [S] at [s]
      ([temporal/trees_omega.ml:25] analogue). *)
end
