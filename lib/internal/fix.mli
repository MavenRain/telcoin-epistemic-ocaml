(** Knaster–Tarski fixpoints over the finite lattice [P(reach)] (DESIGN
    sec.2). These are the plain finite-lattice fixpoints the checker already
    iterates ([system.ml:51-53]); over the Boolean base [B] there is no
    [later]-guardedness discipline (workshop P2). The seeds are load-bearing:
    an UNGUARDED μ (seed [⊥]) must not be seeded at [⊤] or it ⊤-collapses
    ([temporal/DESIGN.md sec.0.1.2]). *)

module Make (F : Frame.S) : sig
  val lfp : 'a F.t -> (F.State_set.t -> F.State_set.t) -> F.State_set.t
  (** [μZ. f Z], iterated from the seed [⊥ = ∅]; [AF]/[EF]/[AU]/[EU]
      ([system.ml:116-133]). *)

  val gfp : 'a F.t -> (F.State_set.t -> F.State_set.t) -> F.State_set.t
  (** [νZ. f Z], iterated from the seed [⊤ = reach]; [AG]/[EG]/[C_G]
      ([system.ml:110-115], [system.ml:94-96]). *)

  val iterate :
    'a F.t -> seed:F.State_set.t -> (F.State_set.t -> F.State_set.t) ->
    F.State_set.t
  (** Iterate [f] to a fixpoint from an EXPLICIT seed — exposes the seed so
      the μ-vs-ν mis-seed confirm-by-mutation pin can seed [AF] at [⊤]
      (DESIGN sec.6 gate 4). *)

  val steps_to_fix :
    'a F.t -> seed:F.State_set.t -> (F.State_set.t -> F.State_set.t) -> int
  (** Number of iterations to convergence — pins the [C_G] gfp convergence
      bound [≤ |reach|] (DESIGN sec.3, sec.6 gate 4). *)
end
