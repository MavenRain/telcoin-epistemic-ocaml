(** Epistemic modalities in the Boolean base [B] (DESIGN sec.3): the S5
    comonad of the essential geometric morphism over the DISCRETE base
    (workshop P3). [K_i] cuts across temporal depth, so it is NOT an
    endofunctor of [Sub(1_E)] — it is a genuine operator on [B = P(reach)],
    reconciled with [E] only through the classical reflection (DESIGN sec.4).

    Grounded in the validator's local view (Fagin–Halpern–Moses–Vardi,
    "Reasoning About Knowledge", ch. 4): [K_i φ] holds at [s] iff [φ] holds at
    every reachable state [i] cannot locally distinguish from [s]. *)

module Make (F : Frame.S) : sig
  val knows : 'a F.t -> Validator.t -> F.State_set.t -> F.State_set.t
  (** [K_i S = f_i*(Π_{f_i} S) = {s | the ~_i-class of s ⊆ S}] — the necessity
      comonad [h* ∘ h_*] of the geometric morphism induced by [f_i]; a lex
      idempotent S5 comonad. Equals [system.ml:69-87] [knows] verbatim. *)

  val everyone : 'a F.t -> Validator.t list -> F.State_set.t -> F.State_set.t
  (** [E_G φ = ⋀_{i∈G} K_i φ] ([system.ml:89-92]); [E_∅ = ⊤]. *)

  val common : 'a F.t -> Validator.t list -> F.State_set.t -> F.State_set.t
  (** [C_G φ = νZ. E_G(φ ∧ Z)], the gfp seeded [⊤], converging in [≤ |reach|]
      iterations ([system.ml:94-96]). *)
end
