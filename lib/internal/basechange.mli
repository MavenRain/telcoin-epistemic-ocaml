(** Base change over finite fibres, in the Boolean base [B = P(reach)]
    (DESIGN sec.2, sec.3). The modal fragment is valued in the discrete
    underlying-set object, so these are the plain finite-lattice operators the
    checker already uses (workshop P2) — NO [later]-contractivity transfers
    from the topos of trees.

    Two spans: the one-step transition span [N] (for [AX]/[EX]) and the view
    map [f_i : reach → V_i] (for [K_i]). *)

module Make (F : Frame.S) : sig
  val pre_all : 'a F.t -> F.State_set.t -> F.State_set.t
  (** [pre_all Z = {s | ∀ s' ∈ step s, s' ∈ Z} = ∀_{π₁}(π₂* Z)] — universal
      base change along the transition span; [AX] ([system.ml:57-61]). *)

  val pre_some : 'a F.t -> F.State_set.t -> F.State_set.t
  (** [pre_some Z = {s | ∃ s' ∈ step s, s' ∈ Z} = ∃_{π₁}(π₂* Z)] — the
      possibility (∃-base-change) modality; [EX] ([system.ml:62-65]). *)

  val reindex_view : 'a F.t -> Validator.t -> F.View_set.t -> F.State_set.t
  (** [f_i* T = {s | f_i s ∈ T}], preimage along the view map (DESIGN sec.3). *)

  val exists_view : 'a F.t -> Validator.t -> F.State_set.t -> F.View_set.t
  (** [Σ_{f_i} S = f_i(S)], the image; left adjoint [Σ_{f_i} ⊣ f_i*]
      (DESIGN sec.3). *)

  val forall_view : 'a F.t -> Validator.t -> F.State_set.t -> F.View_set.t
  (** [Π_{f_i} S = {u | f_i⁻¹ u ⊆ S}] over the views occurring in [reach];
      right adjoint [f_i* ⊣ Π_{f_i}] (DESIGN sec.3). *)
end
