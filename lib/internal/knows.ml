(** The epistemic S5 comonad [K_i = f_i* ∘ Π_{f_i}] and its group closures
    (DESIGN sec.3). All operations total. *)

module Make (F : Frame.S) = struct
  module Bc = Basechange.Make (F)
  module Fx = Fix.Make (F)

  let knows t i s_set = Bc.reindex_view t i (Bc.forall_view t i s_set)

  let everyone t g s_set =
    List.fold_left
      (fun acc v -> F.State_set.inter acc (knows t v s_set))
      (F.reach t) g

  let common t g s_set =
    Fx.gfp t (fun z -> everyone t g (F.State_set.inter s_set z))
end
