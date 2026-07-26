(** The classical reflection bridge (DESIGN sec.4). Total; a no-op on
    two-valued arguments. *)

module Make (F : Frame.S) = struct
  let classical t s v =
    if F.State_set.mem s v then F.up t s else F.State_set.empty
end
