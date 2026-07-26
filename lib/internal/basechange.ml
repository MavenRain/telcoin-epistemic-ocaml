(** Base change along the transition span and the view maps (DESIGN sec.2,
    sec.3). All operations total. *)

module Make (F : Frame.S) = struct
  let pre_all t z =
    F.State_set.filter
      (fun s -> List.for_all (fun s' -> F.State_set.mem s' z) (F.step t s))
      (F.reach t)

  let pre_some t z =
    F.State_set.filter
      (fun s -> List.exists (fun s' -> F.State_set.mem s' z) (F.step t s))
      (F.reach t)

  let reindex_view t i tset =
    F.State_set.filter
      (fun s -> F.View_set.mem (F.view_of t i s) tset)
      (F.reach t)

  let exists_view t i sset =
    F.State_set.fold
      (fun s acc -> F.View_set.add (F.view_of t i s) acc)
      sset F.View_set.empty

  let forall_view t i sset =
    let image = exists_view t i (F.reach t) in
    F.View_set.filter
      (fun u ->
        F.State_set.subset
          (reindex_view t i (F.View_set.singleton u))
          sset)
      image
end
