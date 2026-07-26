(** [Sub(1_E)], the finite Heyting algebra of future-closed subsets of
    [reach] (DESIGN sec.1). All operations total. *)

module Make (F : Frame.S) = struct
  type sub = F.State_set.t

  let top t = F.reach t
  let bot = F.State_set.empty
  let of_pred t p = F.State_set.filter p (F.reach t)
  let meet a b = F.State_set.inter a b
  let join a b = F.State_set.union a b

  let imp t a b =
    F.State_set.filter
      (fun s ->
        F.State_set.for_all
          (fun x -> Bool.not (F.State_set.mem x a) || F.State_set.mem x b)
          (F.up t s))
      (F.reach t)

  let neg t a =
    F.State_set.filter
      (fun s -> F.State_set.is_empty (F.State_set.inter (F.up t s) a))
      (F.reach t)

  let equal a b = F.State_set.equal a b
  let mem s a = F.State_set.mem s a
  let character t a s = F.State_set.inter a (F.up t s)
end
