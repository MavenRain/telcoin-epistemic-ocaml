(** Sieve-graded [Ω] over the reachability order (a poset for 57 of the 69
    models, a preorder for the other 12; [W] is thin either way) (DESIGN
    sec.1). Every operation is total; matches are exhaustive. *)

module Make (F : Frame.S) = struct
  type sieve = F.State_set.t

  let truth t s = F.up t s
  let bot = F.State_set.empty
  let meet a b = F.State_set.inter a b
  let join a b = F.State_set.union a b

  let imp t s a b =
    F.State_set.filter
      (fun x ->
        F.State_set.for_all
          (fun u -> Bool.not (F.State_set.mem u a) || F.State_set.mem u b)
          (F.up t x))
      (F.up t s)

  let neg t s a = imp t s a bot
  let is_true (_ : 'a F.t) s a = F.State_set.mem s a
end
