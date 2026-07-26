(** Knaster–Tarski μ/ν over [P(reach)] (DESIGN sec.2). Iteration to a fixed
    point terminates on the finite lattice for any monotone [f]. *)

module Make (F : Frame.S) = struct
  let rec run f z =
    let z' = f z in
    if F.State_set.equal z z' then z else run f z'

  let lfp (_ : 'a F.t) f = run f F.State_set.empty
  let gfp t f = run f (F.reach t)
  let iterate (_ : 'a F.t) ~seed f = run f seed

  let steps_to_fix (_ : 'a F.t) ~seed f =
    let rec go n z =
      let z' = f z in
      if F.State_set.equal z z' then n else go (n + 1) z'
    in
    go 0 seed
end
