(** Base category [W] and reachability skeleton (DESIGN sec.1). Reuses
    {!System}'s set and spec types so one spec drives both checkers. *)

module type S = sig
  type state
  type view

  module State_set : Set.S with type elt = state
  module View_set : Set.S with type elt = view

  type 'a spec = {
    init : state list;
    next : state -> state list;
    view : Validator.t -> state -> view;
    label : 'a -> state -> bool;
  }

  type 'a t
  type build_error = Empty_init

  val make : 'a spec -> ('a t, build_error) result
  val spec : 'a t -> 'a spec
  val reach : 'a t -> State_set.t
  val states : 'a t -> state list
  val reachable_count : 'a t -> int
  val mem : 'a t -> state -> bool
  val step : 'a t -> state -> state list
  val leq : 'a t -> state -> state -> bool
  val up : 'a t -> state -> State_set.t
  val view_of : 'a t -> Validator.t -> state -> view
  val fibre : 'a t -> Validator.t -> state -> State_set.t

  type 'x obj = {
    sections : state -> 'x list;
    restrict : state -> state -> 'x -> 'x;
  }

  val terminal : 'a t -> unit obj
  val certify_functorial : 'a t -> unit Comp_cat.Res.t
end

module Make (State : System.ORDERED) (View : System.ORDERED) :
  S with type state = State.t and type view = View.t = struct
  module Sys = System.Make (State) (View)
  module State_set = Sys.State_set
  module View_set = Set.Make (View)
  module State_map = Map.Make (State)

  type state = State.t
  type view = View.t

  type 'a spec = {
    init : state list;
    next : state -> state list;
    view : Validator.t -> state -> view;
    label : 'a -> state -> bool;
  }

  type 'a t = {
    the_spec : 'a spec;
    the_reach : State_set.t;
    up_map : State_set.t State_map.t;
  }

  type build_error = Empty_init

  (* Terminals stutter (system.ml:24-25) so every path is infinite. *)
  let step_spec spec s =
    match spec.next s with [] -> [ s ] | _ :: _ as succs -> succs

  let reachable spec =
    let rec go frontier seen =
      match frontier with
      | [] -> seen
      | s :: rest ->
          let fresh =
            List.filter
              (fun s' -> Bool.not (State_set.mem s' seen))
              (step_spec spec s)
          in
          go
            (List.rev_append fresh rest)
            (List.fold_left (fun acc s' -> State_set.add s' acc) seen fresh)
    in
    go spec.init (State_set.of_list spec.init)

  (* The future cone [↑s] by breadth-first closure of the one-step relation
     from [s]; correct on any finite graph (the model's only cycle is the
     terminal self-loop, DESIGN sec.1). *)
  let cone_of spec s =
    let rec go frontier seen =
      match frontier with
      | [] -> seen
      | x :: rest ->
          let fresh =
            List.filter
              (fun y -> Bool.not (State_set.mem y seen))
              (step_spec spec x)
          in
          go
            (List.rev_append fresh rest)
            (List.fold_left (fun acc y -> State_set.add y acc) seen fresh)
    in
    go [ s ] (State_set.singleton s)

  let make spec =
    match spec.init with
    | [] -> Error Empty_init
    | _ :: _ ->
        let the_reach = reachable spec in
        let up_map =
          State_set.fold
            (fun s acc -> State_map.add s (cone_of spec s) acc)
            the_reach State_map.empty
        in
        Ok { the_spec = spec; the_reach; up_map }

  let spec t = t.the_spec
  let reach t = t.the_reach
  let states t = State_set.elements t.the_reach
  let reachable_count t = State_set.cardinal t.the_reach
  let mem t s = State_set.mem s t.the_reach
  let step t s = step_spec t.the_spec s

  let up t s =
    Option.fold ~none:(State_set.singleton s) ~some:Fun.id
      (State_map.find_opt s t.up_map)

  let leq t s u = State_set.mem u (up t s)
  let view_of t v s = t.the_spec.view v s

  let fibre t v s =
    let key = view_of t v s in
    State_set.filter
      (fun u -> Int.equal 0 (View.compare (view_of t v u) key))
      t.the_reach

  type 'x obj = {
    sections : state -> 'x list;
    restrict : state -> state -> 'x -> 'x;
  }

  let terminal (_ : 'a t) : unit obj =
    { sections = (fun _ -> [ () ]); restrict = (fun _ _ () -> ()) }

  let certify_functorial t =
    let elems = states t in
    let reflexive = List.for_all (fun s -> leq t s s) elems in
    let transitive =
      List.for_all
        (fun s ->
          State_set.for_all
            (fun u -> State_set.for_all (fun w -> leq t s w) (up t u))
            (up t s))
        elems
    in
    (* Reflexivity and transitivity are tautological for the ⊑ = reachability
       closure ([up] is seeded with [s] and BFS-closed); ANTISYMMETRY is the
       property that actually distinguishes a finite poset from a cyclic
       preorder, and a genuine (non-terminal) cycle s →* u →* s with s ≠ u
       violates it. Only u ∈ ↑s can witness a violation, so quantify over
       [up t s]. The Done self-loop is s = u and is exempt. *)
    let antisymmetric =
      List.for_all
        (fun s ->
          State_set.for_all
            (fun u ->
              Int.equal 0 (State.compare s u)
              || Bool.not (leq t s u && leq t u s))
            (up t s))
        elems
    in
    if reflexive && transitive && antisymmetric then Comp_cat.Res.ok ()
    else
      Comp_cat.Res.error
        (Comp_cat.Err.Not_universal
           {
             detail =
               "Frame.certify_functorial: ⊑ is not a finite poset \
                (antisymmetry fails: a genuine cycle collapses two states)";
           })
end
