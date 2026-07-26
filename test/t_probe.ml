open Telcoin_epistemic
open Prefetch_model

let a x = Formula.Atom x
let notf x = Formula.Not x
let andf l r = Formula.And (l, r)
let hbo = Formula.K (Validator.V1, a Held_by_other)

let sat mut f =
  match Checker.make (spec_of mut) with
  | Error _ -> false
  | Ok sys -> Checker.satisfiable sys f

let probe tag mut =
  Printf.printf "[%s]\n" tag;
  (* hold-state with Cooperate (D_coop) and positive K there *)
  Printf.printf "  Dcoop exists (Holds & byz):            %b\n"
    (sat mut (andf (a Holds) (a Byz_cooperate)));
  Printf.printf "  positive K at Dcoop (Holds&byz&K):     %b\n"
    (sat mut (andf (a Holds) (andf (a Byz_cooperate) hbo)));
  (* non-coop hold-state = collision partner in same view (T,T,F) *)
  Printf.printf "  non-coop HOLD w/ no holder (Holds&~byz&~HbO): %b\n"
    (sat mut (andf (a Holds) (andf (notf (a Byz_cooperate)) (notf (a Held_by_other)))));
  (* is the hold-view-class a singleton in this model? true if NO second state has view stored=T *)
  Printf.printf "  any HOLD state with HbO false (=> class not singleton on stored): %b\n"
    (sat mut (andf (a Holds) (notf (a Held_by_other))));
  (* K holds anywhere with Holds *)
  Printf.printf "  EF (Holds & K):                        %b\n"
    (sat mut (andf (a Holds) hbo))

let () = probe "PRISTINE" Pristine; probe "MUTATED" No_content_addressing
