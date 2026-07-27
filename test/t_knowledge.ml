(** Knowledge operators against hidden state - the side t_kernel cannot see
    (its toy systems give every validator full observability, collapsing K to
    truth). Here each validator observes ONE bit of a two-bit global state:
    v0 and v2 see bit 0, v1 and v3 see bit 1.

    The muddy-children pair of models pins the announcement effect:
    - [announced]: state (0,0) is not reachable ("at least one bit is set"
      is public). Every validator then KNOWS at-least-one at every state,
      and it is common knowledge.
    - [silent]: all four states reachable. At (0,1), v0 sees 0 and considers
      (0,0) possible, so v0 does NOT know at-least-one - even though it is
      true there. K must separate truth from knowledge; a checker that
      conflates them flips this row. *)

open Telcoin_epistemic

module Bit_pair = struct
  type t = int * int

  let compare (a0, a1) (b0, b1) =
    let c = Int.compare a0 b0 in
    if Int.equal c 0 then Int.compare a1 b1 else c
end

module Sys = System.Make (Bit_pair) (Int)

type atom = At_least_one | Bit0_set | Bit1_set

let label a (b0, b1) =
  match a with
  | At_least_one -> Int.equal 1 b0 || Int.equal 1 b1
  | Bit0_set -> Int.equal 1 b0
  | Bit1_set -> Int.equal 1 b1

let view v (b0, b1) =
  match v with
  | Validator.V0 -> b0
  | Validator.V1 -> b1
  | Validator.V2 -> b0
  | Validator.V3 -> b1
  (* V4..V9: non-participants of this toy frame - constant blind view. *)
  | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7 | Validator.V8
  | Validator.V9 ->
      0

let spec_of_states states =
  { Sys.init = states; next = (fun _ -> []); view; label }

let announced = spec_of_states [ (1, 0); (0, 1); (1, 1) ]

let silent = spec_of_states [ (0, 0); (1, 0); (0, 1); (1, 1) ]

let with_sys spec k =
  Result.fold
    ~ok:k
    ~error:(fun Sys.Empty_init -> Alcotest.fail "make: empty init")
    (Sys.make spec)

(* This model's committee stays the original four validators; the global
   roster is now the ten-member tn_model committee. *)
let all_h = [ Validator.V0; Validator.V1; Validator.V2; Validator.V3 ]

let knows_own_bit () =
  with_sys silent (fun sys ->
      Alcotest.(check bool) "G(bit0 -> K_v0 bit0)" true
        (Sys.valid sys
           (Formula.Ag
              (Formula.Implies
                 (Formula.Atom Bit0_set, Formula.K (Validator.V0, Formula.Atom Bit0_set))))))

let cannot_know_other_bit () =
  with_sys silent (fun sys ->
      Alcotest.(check bool) "G(bit1 -> K_v0 bit1) refuted" false
        (Sys.valid sys
           (Formula.Ag
              (Formula.Implies
                 (Formula.Atom Bit1_set, Formula.K (Validator.V0, Formula.Atom Bit1_set))))))

let truth_without_knowledge () =
  with_sys silent (fun sys ->
      Alcotest.(check bool) "at (0,1): at_least_one true but K_v0 refuted" false
        (Sys.valid sys
           (Formula.Ag
              (Formula.Implies
                 (Formula.Atom At_least_one,
                  Formula.K (Validator.V0, Formula.Atom At_least_one))))))

let announcement_creates_knowledge () =
  with_sys announced (fun sys ->
      Alcotest.(check bool) "announced: G(E_H at_least_one)" true
        (Sys.valid sys
           (Formula.Ag (Formula.Everyone (all_h, Formula.Atom At_least_one)))))

let announcement_creates_common_knowledge () =
  with_sys announced (fun sys ->
      Alcotest.(check bool) "announced: G(C_H at_least_one)" true
        (Sys.valid sys
           (Formula.Ag (Formula.Common (all_h, Formula.Atom At_least_one)))))

let silent_refutes_common_knowledge () =
  with_sys silent (fun sys ->
      Alcotest.(check bool) "silent: C_H at_least_one refuted even at (1,1)" false
        (Sys.satisfiable sys
           (Formula.Common (all_h, Formula.Atom At_least_one))))

let knowledge_is_veridical () =
  with_sys silent (fun sys ->
      Alcotest.(check bool) "G(K_v0 bit0 -> bit0): truth axiom" true
        (Sys.valid sys
           (Formula.Ag
              (Formula.Implies
                 (Formula.K (Validator.V0, Formula.Atom Bit0_set), Formula.Atom Bit0_set)))))

let common_implies_everyone () =
  with_sys announced (fun sys ->
      Alcotest.(check bool) "G(C_H phi -> E_H phi)" true
        (Sys.valid sys
           (Formula.Ag
              (Formula.Implies
                 (Formula.Common (all_h, Formula.Atom At_least_one),
                  Formula.Everyone (all_h, Formula.Atom At_least_one))))))

let () =
  Alcotest.run "knowledge"
    [
      ( "k",
        [
          Alcotest.test_case "knows-own-bit" `Quick knows_own_bit;
          Alcotest.test_case "cannot-know-other-bit" `Quick cannot_know_other_bit;
          Alcotest.test_case "truth-without-knowledge" `Quick truth_without_knowledge;
          Alcotest.test_case "veridical" `Quick knowledge_is_veridical;
        ] );
      ( "common",
        [
          Alcotest.test_case "announced-everyone" `Quick announcement_creates_knowledge;
          Alcotest.test_case "announced-common" `Quick announcement_creates_common_knowledge;
          Alcotest.test_case "silent-no-common" `Quick silent_refutes_common_knowledge;
          Alcotest.test_case "common-implies-everyone" `Quick common_implies_everyone;
        ] );
    ]
