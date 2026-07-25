(** Formula sugar and pretty-printing: [leads_to] must desugar to
    AG (p -> AF q); [conj]/[disj] must have the documented units. *)

open Telcoin_epistemic

type atom = P | Q

let atom = function P -> "p" | Q -> "q"

let leads_to_desugars () =
  let expected =
    Formula.Ag (Formula.Implies (Formula.Atom P, Formula.Af (Formula.Atom Q)))
  in
  Alcotest.(check string)
    "leads_to = AG (p -> AF q)"
    (Formula.pp ~atom expected)
    (Formula.pp ~atom (Formula.leads_to (Formula.Atom P) (Formula.Atom Q)))

let conj_unit () =
  Alcotest.(check string) "conj [] = true" "true"
    (Formula.pp ~atom (Formula.conj []))

let disj_unit () =
  Alcotest.(check string) "disj [] = false" "false"
    (Formula.pp ~atom (Formula.disj []))

let pp_knowledge () =
  Alcotest.(check string)
    "K/C rendering"
    "K_v0(C_{v0,v1}(p))"
    (Formula.pp ~atom
       (Formula.K
          ( Validator.V0,
            Formula.Common ([ Validator.V0; Validator.V1 ], Formula.Atom P) )))

let () =
  Alcotest.run "formula"
    [
      ( "sugar",
        [
          Alcotest.test_case "leads_to" `Quick leads_to_desugars;
          Alcotest.test_case "conj-unit" `Quick conj_unit;
          Alcotest.test_case "disj-unit" `Quick disj_unit;
          Alcotest.test_case "pp-knowledge" `Quick pp_knowledge;
        ] );
    ]
