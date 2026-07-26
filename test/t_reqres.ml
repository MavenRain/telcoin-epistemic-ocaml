(** The reqres family (DESIGN replacement for #10) proves on the pristine
    {!Reqres_model} through [prove_nonvacuous] (so the antecedent is also
    checked reachable), the reachable graph stays in its justified band,
    and the epistemic layer is genuinely partial-information: the K_V1
    operand is contingent (its ~K is satisfiable), and the card's false
    witness - an outstanding request to V3 whose serve-forged/deny branch
    leaves V3 NOT holding the bytes, view-identical to the genuine branch
    where V3 does hold - is reachable on both sides. *)

open Telcoin_epistemic
open Reqres_model

(** Build the pristine system or fail the test on an impossible
    [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

(** Render a proof error for the assertion message. *)
let error_to_string = function
  | Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Reqres_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Reqres_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Reqres_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* The reachable set is the one-fetch walk with a 5-way hidden branch at
   Init: 1 initial state plus 5 branches x 3 phases (Serving, Verifying,
   Done) = 16 states; the executed cache/response fields are
   phase-and-branch determined, so they add no factor. 32 leaves slack. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 32))

(** Every path reaches the terminal phase. *)
let terminal_reached () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF done" true
        (Checker.valid sys (Formula.Af (f At_done))))

(** The pristine digest gate's contract: V1 never caches an unheld V3
    output - a verified-from-V3 state entails V3 possessed the bytes
    (state-sync consensus.rs:84-89). The [No_digest_gate] mutation is
    exactly what breaks this. *)
let gate_blocks_unheld_cache () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G (verified-from-v3 -> held-v3)" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies (f (Verified_from Resp_v3), f (Held Resp_v3))))))

(* The formula's single positive K occurrence is K_V1(held-v3) in the
   verified-implies-knowledge conjunct: assert its ~K is satisfiable, or
   the operand would be plain truth under the view partition and the
   statement epistemically vacuous. *)
let k_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(held-v3): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f (Held Resp_v3))))))

(* wcheck operand-false side: V1's request to V3 is outstanding (nothing
   cached) while V3 does NOT hold the bytes - the serve-forged/deny
   branch of the false witness. *)
let false_witness_unheld () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (pending-from-v3 /\\ ~held-v3)" true
        (Checker.satisfiable sys
           (Formula.And
              (f (Pending_from Resp_v3), Formula.Not (f (Held Resp_v3))))))

(* wcheck operand-true collision partner: the SAME V1 view (outstanding
   request to V3, empty cache) in the genuine branch where V3 DOES hold -
   view-identical to the false witness, which is exactly why
   K_v1(held-v3) fails at both and the ~K teeth are contingent. *)
let collision_partner_held () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (pending-from-v3 /\\ held-v3)" true
        (Checker.satisfiable sys
           (Formula.And (f (Pending_from Resp_v3), f (Held Resp_v3)))))

(* The holds-and-denies ray telcoin-network acknowledges (mod.rs:791-795,
   :1892-1910): an asked-and-possessing V3 ([Withhold]) concludes the
   fetch with nothing verified. This is exactly the witness refuting the
   inevitability claim [Ag((pending /\ held) -> Af verified)] the
   statement deliberately does NOT make - if this test fails, possession
   has been re-hardwired to cooperation. *)
let withheld_terminal_unverified () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (done /\\ held-v3 /\\ ~verified-from-v3)" true
        (Checker.satisfiable sys
           (Formula.And
              ( f At_done,
                Formula.And
                  (f (Held Resp_v3), Formula.Not (f (Verified_from Resp_v3)))
              ))))

let () =
  Alcotest.run "reqres"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Reqres_statements.name `Quick (prove_one st))
          Reqres_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "terminal-reached" `Quick terminal_reached;
          Alcotest.test_case "gate-blocks-unheld-cache" `Quick
            gate_blocks_unheld_cache;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-contingent" `Quick k_contingent;
          Alcotest.test_case "false-witness-unheld" `Quick false_witness_unheld;
          Alcotest.test_case "collision-partner-held" `Quick
            collision_partner_held;
          Alcotest.test_case "withheld-terminal-unverified" `Quick
            withheld_terminal_unverified;
        ] );
    ]
