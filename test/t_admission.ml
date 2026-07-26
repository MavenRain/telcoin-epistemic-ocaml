(** The ADMISSION family (#4, #7) proves on the pristine {!Admission_model}
    through [prove_nonvacuous] (so each antecedent is also checked reachable),
    the reachable graph stays in its justified band, and the epistemic layer is
    genuinely partial-information: the one positive knowledge operand is
    contingent, and both cards' false witnesses - V1 banned-yet-ignorant (#7)
    and V2 unable to see V1's ban of O (#4) - are reachable, while the state the
    admission-denial gate forbids (connected-while-banned) is unreachable. *)

open Telcoin_epistemic
open Admission_model

(** Build the pristine system or fail the test on an impossible [Empty_init]. *)
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
        (st.Admission_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Admission_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Admission_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: two connection states x two ban states = 4 per-pair
   values, three independent pairs = 4^3 = 64. The pristine reachable set is
   exactly 27 (3^3) because the retry guard keeps (Up,Banned) off every pair;
   only the admission-denial mutation reaches the 4th value. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 64))

(* The pristine severance invariant: (Up,Banned) is unreachable on both the
   (V1 -> O) and (V2 -> V1) pairs, so an admitted connection is never banned -
   exactly what the admission denial enforces and the mutation removes. *)
let admitted_never_banned () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G (conn-up -> unbanned) on P1 and P3" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.And
                 ( Formula.Implies (f Conn_v1o_up, Formula.Not (f Ban_1o_active)),
                   Formula.Implies (f Conn_v2v1_up, Formula.Not (f Ban_2v1_active))
                 )))))

(* The single positive knowledge conjunct across the family is
   K_V1(~banned_2(V1)) in #7 conjunct 2: assert its complement is reachable, so
   the operand is NOT plain truth under the view partition and the statement is
   not epistemically vacuous. *)
let k_v1_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(~banned_2(V1)): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K (Validator.V1, Formula.Not (f Ban_2v1_active))))))

(* #7 card false witness: the temp-ban ignorance window - V2 bans V1 (conn
   dropped) yet V1 cannot know it, because the still-banned state and its
   post-expiry sibling share V1's view (V1 never sees V2's banner-local flag). *)
let false_witness_tempban () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (banned_2(V1) /\\ ~K_v1 banned_2(V1))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Ban_2v1_active,
                Formula.Not (Formula.K (Validator.V1, f Ban_2v1_active)) ))))

(* #4 card false witness: internode opacity - V1 bans the phantom peer O while
   V2 does not, and V2 (whose view holds no component of the V1 -> O pair)
   cannot know it. *)
let false_witness_opacity () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (banned_1(O) /\\ ~banned_2(O) /\\ ~K_v2 banned_1(O))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Ban_1o_active,
                Formula.And
                  ( Formula.Not (f Ban_2o_active),
                    Formula.Not (Formula.K (Validator.V2, f Ban_1o_active)) ) ))))

(* The severance guard's contract: the connected-while-banned state on (V1 -> O)
   - conn(V1,O)=Up with ban_1(O) still active - is UNreachable pristine, which
   is exactly why #4's inner Eu is unsatisfiable; the mutation makes it
   reachable and flips the proof. *)
let connected_while_banned_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (conn(V1,O)=up /\\ banned_1(O))" false
        (Checker.satisfiable sys
           (Formula.And (f Conn_v1o_up, f Ban_1o_active))))

let () =
  Alcotest.run "admission"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Admission_statements.name `Quick
              (prove_one st))
          Admission_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "admitted-never-banned" `Quick admitted_never_banned;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-v1-contingent" `Quick k_v1_contingent;
          Alcotest.test_case "false-witness-tempban" `Quick false_witness_tempban;
          Alcotest.test_case "false-witness-opacity" `Quick false_witness_opacity;
          Alcotest.test_case "connected-while-banned-unreachable" `Quick
            connected_while_banned_unreachable;
        ] );
    ]
