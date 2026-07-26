(** Gate 3 — the reflection non-vacuity probe (DESIGN sec.0.1.4, sec.6 gate 3).

    The classical {!Reflect} bridge is a NO-OP on S1–S7 (every antecedent and
    [Not]-argument there is a crisp Boolean of atoms under a modal wrapper), so
    it is green-by-vacuity unless a synthetic witness exercises it. On a small
    synthetic frame with a genuinely sieve-graded [Ag p]:

    (a) the reflected [grade] equals the classical [System.sat];
    (b) DELETING [classical] ([grade_noreflect]) FLIPS the probe — proving the
        reflection path is live — while S1–S7 stay green under the same
        deletion — proving vacuity on them. *)

open Telcoin_epistemic

type atom = P | Q

let label a s =
  match a with P -> Int.equal s 1 || Int.equal s 2 | Q -> Int.equal s 2

(* Chain 0 -> 1 -> 2, with 2 terminal (stutter-closed). [P] holds on the
   future-closed set {1,2}; [Q] on {2}. At world 0, [Ag P] is FALSE but its
   grade [character {1,2} 0 = {1,2}] is a proper sieve, so reflection bites. *)
let next s = if Int.equal s 0 then [ 1 ] else if Int.equal s 1 then [ 2 ] else []

module Oracle = System.Make (Int) (Int)
module Checker = Denote.Make (Int) (Int)

let ospec : atom Oracle.spec =
  { Oracle.init = [ 0 ]; next; view = (fun _ s -> s); label }

let dspec : atom Checker.spec =
  { Checker.init = [ 0 ]; next; view = (fun _ s -> s); label }

let probe_a = Formula.Not (Formula.Ag (Formula.Atom P))
let probe_b = Formula.Implies (Formula.Ag (Formula.Atom P), Formula.Atom Q)
let worlds = [ 0; 1; 2 ]

let with_pair k =
  Result.fold ~error:(fun Oracle.Empty_init -> Alcotest.fail "oracle init")
    ~ok:(fun osys ->
      Result.fold
        ~error:(fun Checker.Empty_init -> Alcotest.fail "denote init")
        ~ok:(fun dsys -> k osys dsys)
        (Checker.make dspec))
    (Oracle.make ospec)

let holds_reflect dsys f s = Checker.is_true dsys s (Checker.grade dsys f s)

let holds_noreflect dsys f s =
  Checker.is_true dsys s (Checker.grade_noreflect dsys f s)

let oracle_holds osys f s = Oracle.State_set.mem s (Oracle.sat osys f)

(* (a) reflected grade = classical sat, at every world, for both probes. *)
let reflected_equals_classical () =
  with_pair (fun osys dsys ->
      let agree f =
        List.for_all
          (fun s -> Bool.equal (holds_reflect dsys f s) (oracle_holds osys f s))
          worlds
      in
      Alcotest.(check bool) "reflected grade = classical sat (both probes)" true
        (agree probe_a && agree probe_b))

(* (b) deleting classical flips both probes at world 0. *)
let deletion_flips_probe () =
  with_pair (fun _osys dsys ->
      Alcotest.(check (list bool))
        "with-reflection true, without-reflection false, at world 0"
        [ true; false; true; false ]
        [
          holds_reflect dsys probe_a 0;
          holds_noreflect dsys probe_a 0;
          holds_reflect dsys probe_b 0;
          holds_noreflect dsys probe_b 0;
        ])

(* (b) S1–S7 stay green under the SAME deletion: reflection never fires on
   them (all Not/Implies sit under a modal wrapper, where grade delegates to
   the Boolean bset), so grade and grade_noreflect give the identical verdict
   at the initial world. *)
let statements_vacuous_under_deletion () =
  Result.fold
    ~error:(fun Tn_model.Checker.Empty_init -> Alcotest.fail "tn init")
    ~ok:(fun sys ->
      let w0 = Tn_state.initial in
      let both_true st =
        let f = st.Statements.formula in
        Tn_model.Checker.is_true sys w0 (Tn_model.Checker.grade sys f w0)
        && Tn_model.Checker.is_true sys w0
             (Tn_model.Checker.grade_noreflect sys f w0)
      in
      Alcotest.(check bool)
        "all 7 statements validate with reflection ON and OFF alike" true
        (List.for_all both_true Statements.all))
    (Tn_model.make ())

let () =
  Alcotest.run "reflection"
    [
      ( "non-vacuity",
        [
          Alcotest.test_case "reflected=classical" `Quick reflected_equals_classical;
          Alcotest.test_case "deletion-flips" `Quick deletion_flips_probe;
          Alcotest.test_case "statements-vacuous" `Quick statements_vacuous_under_deletion;
        ] );
    ]
