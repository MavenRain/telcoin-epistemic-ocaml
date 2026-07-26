(** Gate 2 — the EXECUTABLE reduction gate (DESIGN sec.0.1.3, sec.6 gate 2,
    the D3 guardrail).

    For every subformula of every statement Si AND a spanning hand battery
    covering all {!Formula.t} constructors, assert

      [is_true (Denote.grade sys f s) = State_set.mem s (System.sat oracle f)]

    at ALL reachable [s], over the pristine model and all six mutants. This
    mechanically proves the presheaf-topos denotation ({!Denote}) equals the
    original checker ({!System}) operator-by-operator — in particular it is
    what actually catches a wrong persistence direction (sec.0.1.2) or a
    mis-seeded fixpoint; the pen-and-paper sec.4 argument is not enough. *)

open Telcoin_epistemic

(* The reduction oracle: the original checker (system.ml), kept per DESIGN
   sec.5. Denote's [State_set] is the SAME module (both are
   [System.Make (Tn_state) (Tn_state.Local).State_set]). *)
module Oracle = System.Make (Tn_state) (Tn_state.Local)

let muts =
  [
    Tn_model.Pristine;
    Tn_model.Drop_batch_gate;
    Tn_model.Weak_quorum;
    Tn_model.No_support_check;
    Tn_model.Unbounded_delay;
    Tn_model.Leader_censors_v2;
    Tn_model.No_vote_once;
  ]

let oracle_spec mut : Tn_model.atom Oracle.spec =
  {
    Oracle.init = [ Tn_state.initial ];
    next = Tn_model.next_with mut;
    view = (fun v s -> Tn_state.local_of s v);
    label = Tn_model.label;
  }

let rec subformulas f =
  f
  ::
  (match f with
  | Formula.Atom _ | Formula.Top | Formula.Bot -> []
  | Formula.Not p
  | Formula.Ax p
  | Formula.Ex p
  | Formula.Ag p
  | Formula.Eg p
  | Formula.Af p
  | Formula.Ef p
  | Formula.K (_, p)
  | Formula.Everyone (_, p)
  | Formula.Common (_, p) ->
      subformulas p
  | Formula.And (l, r)
  | Formula.Or (l, r)
  | Formula.Implies (l, r)
  | Formula.Au (l, r)
  | Formula.Eu (l, r) ->
      subformulas l @ subformulas r)

(* A spanning hand battery: every AST constructor, including the possibility
   modalities EX/EF/EG and the past-closed [Not At_done] that pins the
   persistence direction. *)
let battery =
  let open Formula in
  let a1 = Atom (Tn_model.Cert_formed Tn_model.anchor) in
  let a2 = Atom Tn_model.At_done in
  let a3 = Atom Tn_model.Byz_equivocating in
  let a4 = Atom (Tn_model.In_dag (Validator.V1, Tn_model.anchor)) in
  let a5 = Atom Tn_model.Conflicting_certs in
  [
    a1; a2; a3; Top; Bot; Not a2; Not a1; Not a5;
    And (a1, a2); Or (a1, a2); Implies (a1, a2); Implies (a4, a3);
    Ax a1; Ex a1; Ag a1; Eg a1; Af a2; Ef a1; Au (a1, a2); Eu (a1, a2);
    K (Validator.V0, a1); Everyone (Tn_model.honest, a1);
    Common (Tn_model.honest, a1);
    Ag (Implies (a4, K (Validator.V1, Atom (Tn_model.Quorum_voted Tn_model.anchor))));
    Not (Ag (Not a5)); Implies (Af a2, a1); Ax (Ax a2); Ag (Not a5);
    Eg (Not a2);
  ]

let statement_formulas =
  List.concat_map
    (fun st -> subformulas st.Statements.formula @ subformulas st.Statements.antecedent)
    Statements.all

(* Dedup structurally (atoms are first-order — no functions — so polymorphic
   compare is total): the seven statements share many subformulas. *)
let all_formulas = List.sort_uniq compare (List.append statement_formulas battery)

let with_pair mut k =
  Result.fold
    ~error:(fun Oracle.Empty_init -> Alcotest.fail "oracle: empty init")
    ~ok:(fun osys ->
      Result.fold
        ~error:(fun Tn_model.Checker.Empty_init -> Alcotest.fail "denote: empty init")
        ~ok:(fun dsys -> k osys dsys)
        (Tn_model.Checker.make (Tn_model.spec_of mut)))
    (Oracle.make (oracle_spec mut))

(* Returns [None] on success, or [Some formula-index] of the first mismatch,
   so a failure is diagnosable. Combinators throughout (no two-arm option
   match): [List.find_map] short-circuits on the first offending formula. *)
let first_mismatch osys dsys =
  let states = Tn_model.Checker.states dsys in
  List.find_map
    (fun (idx, f) ->
      let g = Tn_model.Checker.grade dsys f in
      let osat = Oracle.sat osys f in
      let agrees s =
        Bool.equal
          (Tn_model.Checker.is_true dsys s (g s))
          (Oracle.State_set.mem s osat)
      in
      if List.for_all agrees states then None else Some idx)
    (List.mapi (fun i f -> (i, f)) all_formulas)

let reduction_holds mut () =
  with_pair mut (fun osys dsys ->
      Alcotest.(check (option int))
        ("is_true ∘ grade = sat over "
        ^ Int.to_string (List.length all_formulas)
        ^ " formulas × "
        ^ Int.to_string (Tn_model.Checker.reachable_count dsys)
        ^ " worlds")
        None (first_mismatch osys dsys))

let mut_name = function
  | Tn_model.Pristine -> "pristine"
  | Tn_model.Drop_batch_gate -> "drop-batch-gate"
  | Tn_model.Weak_quorum -> "weak-quorum"
  | Tn_model.No_support_check -> "no-support-check"
  | Tn_model.Unbounded_delay -> "unbounded-delay"
  | Tn_model.Leader_censors_v2 -> "leader-censors-v2"
  | Tn_model.No_vote_once -> "no-vote-once"

let () =
  Alcotest.run "reduction"
    [
      ( "is_true-grade-equals-sat",
        List.map
          (fun mut ->
            Alcotest.test_case (mut_name mut) `Quick (reduction_holds mut))
          muts );
    ]
