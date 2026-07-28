(** The PARENT_CLAIM_BINDING family (S1, S2, S3) proves on the pristine
    {!Parent_claim_binding_model} through [prove_nonvacuous] (so each
    antecedent is checked reachable too), the reachable graph stays in its
    justified band, the three states the gates forbid are unreachable, and the
    epistemic layer is genuinely partial-information.

    The [contingency] group is where R2 and R3 are discharged:

    - the family's one POSITIVE [K] - [K_j(exists(d))] at a stored state - is
      contingent (its negation is reachable) AND its view class at the
      operative state is provably NOT a singleton: at a stored state [j] does
      not know that [b] is not the holder, which is possible only because a
      second reachable state shares [Vj Ph_stored] and disagrees on
      [holds(b,d)];
    - both [~K] conjuncts get an explicit two-member ignorance witness: the
      blocked window is reached in worlds where [d] exists and in worlds where
      it does not, and the dropped-offer state is reached both when [b]'s
      bytes are genuine and when they are forged. *)

open Telcoin_epistemic
open Parent_claim_binding_model

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
        (st.Parent_claim_binding_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Parent_claim_binding_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Parent_claim_binding_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The voter [j]: the family's only knowledge agent. *)
let j = Validator.V1

(* Loose product bound: the voter component is 4 hidden worlds x 9 evaluation
   phases = 36 and the author component is 2 stores x 6 phases = 12, so 48
   caps the disjoint sum. The pristine reachable set is exactly 32: 4 + 5 + 7 +
   6 = 22 voter states (no offer in W_none/W_c_holds, no stored/voted in
   W_none/W_bogus, and the two mutant-only phases Ph_b_hinted and
   Ph_b_offer_taken unreachable) plus 2 x 5 = 10 author states
   (Ph_auth_served_undeclared unreachable). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 48))

(* The requester binding's contract: a certificate offered by [b] while the
   outstanding-request slot names [a] is never admitted onto the vote path.
   This is the state handler.rs:936-946 forbids, and the state
   No_requester_binding makes reachable. *)
let unrequested_admission_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (offered(b,d) /\\ bound=a /\\ admitted(j,d,from=b))" false
        (Checker.satisfiable sys
           (Formula.And
              (f Offer_seen, Formula.And (f Bound_a, f Offer_admitted)))))

(* First-come exclusivity as a reachability fact: the slot is claimed once and
   never rebound, so bound(j,(r-1,d))=b is unreachable. This is the
   Entry::Vacant guard at handler.rs:910-921, and No_vacant_claim removes it. *)
let slot_never_rebound () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF bound(j,(r-1,d))=b" false
        (Checker.satisfiable sys (f Bound_b)))

(* The author-side disclosure filter's contract: a certificate the header does
   not declare is never served, whatever the author happens to hold
   (certifier.rs:150-151). No_author_parent_filter makes it reachable, but
   only from the store that actually holds the undeclared certificate. *)
let undeclared_disclosure_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF served_undeclared(a)" false
        (Checker.satisfiable sys (f A_served_undeclared)))

(* R2, half 1 - the positive K of S1 conjunct C is CONTINGENT: there are
   reachable states at which j does not know that d exists, so the knowledge
   claim is not collapsed into plain truth under the view partition. *)
let positive_k_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF ~K_j(exists(d)): knowledge did not collapse"
        true
        (Checker.satisfiable sys (Formula.Not (Formula.K (j, f D_exists)))))

(* R2, half 2 - the view class at the operative state is NOT a singleton.
   holds(b,d) is FALSE at the stored state reached in W_c_holds; asserting that
   j does not know ~holds(b,d) there is satisfiable only because a SECOND
   reachable state - the stored state of W_b_holds - shares Vj Ph_stored and
   satisfies holds(b,d). A singleton class would make this false. *)
let positive_k_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (stored(j,d) /\\ ~K_j(~holds(b,d))): the Vj Ph_stored class has \
         two members"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Stored,
                Formula.Not (Formula.K (j, Formula.Not (f B_holds_d))) ))))

(* R3 witness for S2 conjunct C, member 1: the blocked window is reached in a
   world where d genuinely exists. *)
let ignorance_blocked_exists () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (blocked(j,h_b) /\\ exists(d))" true
        (Checker.satisfiable sys (Formula.And (f Hb_blocked, f D_exists))))

(* R3 witness for S2 conjunct C, member 2: the SAME j-view is reached in a
   world where d was never built. The pair shares Vj Ph_b_filtered, so both
   K_j(exists(d)) and K_j(~exists(d)) fail there. *)
let ignorance_blocked_absent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (blocked(j,h_b) /\\ ~exists(d))" true
        (Checker.satisfiable sys
           (Formula.And (f Hb_blocked, Formula.Not (f D_exists)))))

(* R3 witness for S1 conjunct B, member 1: the offer j drops carries the
   GENUINE certificate (W_b_holds). *)
let ignorance_drop_genuine () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (offered(b,d) /\\ ~admitted /\\ exists(d))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Offer_seen,
                Formula.And (Formula.Not (f Offer_admitted), f D_exists) ))))

(* R3 witness for S1 conjunct B, member 2: the offer j drops is FORGED
   (W_bogus). Because the retain of handler.rs:936-946 runs before any
   verification, these two states share Vj Ph_b_offer_dropped exactly - which
   is the whole content of "dropping teaches j nothing". *)
let ignorance_drop_forged () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (offered(b,d) /\\ ~admitted /\\ ~exists(d))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Offer_seen,
                Formula.And
                  (Formula.Not (f Offer_admitted), Formula.Not (f D_exists)) ))))

(* Both resolutions of the blocked window are live, so S2 conjunct B's until is
   not a one-armed encoding of the timeout. *)
let both_resolutions_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF stored(j,d) and EF timeout(j,h_b)" true
        (Checker.satisfiable sys (f Stored)
        && Checker.satisfiable sys (f Hb_timedout)))

let () =
  Alcotest.run "parent_claim_binding"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Parent_claim_binding_statements.name `Quick
              (prove_one st))
          Parent_claim_binding_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "unrequested-admission-unreachable" `Quick
            unrequested_admission_unreachable;
          Alcotest.test_case "slot-never-rebound" `Quick slot_never_rebound;
          Alcotest.test_case "undeclared-disclosure-unreachable" `Quick
            undeclared_disclosure_unreachable;
          Alcotest.test_case "both-resolutions-reachable" `Quick
            both_resolutions_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "positive-k-contingent" `Quick
            positive_k_contingent;
          Alcotest.test_case "positive-k-class-not-singleton" `Quick
            positive_k_class_not_singleton;
          Alcotest.test_case "ignorance-blocked-exists" `Quick
            ignorance_blocked_exists;
          Alcotest.test_case "ignorance-blocked-absent" `Quick
            ignorance_blocked_absent;
          Alcotest.test_case "ignorance-drop-genuine" `Quick
            ignorance_drop_genuine;
          Alcotest.test_case "ignorance-drop-forged" `Quick
            ignorance_drop_forged;
        ] );
    ]
