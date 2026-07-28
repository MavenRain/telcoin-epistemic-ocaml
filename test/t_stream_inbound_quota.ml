(** The STREAM_INBOUND_QUOTA family (S1, S2, S3) proves on the pristine
    {!Stream_inbound_quota_model} through [prove_nonvacuous], so every
    antecedent is checked reachable as well; the reachable graph stays in its
    justified band and at its exact pinned size; the two states the per-peer
    rate window and the identity gate forbid - a window driven past the bound
    by someone other than its owner, and an answered stream from a peer whose
    BLS identity never resolved - are unreachable; and the epistemic layer is
    genuinely partial-information: the family's single positive knowledge
    operand is contingent AND its view class is provably not a singleton, and
    all three ignorance conjuncts have reachable witnesses. *)

open Telcoin_epistemic
open Stream_inbound_quota_model

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
        (st.Stream_inbound_quota_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Stream_inbound_quota_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Stream_inbound_quota_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Loose product bound: 3 meter values x 2 own-rate values x 3 reset histories
   x 2 resolution values x 4 stream fates = 144 before any reachability
   constraint. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 144))

(* The exact pristine reachable count, pinned so a modelling drift that widens
   or narrows the graph cannot slip through as a still-green proof. It is 37:
   the meter never exceeds the opener's own rate (S1), an answered fate forces
   a resolved identity (the consensus.rs:1665 gate) and a rate-limited fate
   forces a full meter at the moment of the open, and a meter below the
   opener's rate requires one of the two resets to have fired. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "exact pristine reachable count" 37
        (Checker.reachable_count sys))

(* S1 conjunct B as a reachability fact, and the whole content of the per-peer
   keying at behavior.rs:283: no reachable state has R's window entry for W
   past the bound while W itself is still inside its allowance. This is the
   state No_per_peer_keying makes reachable. *)
let foreign_meter_pressure_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (window_count(R,W) > MAX /\\ opened(W,R) <= MAX)" false
        (Checker.satisfiable sys
           (Formula.And (f Meter_full, Formula.Not (f Own_over_cap)))))

(* The identity gate's contract at consensus.rs:1665, as a reachability fact:
   nothing is ever answered on a stream from a peer whose BLS identity has not
   resolved. This is the state No_identity_guard makes reachable, and it is
   why S3 conjunct B's knowledge holds. *)
let unresolved_answer_unreachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "not EF (answered(R,W) /\\ peer_to_bls(W) = None)" false
        (Checker.satisfiable sys
           (Formula.And (f Answered, Formula.Not (f Identity_resolved)))))

(* Both silent causes really do fire: without both of them reachable S3 would
   be a statement about an empty class rather than a proved one. *)
let both_silent_causes_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF rate_limited(R,W) /\\ EF unknown_peer_drop(R,W)"
        true
        (Checker.satisfiable sys (f Rejected)
        && Checker.satisfiable sys (f Identity_drop)))

(* The family's single positive knowledge operand is S3 conjunct B's
   K_V1(peer_to_bls(W) = Some): assert its complement is reachable, so the
   knowledge is contingent and did not collapse into plain truth under the
   view partition. It fails at every state in which W has opened nothing or has
   only ever been dropped. *)
let k_resolution_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(peer_to_bls(W) = Some): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Identity_resolved)))))

(* R2 non-singleton evidence for that same positive K. At an answered state
   pick an atom FALSE there - R's tumbling window has not rolled - and assert
   W does not know its negation. That is only possible if another reachable
   state shares W's view (View_opener, which carries no component of R's window
   phase: [started] is R's own Instant, behavior.rs:283) and satisfies it, i.e.
   the class is NOT a singleton. It contains at least the pre-roll and the
   post-roll world of the same answered exchange. *)
let k_resolution_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (answered /\\ ~rolled /\\ ~K_v1(~rolled)): view class > 1" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Answered;
                Formula.Not (f Window_rolled);
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Window_rolled)));
              ])))

(* S3 conjunct A's first ignorance witness, pointed at the quota world: W has
   been rate-limited, W has exceeded its own allowance and has not redialled,
   and W still cannot know that the quota is what killed the stream - the
   post-roll identity-drop world shares its view. *)
let ignorance_witness_quota_cause () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (rate_limited /\\ opened > MAX /\\ ~redialled /\\ ~K_v1 \
         rate_limited)"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Rejected;
                f Own_over_cap;
                Formula.Not (f Reconnected);
                Formula.Not (Formula.K (Validator.V1, f Rejected));
              ])))

(* The dual half of the same class, pointed at the identity world: the
   blindness is two-sided and not an artefact of one witness. *)
let ignorance_witness_identity_cause () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (unknown_peer_drop /\\ opened > MAX /\\ ~redialled /\\ ~K_v1 \
         unknown_peer_drop)"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Identity_drop;
                f Own_over_cap;
                Formula.Not (f Reconnected);
                Formula.Not (Formula.K (Validator.V1, f Identity_drop));
              ])))

(* S2 conjunct B's ignorance witness: after the redial deletes W's window entry
   (behavior.rs:258) the responder's whole observable state is the same for a
   peer that spent its allowance and redialled as for a peer that redialled and
   opened once, so R cannot know W's true rate. *)
let ignorance_witness_erased_history () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (redialled /\\ ~rate_limited /\\ opened > MAX /\\ ~K_v0 opened > \
         MAX)"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Reconnected;
                Formula.Not (f Rejected);
                f Own_over_cap;
                Formula.Not (Formula.K (Validator.V0, f Own_over_cap));
              ])))

(* The dual direction of that same blindness: a redialled peer whose rate is
   still inside the allowance is equally unidentifiable, so R cannot rule the
   evasion out either. *)
let ignorance_witness_erased_history_dual () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (redialled /\\ opened <= MAX /\\ ~K_v0 ~(opened > MAX))" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Reconnected;
                Formula.Not (f Own_over_cap);
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Own_over_cap)));
              ])))

let () =
  Alcotest.run "stream_inbound_quota"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Stream_inbound_quota_statements.name `Quick
              (prove_one st))
          Stream_inbound_quota_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "foreign-meter-pressure-unreachable" `Quick
            foreign_meter_pressure_unreachable;
          Alcotest.test_case "unresolved-answer-unreachable" `Quick
            unresolved_answer_unreachable;
          Alcotest.test_case "both-silent-causes-reachable" `Quick
            both_silent_causes_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-resolution-contingent" `Quick
            k_resolution_contingent;
          Alcotest.test_case "k-resolution-class-not-singleton" `Quick
            k_resolution_class_not_singleton;
          Alcotest.test_case "ignorance-witness-quota-cause" `Quick
            ignorance_witness_quota_cause;
          Alcotest.test_case "ignorance-witness-identity-cause" `Quick
            ignorance_witness_identity_cause;
          Alcotest.test_case "ignorance-witness-erased-history" `Quick
            ignorance_witness_erased_history;
          Alcotest.test_case "ignorance-witness-erased-history-dual" `Quick
            ignorance_witness_erased_history_dual;
        ] );
    ]
