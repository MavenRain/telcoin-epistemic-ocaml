(** Proof suite for the ARCHIVE_DIGEST_LOOKUP family: the three statements
    prove on the pristine model, the model stays inside its stated size bound,
    each gate's forbidden state is genuinely unreachable, and - the part that
    matters most - every knowledge and ignorance claim is discharged by an
    explicit witness rather than by a collapsed view class.

    The [contingency] group carries, for each K conjunct, both obligations:
    the knowledge is contingent (its negation is satisfiable somewhere
    reachable) and its view class at the operative state is NOT a singleton
    (at an operative state the knower fails to know the negation of an atom
    that is false there, which is only possible when another reachable state
    shares its view and satisfies that atom). For the ignorance conjunct it
    carries the witness pair: a state where the operand is true yet unknown,
    and a state with the same advertisement where it is false. *)

open Telcoin_epistemic
open Archive_digest_lookup_model

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
        (st.Archive_digest_lookup_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Archive_digest_lookup_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Archive_digest_lookup_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The exact pristine reachable count: 9 archive configurations x 4 exchange
    phases. The nine are the fresh pack, d saved, d+g saved, the repaired
    pack, the two post-repair single-record packs (d re-saved, e recycling
    p0), their two two-record extensions, and the second initial state (an
    already-repaired pack that never held d). *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check int)
        "reachable states" 36 (Checker.reachable_count sys))

(** The advertisement's sole gate really is a gate: no reachable state
    advertises possession of a digest whose index entry points past the end of
    the data file (consensus_pack.rs:1241). *)
let advertisement_is_bounded () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "no out-of-bounds advertisement is reachable" false
        (Checker.satisfiable sys
           (Formula.And (f Advertised_yes, Formula.Not (f In_bounds_d)))))

(** The fetch's recheck really is a gate: no reachable state answers for d
    while the pack does not hold d's preimage (consensus_pack.rs:1261-1263). *)
let answer_implies_payload () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "no answer for d without d's preimage is reachable" false
        (Checker.satisfiable sys
           (Formula.And (f Answered_d, Formula.Not (f Holds_d)))))

(** The accrue really is the sole writer: no reachable state has a bucket
    entry the filter would reject (index.rs:770). *)
let entry_implies_filter_bit () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "no bucket entry with an unset bloom bit is reachable" false
        (Checker.satisfiable sys
           (Formula.And (f Index_has_d, Formula.Not (f Filter_admits_d)))))

(** The premise of the whole family is reachable: the repair leaves d's index
    entry over an offset that no longer holds d's preimage
    (consensus_pack.rs:680-684, :1258-1260). *)
let dangling_entry_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "a dangling index entry for d is reachable" true
        (Checker.satisfiable sys (f Dangling_d)))

(** Nothing the pristine archive serves ever poisons an exchange: the recheck
    stops the substituted record before it reaches the wire. *)
let no_poisoned_exchange_pristine () =
  with_sys (fun sys ->
      Alcotest.(check bool) "no poisoned exchange is reachable pristine" false
        (Checker.satisfiable sys (f Poisoned)))

(** R2 contingency for [K_V1 holds(v,preimage(g))]: the requester's knowledge
    is not rigid - there are reachable states where it does not hold. *)
let requester_knowledge_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "K_V1 holds(v,g) fails somewhere reachable" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Holds_g)))))

(** R2 non-singleton class for [K_V1 holds(v,preimage(g))]: at a state where
    the requester kept g, it does NOT know that d's index entry is sound. That
    is only possible because another reachable state shares its view - the
    repaired-and-recycled archive, whose answer carrying g alone is
    indistinguishable from the second initial state's. *)
let requester_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "the V1-view class at a kept-g state holds more than one state" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Kept_g,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Dangling_d))) ))))

(** R2 contingency for [K_V0 holds(v,preimage(d))]: the archive's knowledge of
    its own payload is not rigid. *)
let archive_knowledge_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool) "K_V0 holds(v,d) fails somewhere reachable" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V0, f Holds_d)))))

(** R2 non-singleton class for [K_V0 holds(v,preimage(d))]: at a state where
    the archive answered for d, it does not know that no repair has happened -
    a pre-repair pack and a post-repair pack that re-saved d produce the same
    index answer, the same file length and the same answer trace. *)
let archive_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "the V0-view class at an answered-d state holds more than one state"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Answered_d,
                Formula.Not (Formula.K (Validator.V0, Formula.Not (f Healed)))
              ))))

(** R3 ignorance witness, first half: a reachable state where the archive
    advertises possession, really does hold d's preimage, and still does not
    know it - the advertisement never read the bytes. *)
let advertisement_ignorance_witness_true_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "an advertisement over a payload the archive holds but does not know \
         is reachable"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Advertised_yes,
                Formula.And
                  (f Holds_d, Formula.Not (Formula.K (Validator.V0, f Holds_d)))
              ))))

(** R3 ignorance witness, second half: the state that makes the first half
    ignorance rather than knowledge - the same advertisement over a recycled
    offset that does not hold d's preimage. *)
let advertisement_ignorance_witness_false_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "an advertisement over an offset that does not hold d is reachable"
        true
        (Checker.satisfiable sys
           (Formula.And (f Advertised_yes, Formula.Not (f Holds_d)))))

(** The filter is genuinely not authoritative: a digest that no bucket ever
    held survives it (index.rs:775-782, bloom.rs:65-95). *)
let filter_false_positive_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a bloom false positive for a never-saved digest is reachable" true
        (Checker.satisfiable sys
           (Formula.And (f Filter_admits_q, Formula.Not (f Index_has_q)))))

let () =
  Alcotest.run "archive_digest_lookup"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Archive_digest_lookup_statements.name `Quick
              (prove_one st))
          Archive_digest_lookup_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "advertisement-is-bounded" `Quick
            advertisement_is_bounded;
          Alcotest.test_case "answer-implies-payload" `Quick
            answer_implies_payload;
          Alcotest.test_case "entry-implies-filter-bit" `Quick
            entry_implies_filter_bit;
          Alcotest.test_case "dangling-entry-is-reachable" `Quick
            dangling_entry_is_reachable;
          Alcotest.test_case "no-poisoned-exchange-pristine" `Quick
            no_poisoned_exchange_pristine;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "requester-knowledge-is-contingent" `Quick
            requester_knowledge_is_contingent;
          Alcotest.test_case "requester-view-class-is-not-a-singleton" `Quick
            requester_view_class_is_not_a_singleton;
          Alcotest.test_case "archive-knowledge-is-contingent" `Quick
            archive_knowledge_is_contingent;
          Alcotest.test_case "archive-view-class-is-not-a-singleton" `Quick
            archive_view_class_is_not_a_singleton;
          Alcotest.test_case "advertisement-ignorance-witness-true-side" `Quick
            advertisement_ignorance_witness_true_side;
          Alcotest.test_case "advertisement-ignorance-witness-false-side" `Quick
            advertisement_ignorance_witness_false_side;
          Alcotest.test_case "filter-false-positive-is-reachable" `Quick
            filter_false_positive_is_reachable;
        ] );
    ]
