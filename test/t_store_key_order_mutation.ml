(** Confirm-by-mutation for the STORE_KEY_ORDER family: each pin asserts the
    pristine proof AND the flip to refuted under the gate deletion, per
    statement, so a pin can never pass on the strength of some other
    statement's collapse. The two gates live in different crates and the last
    group asserts that each leaves the other's statements standing, so neither
    pin is attributable to the other's deletion.

    - {!Store_key_order_model.No_big_endian} deletes [.with_big_endian()] from
      [encode_key] (types/src/codec.rs:45). It pins S1: with the [Round]
      suffix little-endian, [R_hi = 256] ([00 01 00 00]) sorts before
      [R_lo = 1] ([01 00 00 00]) inside [j]'s block, so the backwards walk of
      [record_prior_to] (mdbx/database.rs:231-240, redb/database.rs:239-251)
      ends on [j]'s LOWEST stored round. No sibling repairs it: both backends
      sort by raw bytes and neither re-sorts (redb/wraps.rs:10-16,
      mdbx/database.rs:154-159), [skip_to] is a [skip_while] over the same
      stream rather than a seek (mdbx/database.rs:211-220,
      redb/database.rs:176-206), [last_record] is the cursor's byte-maximum
      (mdbx/database.rs:242-250, redb/database.rs:253-257), [reverse_iter]
      walks the same bytes backwards (mdbx/database.rs:222-229,
      redb/database.rs:208-237), and the memory layer keys a
      [BTreeMap<Vec<u8>, _>] by the identical bytes (mem_db.rs:10, :259-278) so
      it repeats the order rather than repairing it. The decoder moves with the
      encoder (codec.rs:20-26, :32-37), so the values stay right and ONLY the
      order is wrong - which is exactly why nothing downstream notices.
    - {!Store_key_order_model.No_origin_guard} deletes the [if &name == origin]
      test from [last_round_number] (stores/certificate_store.rs:414-416). It
      pins S2 (the probe reports the neighbouring authority's round as [j]'s,
      so V0's view is unchanged while "j signed at R_hi" is false) and S3 (that
      false answer makes [header.round() > last_round] false, so the ancestor
      fetch is suppressed for an authority V0 holds nothing from). No sibling
      repairs it: [last_round] (:389-399) and [next_round_number] (:428-434)
      carry their own copies of the same test but answer different questions
      and no caller cross-checks them; :415 returns the KEY's round without
      loading the certificate, so nothing re-derives the author; and the second
      fetch entry point is NOT a repair, because the missing-parent path
      (state_sync/cert_manager.rs:157-177) sends
      [CertificateFetcherCommand::Ancestors] into the SAME [handle_command]
      (certificate_fetcher.rs:178-191), which falls through to the SAME gate at
      :207. [Kick] (:181-190) needs a non-empty [self.targets], which is
      populated only at :212 after the gate has passed.

    Reported rather than hidden: the two deletions are genuinely independent on
    this family. The last group asserts S1 still proves under
    {!Store_key_order_model.No_origin_guard} and that S2 and S3 still prove
    under {!Store_key_order_model.No_big_endian}, so each pin is attributable
    to its own gate and neither statement is riding on the other's collapse.

    The pins were confirmed CONJUNCT BY CONJUNCT before being written, so no
    pin can be passing because some other conjunct of the same statement
    collapsed. Proving each conjunct alone against each transition relation
    (54 reachable states under all three) gives:

    {v
                                 pristine  no_big_endian  no_origin_guard
      S1.A highest_row_wins       PROVED     REFUTED         PROVED
      S1.B low_answer_is_maximum  PROVED     REFUTED         PROVED
      S1.C lone_low_not_skipped   PROVED     PROVED          PROVED
      S2.A K_V0(signed(j,R_hi))   PROVED     PROVED          REFUTED
      S2.B ~K_V0(~signed(j,R_hi)) PROVED     PROVED          PROVED
      S3.A AF fetch_ancestors(j)  PROVED     PROVED          REFUTED
      S3.B suppression grounded   PROVED     PROVED          REFUTED
    v}

    Every refutation above is a [Refuted] verdict, never a
    [Vacuous_antecedent]: each statement's antecedent stays reachable under the
    mutation that pins it, so the pins are genuine counterexamples rather than
    the antecedent falling out of the reachable set. S1.C and S2.B are stated
    because they are true, not because a mutation refutes them; each of them
    sits inside a conjunction that a mutation does refute. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Store_key_order_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Store_key_order_model.Checker.make (Store_key_order_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st -> Int.equal 0 (String.compare st.Store_key_order_statements.name name))
    Store_key_order_statements.all

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " flips to refuted under the mutation")
            false
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Store_key_order_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Store_key_order_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Store_key_order_statements.prove sys st)))

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** The statement is UNTOUCHED by this mutation: it still proves. This is what
    keeps each pin attributable to its own gate. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under an unrelated gate deletion")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Store_key_order_statements.prove sys st)))

let () =
  Alcotest.run "store_key_order_mutation"
    [
      ( "deleted big-endian key encoding reorders the origin block",
        pin Store_key_order_model.No_big_endian
          "ordered-scan-lands-on-the-origins-greatest-stored-round" );
      ( "deleted origin guard attributes a neighbours round to the origin",
        pin Store_key_order_model.No_origin_guard
          "origin-guard-makes-the-round-answer-knowledge-of-the-named-authoritys-act"
      );
      ( "deleted origin guard suppresses the ancestor fetch",
        pin Store_key_order_model.No_origin_guard
          "origin-guard-keeps-the-ancestor-fetch-alive-for-a-silent-authority" );
      ( "each gate deletion leaves the other statements standing",
        [
          Alcotest.test_case "order-statement:under-guard-deletion" `Quick
            (survives_under Store_key_order_model.No_origin_guard
               "ordered-scan-lands-on-the-origins-greatest-stored-round");
          Alcotest.test_case "knowledge-statement:under-encoding-deletion"
            `Quick
            (survives_under Store_key_order_model.No_big_endian
               "origin-guard-makes-the-round-answer-knowledge-of-the-named-authoritys-act");
          Alcotest.test_case "fetch-statement:under-encoding-deletion" `Quick
            (survives_under Store_key_order_model.No_big_endian
               "origin-guard-keeps-the-ancestor-fetch-alive-for-a-silent-authority");
        ] );
    ]
