(** Pristine-model suite for the ARCHIVE-EPOCH-IMPORT family.

    Three groups:

    - [proofs] - every statement proves on the pristine interpreted system,
      through [prove_nonvacuous], so a statement whose antecedent were
      unreachable would fail here rather than pass vacuously;
    - [sanity] - the reachable set stays inside the stated bound, each gate's
      forbidden configuration is unsatisfiable, and - the other half of the
      same coin - the configurations the model must NOT be missing (the
      pristine unlink window, the legacy v0 stream branch) are satisfiable, so
      S2 and S3 are not true by omission;
    - [contingency] - R2/R3 discharge. For the one positive [K] conjunct
      ([K_v(holds(w, start..final))]) both the "not collapsed" probe and the
      "view class is not a singleton" probe; for the [~K] conjunct the explicit
      ignorance witness at a published state. *)

open Telcoin_epistemic
open Archive_epoch_import_model

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
        (st.Archive_epoch_import_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Archive_epoch_import_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Archive_epoch_import_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The reachable set stays inside the product bound the family scopes itself
    to: seven initial states whose runs are at most five pipeline stages long,
    plus the already-held run, whose two stages carry the live reader/cache
    sub-model (2 cache x 3 reader states), i.e. 7*5 + 2*2*3 = 47. The exact
    pristine count is 40. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        ("reachable_count = "
        ^ Int.to_string (Checker.reachable_count sys)
        ^ " <= 47")
        true
        (Int.equal (Int.min (Checker.reachable_count sys) 47)
           (Checker.reachable_count sys)))

(** Assert a formula is unsatisfiable on the pristine model. *)
let forbidden label g () =
  with_sys (fun sys ->
      Alcotest.(check bool) label false (Checker.satisfiable sys g))

(** Assert a formula is satisfiable on the pristine model. *)
let reachable label g () =
  with_sys (fun sys ->
      Alcotest.(check bool) label true (Checker.satisfiable sys g))

(** The publish-time equality of consensus.rs:492-497: no state has a published
    pack whose sender held only a prefix of the epoch. *)
let short_chain_never_published =
  forbidden "a short chain is never published"
    (Formula.And (f Published, Formula.Not (f Peer_holds_full_epoch)))

(** The batch bound of consensus_pack.rs:1466-1468 and :1587-1590: the buffered
    set never exceeds the cap, on either stream version. *)
let buffer_never_overruns =
  forbidden "the buffered batch set never exceeds the cap" (f Buffer_over_cap)

(** The short circuit of consensus.rs:458-464: the already-held branch never
    unlinks the canonical directory. *)
let already_held_never_unlinks =
  forbidden "an already-held epoch is never unlinked"
    (Formula.And (f Redundant_import, f Epoch_dir_absent))

(** ... and therefore no reader of that epoch is ever answered with an open
    error on the pristine model. *)
let reader_never_errors = forbidden "no reader errors" (f Reader_failed)

(** The model is NOT rigged so that the unlink window exists only under a
    mutation: the incomplete-pack initial states take the
    [if std::fs::exists(&base_dir)] branch at consensus.rs:513 with no mutation
    applied. *)
let pristine_window_exists =
  reachable "the pristine model does contain the remove+rename window"
    (f Epoch_dir_absent)

(** The legacy v0 decoder branch is live in the pristine model, so S3's
    restriction of its second conjunct to v1 is a real restriction and the
    mutation's non-repair by the v0 counter is checkable. *)
let legacy_branch_exists =
  reachable "the legacy v0 stream branch is reachable"
    (Formula.And (f Stream_in_progress, Formula.Not (f Stream_is_v1)))

(** A peer that declares an over-cap batch count really is rejected: the state
    where the v1 flood is refused exists rather than being unreachable. *)
let over_cap_declaration_reachable =
  reachable "an over-cap v1 declaration is reachable"
    (Formula.And (f Stream_is_v1, f Declares_over_cap))

(** R2, half one: the positive [K] is contingent, not collapsed - there are
    reachable states at which [v] does NOT know the peer held the whole epoch
    (every state before the publish-time equality has run). *)
let knowledge_is_contingent =
  reachable "K_v(holds(w, start..final)) is not everywhere true"
    (Formula.Not (Formula.K (Validator.V0, f Peer_holds_full_epoch)))

(** R2, half two: at a published state - the operative state of the positive
    [K] - [V0]'s view class is not a singleton. [holds(w, final+1)] is false at
    the {!initial_peer_exact} published state, so [v] could only fail to know
    its negation if another reachable state shares [v]'s view and satisfies it:
    that state is {!initial_peer_ahead}'s published state. *)
let view_class_not_singleton =
  reachable "at a published state V0's view class has a second member"
    (Formula.And
       ( f Published,
         Formula.Not
           (Formula.K (Validator.V0, Formula.Not (f Peer_holds_beyond_epoch)))
       ))

(** R2, strengthened: the previous probe finds ONE published state with a
    second class member; this one shows it of EVERY published state. All four
    published states of the pristine model (two in the fresh-directory branch,
    two in the incomplete-pack branch) pair an exactly-at-the-boundary peer
    with an ahead-of-the-boundary peer, so no operative state of the positive
    [K] has a singleton view class. *)
let every_published_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "every published state's V0 class has a second member" true
        (Checker.valid sys
           (Formula.Ag
              (Formula.Implies
                 ( f Published,
                   Formula.Not
                     (Formula.K
                        ( Validator.V0,
                          Formula.Not (f Peer_holds_beyond_epoch) )) )))))

(** R3: the explicit ignorance witness for [~K_v(holds(w, final+1))]. At a
    published state [v] knows neither that the peer is past the epoch boundary
    nor that it is not, because the responder streams only up to the requested
    final number and the two peers put identical bytes on the wire. *)
let ignorance_witness =
  reachable "at a published state V0 knows neither holds(w, final+1) nor its negation"
    (Formula.And
       ( f Published,
         Formula.And
           ( Formula.Not (Formula.K (Validator.V0, f Peer_holds_beyond_epoch)),
             Formula.Not
               (Formula.K
                  (Validator.V0, Formula.Not (f Peer_holds_beyond_epoch))) ) ))

(** Both truth values of the hidden operand are reachable AT a published state,
    which is what makes the pair above a genuine pair. *)
let both_holdings_publish_ahead =
  reachable "a published state with a peer past the boundary"
    (Formula.And (f Published, f Peer_holds_beyond_epoch))

(** The other member of that pair. *)
let both_holdings_publish_exact =
  reachable "a published state with a peer exactly at the boundary"
    (Formula.And (f Published, Formula.Not (f Peer_holds_beyond_epoch)))

let () =
  Alcotest.run "archive_epoch_import"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Archive_epoch_import_statements.name `Quick
              (prove_one st))
          Archive_epoch_import_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "short-chain-never-published" `Quick
            short_chain_never_published;
          Alcotest.test_case "buffer-never-overruns" `Quick
            buffer_never_overruns;
          Alcotest.test_case "already-held-never-unlinks" `Quick
            already_held_never_unlinks;
          Alcotest.test_case "reader-never-errors" `Quick reader_never_errors;
          Alcotest.test_case "pristine-window-exists" `Quick
            pristine_window_exists;
          Alcotest.test_case "legacy-branch-exists" `Quick legacy_branch_exists;
          Alcotest.test_case "over-cap-declaration-reachable" `Quick
            over_cap_declaration_reachable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "knowledge-is-contingent" `Quick
            knowledge_is_contingent;
          Alcotest.test_case "view-class-not-singleton" `Quick
            view_class_not_singleton;
          Alcotest.test_case "every-published-class-not-singleton" `Quick
            every_published_class_not_singleton;
          Alcotest.test_case "ignorance-witness" `Quick ignorance_witness;
          Alcotest.test_case "published-with-peer-ahead" `Quick
            both_holdings_publish_ahead;
          Alcotest.test_case "published-with-peer-exact" `Quick
            both_holdings_publish_exact;
        ] );
    ]
