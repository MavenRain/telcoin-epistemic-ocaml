(** The three ARCHIVE-PACK-HEAL statements prove on the pristine model through
    [prove_nonvacuous] (so each antecedent is also checked reachable), the
    reachable graph stays in its justified band, the three gates the family is
    about really do make their forbidden states unreachable, and the epistemic
    layer is genuinely partial-information:

    - the node's knowledge that the pack's index fell behind its data file is
      contingent (it fails somewhere reachable) and its operative view class is
      not a singleton;
    - that knowledge is not a relabelling of the node's own signal: the data
      can already be ahead of the index while the error is still sitting
      uncollected on the watch, so the view underdetermines the fact in the
      other direction;
    - the two failure routes that publish the same [PackError] - the latching
      torn write and the non-latching index-save failure - are both reachable
      and share the node's view, which is the concrete witness pair for the
      latch ignorance;
    - the repair's dropped output has both fates reachable at one and the same
      post-reopen view, which is the witness pair for the peer-possession
      ignorance;
    - and two R5 anchors. The repair's phase A really can grow a file on the
      PRISTINE model, so S1's [batch-final-above-header] guard is load-bearing
      and the statement is not quietly claiming more than the clamp buys. And
      the repair really can leave the position index disagreeing with the data
      file, so S2's conjunct B claims the digest halves of the consistency
      check and no more. *)

open Telcoin_epistemic
open Archive_pack_heal_model

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
        (st.Archive_pack_heal_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Archive_pack_heal_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Archive_pack_heal_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Justified bound. The lifecycle is four phases. While the writer runs, the
   four file lengths are determined by the save history and take only seven
   shapes (nothing saved; one saved; two saved; and, for each of the two
   failing-save positions, the tracked-lengths-behind and the
   tracked-lengths-caught-up variant), so that phase is at most
   7 x latch 2 x signal 3 x holder 2 = 84. A crash maps each of those seven
   shapes through at most five damage patterns, so there are at most
   7 x 5 x holder 2 = 70 at-rest configurations, and each reopen phase is a
   function of one of them: 70 healed and 70 static. Bound 84 + 210 = 294.
   The actual pristine reachable set is 64 states (64 under No_shrink_clamp,
   84 under No_static_consistency_gate, 60 under No_write_failure_latch).

   That is above the 50 the authoring contract asks for, and the extra came
   from a deliberate faithfulness choice rather than from slack: modelling the
   index-save failure that leaves the digest indexes CAUGHT UP with the data
   while only the position index is short (consensus_pack.rs:1010-1012 having
   already run inside the batch loop before the position save at :1060-1062
   fails) costs 15 states and refutes nothing, but without it the family would
   be omitting the commoner of the two non-latching failure shapes. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in the justified band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 294))

(** One [satisfiable] assertion on the pristine model. *)
let sat_is label expected formula () =
  with_sys (fun sys ->
      Alcotest.(check bool) label expected (Checker.satisfiable sys formula))

(* S1's gate: with the batch digest index still tracking a real length, no
   reopen ever leaves the data file longer than it found it (the clamp at
   consensus_pack.rs:713-716 plus phase A's two bounded branches, :675-678). *)
let no_guarded_extension =
  sat_is
    "EF (heal-ran /\\ batch-index-survived /\\ heal-extended) is unreachable"
    false
    (Formula.conj [ f Heal_ran; f Batch_index_survived; f Heal_extended ])

(* S2's gate: a read-only open never lets through a pack whose three files
   disagree (consensus_pack.rs:894-902 over :640-662). *)
let no_inconsistent_static_open =
  sat_is "EF (open-static-ok /\\ ~files-consistent) is unreachable" false
    (Formula.And (f Static_open_served, Formula.Not (f Files_agree)))

(* S2's other half: the append open never REFUSES, it repairs, and its
   epilogue always reconciles both digest indexes with the healed length
   (consensus_pack.rs:721-726). *)
let append_open_reconciles_digests =
  sat_is "EF (heal-ran /\\ ~digest-lengths-match) is unreachable" false
    (Formula.And (f Heal_ran, Formula.Not (f Digest_lengths_match)))

(* S3's underlying invariant: no route to [tx_error.send_replace]
   (consensus_pack.rs:141-143) leaves the position index caught up with the
   data file, because every failing save has already appended
   (:1048-1051) before it indexes (:1056-1062). *)
let no_error_without_an_index_gap =
  sat_is "EF (error-seen /\\ ~data-ahead-of-index) is unreachable" false
    (Formula.And (f Error_seen, Formula.Not (f Data_ahead_of_index)))

(* R2, part 1, for S3's positive K: the knowledge is contingent, not
   collapsed - somewhere reachable the node does not know the index fell
   behind. *)
let k_contingent =
  sat_is "EF ~K_v0(data-ahead-of-index): knowledge did not collapse" true
    (Formula.Not (Formula.K (Validator.V0, f Data_ahead_of_index)))

(* R2, part 2, for S3's positive K: the operative view class is NOT a
   singleton. At a state where the node has collected an error, asserting that
   it does not know the pack is unlatched forces a second reachable state in
   the same [V0] view class - same collected signal, same indexed count,
   opposite latch. *)
let k_class_not_singleton =
  sat_is
    "EF (error-seen /\\ ~K_v0(~pack-latched)): class is not a singleton" true
    (Formula.And
       ( f Error_seen,
         Formula.Not (Formula.K (Validator.V0, Formula.Not (f Pack_latched)))
       ))

(* R1 evidence for S3's positive K: the operand is not a relabelling of the
   node's own view. The watch can already hold a published error the node has
   not collected ([get_error] is only consulted at the head of the next
   request, consensus_pack.rs:368), so the data is ahead of the index while
   the node's view is still the clean one. *)
let k_operand_is_not_the_signal =
  sat_is "EF (data-ahead-of-index /\\ ~error-seen): the view underdetermines it"
    true
    (Formula.And (f Data_ahead_of_index, Formula.Not (f Error_seen)))

(* R3 witness pair for S3's latch ignorance, side A: the torn data write, the
   route that DOES latch (archive/pack.rs:269). *)
let latch_witness_latched =
  sat_is "EF (error-seen /\\ pack-latched)" true
    (Formula.And (f Error_seen, f Pack_latched))

(* R3 witness pair, side B: the index-save failure at consensus_pack.rs:
   1056-1058 / :1060-1062, an [IndexAppend] error that publishes on the same
   watch and explicitly does NOT latch (archive/pack.rs:270-274). *)
let latch_witness_unlatched =
  sat_is "EF (error-seen /\\ ~pack-latched)" true
    (Formula.And (f Error_seen, Formula.Not (f Pack_latched)))

(* R3 witness pair for S1's possession ignorance, side A: the repair dropped
   an output the peer had already been streamed
   ([get_partial_epoch_stream], consensus.rs:587-602). *)
let holder_witness_holds =
  sat_is "EF (heal-ran /\\ heal-dropped /\\ holds(w, n))" true
    (Formula.conj [ f Heal_ran; f Heal_dropped_output; f Peer_holds_epoch_bytes ])

(* R3 witness pair, side B: it dropped an output nobody ever asked for. *)
let holder_witness_not_holds =
  sat_is "EF (heal-ran /\\ heal-dropped /\\ ~holds(w, n))" true
    (Formula.conj
       [
         f Heal_ran;
         f Heal_dropped_output;
         Formula.Not (f Peer_holds_epoch_bytes);
       ])

(* ...and the pair really does share the reopened node's view: at a state
   where the repair dropped an output the node can rule out neither fate,
   which is only possible if reachable states with both possessions carry the
   same four healed lengths. [trunc_and_heal] reports nothing about what it
   trimmed (consensus_pack.rs:665-670), so they do. *)
let holder_pair_shares_the_view =
  sat_is
    "EF (heal-ran /\\ heal-dropped /\\ ~K_v0(~holds(w, n))): the fates are \
     indistinguishable"
    true
    (Formula.conj
       [
         f Heal_ran;
         f Heal_dropped_output;
         Formula.Not
           (Formula.K (Validator.V0, Formula.Not (f Peer_holds_epoch_bytes)));
       ])

(* ...and in the other direction too, so the node cannot conclude the bytes
   are safe elsewhere either. *)
let holder_pair_shares_the_view_positive =
  sat_is
    "EF (heal-ran /\\ heal-dropped /\\ ~K_v0(holds(w, n))): both directions of \
     the ignorance"
    true
    (Formula.conj
       [
         f Heal_ran;
         f Heal_dropped_output;
         Formula.Not (Formula.K (Validator.V0, f Peer_holds_epoch_bytes));
       ])

(* R5 anchor for S2. The PRISTINE repair does NOT restore full three-file
   agreement: both index truncations in the walk-back are guarded by
   [idx != start_idx] (consensus_pack.rs:695, :706), so a position index
   holding exactly one entry is left untouched when that entry does not fit
   the surviving data, and the clamp at :716 leaves the file where it was. The
   reopened pack then carries an entry claiming an [output_end] past its own
   data file - a pack a later read-only open would refuse. This is why S2's
   conjunct B claims the digest halves only. *)
let append_open_can_leave_the_position_index_stale =
  sat_is
    "EF (heal-ran /\\ ~files-consistent): the repair is NOT gate-idempotent"
    true
    (Formula.And (f Heal_ran, Formula.Not (f Files_agree)))

(* R5 anchor for S1. The PRISTINE repair can grow a data file: when the batch
   digest index is back at the bare header, consensus_pack.rs:675's second
   test fails, control falls to the [else if consensus_final >
   DATA_HEADER_BYTES] branch at :677, and [data.truncate(consensus_final)] runs
   with nothing bounding [consensus_final] by the bytes that survived. So S1's
   [batch-index-survived] guard is not decoration - deleting it makes S1 false
   on the pristine model, which is exactly why the statement carries it. *)
let phase_a_extension_is_reachable =
  sat_is
    "EF (heal-ran /\\ heal-extended): the UNGUARDED shrink-only claim is FALSE"
    true
    (Formula.And (f Heal_ran, f Heal_extended))

let () =
  Alcotest.run "archive_pack_heal"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Archive_pack_heal_statements.name `Quick
              (prove_one st))
          Archive_pack_heal_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "no-guarded-extension" `Quick no_guarded_extension;
          Alcotest.test_case "no-inconsistent-static-open" `Quick
            no_inconsistent_static_open;
          Alcotest.test_case "append-open-reconciles-digests" `Quick
            append_open_reconciles_digests;
          Alcotest.test_case "no-error-without-an-index-gap" `Quick
            no_error_without_an_index_gap;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-contingent" `Quick k_contingent;
          Alcotest.test_case "k-class-not-singleton" `Quick
            k_class_not_singleton;
          Alcotest.test_case "k-operand-is-not-the-signal" `Quick
            k_operand_is_not_the_signal;
          Alcotest.test_case "latch-witness-latched" `Quick
            latch_witness_latched;
          Alcotest.test_case "latch-witness-unlatched" `Quick
            latch_witness_unlatched;
          Alcotest.test_case "holder-witness-holds" `Quick holder_witness_holds;
          Alcotest.test_case "holder-witness-not-holds" `Quick
            holder_witness_not_holds;
          Alcotest.test_case "holder-pair-shares-the-view" `Quick
            holder_pair_shares_the_view;
          Alcotest.test_case "holder-pair-shares-the-view-positive" `Quick
            holder_pair_shares_the_view_positive;
          Alcotest.test_case "phase-a-extension-is-reachable" `Quick
            phase_a_extension_is_reachable;
          Alcotest.test_case "append-open-can-leave-the-position-index-stale"
            `Quick append_open_can_leave_the_position_index_stale;
        ] );
    ]
