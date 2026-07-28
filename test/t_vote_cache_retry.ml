(** The VOTE_CACHE_RETRY family (S1, S2, S3) proves on the pristine
    {!Vote_cache_retry_model} through [prove_nonvacuous] (so each antecedent is
    also checked reachable), the reachable graph stays in its justified band,
    the two states the deleted gates forbid are unreachable-by-construction
    rather than merely unasserted, and the epistemic layer is genuinely
    partial-information: the single positive knowledge operand is contingent AND
    its view class is proved non-singleton, and each ignorance conjunct has a
    reachable witness pair exhibited on both sides. *)

open Telcoin_epistemic
open Vote_cache_retry_model

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
        (st.Vote_cache_retry_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Vote_cache_retry_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Vote_cache_retry_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The operative state of the family's single positive knowledge claim: i holds
    the missing-parent hint, its vote task is alive and nothing is in flight. *)
let positive_k_operative =
  Formula.And
    ( f Author_holds_hint,
      Formula.And (f Vote_task_live, Formula.Not (f Vote_request_in_flight)) )

(* Loose product bound: 5 cache slots x 2 hint values x 2 request states x 3
   task states x 2 epoch skews x 2 peer-reply values = 240. The pristine
   reachable set is exactly 44: a request is only in flight while the vote task
   is live, the hint is only held once the voter has reported a gap (which needs
   the epochs aligned), and the epoch skew never reappears once crossed. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 240))

(* The exact pristine count, pinned so that a silent change to the transition
   relation cannot pass unnoticed. *)
let reachable_exact () =
  with_sys (fun sys ->
      Alcotest.(check int) "pristine reachable count" 44
        (Checker.reachable_count sys))

(* What the re-issue gate at handler.rs:519-534 forbids: a cached
   MissingParents(M) entry never coexists with a dead vote task, because the
   empty retry is answered with M rather than with WrongNumberOfParents. This is
   exactly the state No_empty_parent_reissue makes reachable. *)
let cached_hint_never_kills_the_task () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (cached = MissingParents(M) /\\ dead)" false
        (Checker.satisfiable sys
           (Formula.And (f Cache_missing_hint, f Vote_task_dead))))

(* What the classification arm at message.rs:331-335 forbids: while the voter is
   exactly one epoch behind, its cache slot for the author never holds a final
   Error. This is exactly the state No_one_epoch_ahead_arm makes reachable. *)
let boundary_race_never_frozen_final () =
  with_sys (fun sys ->
      Alcotest.(check bool) "not EF (epoch(j)+1 = epoch(h) /\\ cached = Error)"
        false
        (Checker.satisfiable sys
           (Formula.And (f Voter_epoch_behind, f Cache_final_answer))))

(* R2, half one - the positive operand K_V1(cached = MissingParents(M)) is
   contingent: its complement is reachable, so the knowledge did not collapse
   into plain truth under the view partition. *)
let k_v1_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF ~K_v1(cached = MissingParents(M)): knowledge did not collapse" true
        (Checker.satisfiable sys
           (Formula.Not (Formula.K (Validator.V1, f Cache_missing_hint)))))

(* R2, half two - the V1-view class at the operative state is NOT a singleton.
   At an operative state where j has not yet answered author k, i does not know
   that j has not answered author k: only another reachable state sharing i's
   view (its hint, its task, its outstanding request) and satisfying
   replied(j,k) can make this satisfiable, which is precisely the non-singleton
   evidence. That other author's act is invisible to i - the vote response
   carries nothing about it. *)
let k_v1_class_not_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (hint_i /\\ live /\\ ~evaluating /\\ ~K_v1(~replied(j,k))): class \
         has >= 2 reachable states"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( positive_k_operative,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Peer_k_answered)))
              ))))

(* R3 for S2 conjunct C: a dead vote task at a voter that IS one epoch behind,
   where i cannot rule the skew in. *)
let author_blind_to_the_skew () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "EF (dead /\\ epoch(j)+1 = epoch(h) /\\ ~K_v1(epoch(j)+1 = epoch(h)))"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Vote_task_dead,
                Formula.And
                  ( f Voter_epoch_behind,
                    Formula.Not (Formula.K (Validator.V1, f Voter_epoch_behind))
                  ) ))))

(* R3 for S2 conjunct C, the first half of the witness pair: the task dies while
   the voter is one epoch behind (six sends of network/mod.rs:474-484 all
   meeting a behind voter, then :487-488 and certifier.rs:185-190). *)
let dead_with_a_behind_voter () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (dead /\\ epoch(j)+1 = epoch(h))" true
        (Checker.satisfiable sys
           (Formula.And (f Vote_task_dead, f Voter_epoch_behind))))

(* R3 for S2 conjunct C, the second half: the task dies at an aligned voter (the
   max_header_delay timeout at handler.rs:582-586, or a header-level rejection).
   i's view is identical in both, which is what makes the ignorance real. *)
let dead_with_an_aligned_voter () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (dead /\\ ~(epoch(j)+1 = epoch(h)))" true
        (Checker.satisfiable sys
           (Formula.And (f Vote_task_dead, Formula.Not (f Voter_epoch_behind)))))

(* R3 for S2 conjunct D: having cached a final Error, the voter cannot tell that
   it has terminated the author's vote task. *)
let voter_blind_to_the_kill () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (cached = Error /\\ dead /\\ ~K_v0(dead))" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Cache_final_answer,
                Formula.And
                  ( f Vote_task_dead,
                    Formula.Not (Formula.K (Validator.V0, f Vote_task_dead)) )
              ))))

(* The twin that makes that class non-singleton: the same cached Error with a
   LIVE vote task, reached because the proposer re-proposes the stored header
   (proposer.rs:802-822) and the certifier spawns a fresh task. *)
let final_cache_with_a_live_task () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (cached = Error /\\ live)" true
        (Checker.satisfiable sys
           (Formula.And (f Cache_final_answer, f Vote_task_live))))

(* The witness behind S3 conjunct A: author k really is answered while author i's
   evaluation slot is held. Under Single_shared_vote_lock this state is still
   reachable (k first, i afterwards) - what that mutation destroys is the UNTIL,
   which is why conjunct A is stated with Eu and not with Ef. *)
let peer_answered_while_slot_held () =
  with_sys (fun sys ->
      Alcotest.(check bool) "EF (evaluating(j,i,h) /\\ replied(j,k))" true
        (Checker.satisfiable sys
           (Formula.And (f Vote_request_in_flight, f Peer_k_answered))))

let () =
  Alcotest.run "vote_cache_retry"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Vote_cache_retry_statements.name `Quick
              (prove_one st))
          Vote_cache_retry_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "reachable-exact" `Quick reachable_exact;
          Alcotest.test_case "cached-hint-never-kills-the-task" `Quick
            cached_hint_never_kills_the_task;
          Alcotest.test_case "boundary-race-never-frozen-final" `Quick
            boundary_race_never_frozen_final;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "k-v1-contingent" `Quick k_v1_contingent;
          Alcotest.test_case "k-v1-class-not-singleton" `Quick
            k_v1_class_not_singleton;
          Alcotest.test_case "author-blind-to-the-skew" `Quick
            author_blind_to_the_skew;
          Alcotest.test_case "dead-with-a-behind-voter" `Quick
            dead_with_a_behind_voter;
          Alcotest.test_case "dead-with-an-aligned-voter" `Quick
            dead_with_an_aligned_voter;
          Alcotest.test_case "voter-blind-to-the-kill" `Quick
            voter_blind_to_the_kill;
          Alcotest.test_case "final-cache-with-a-live-task" `Quick
            final_cache_with_a_live_task;
          Alcotest.test_case "peer-answered-while-slot-held" `Quick
            peer_answered_while_slot_held;
        ] );
    ]
