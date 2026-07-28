(** The stream_slot_tenure family proves on the pristine
    {!Stream_slot_tenure_model} through [prove_nonvacuous] (so every antecedent
    is checked reachable too), the reachable graph stays in its justified band,
    the two structural invariants the consume-on-open gate enforces are
    genuinely unreachable rather than merely unasserted, and the epistemic layer
    is real partial information on both sides:

    - the responder V0's ignorance of the requester's disposition is witnessed
      by a concrete reachable pair - one clean reservation from a peer that will
      never come back, one from a peer that may - that share V0's view exactly,
      and it is honestly bounded: V0 DOES learn the disposition the moment the
      peer acts, and that is asserted here too;
    - the requester V1's knowledge that its reservation has been consumed is
      contingent (false at every held state) and its view class at a served
      state is NOT a singleton - V1 cannot see when the responder's 15s cleanup
      interval next fires, and the test pins exactly that. *)

open Telcoin_epistemic
open Stream_slot_tenure_model

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
        (st.Stream_slot_tenure_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Stream_slot_tenure_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Stream_slot_tenure_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The reservation is gone from the responder's map. *)
let released = Formula.Not (f Slot_reserved)

(** The hidden frozen disposition: this requester never comes back. *)
let silent = f Requester_gone_silent

(** A [satisfiable] case with its own label. *)
let sat_case label want formula () =
  with_sys (fun sys ->
      Alcotest.(check bool) label want (Checker.satisfiable sys formula))

(** Crude product bound: 2 dispositions x 2 slot values x 2 ages x 4 service
    values x 2 charge values x 3 loop phases = 192. The pristine reachable set
    is 39: the consume-on-open gate kills every (held, served) combination,
    [Svc_double] is unreachable without the mutation, a replayed admission is
    always charged, and the abandoned branch only ever idles. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 60))

(** The consume-on-open gate (mod.rs:1843-1845): a reservation that has been
    served is no longer in the map, so no reachable state is both held and
    served. This is the invariant {!Stream_slot_tenure_model.Non_consuming_open}
    deletes. *)
let no_held_served_state () =
  sat_case "reserved /\\ served is unreachable" false
    (Formula.And (f Slot_reserved, f Served_once))
    ()

(** One admission never yields two epoch-pack transfers. *)
let no_double_serve () =
  sat_case "double_served is unreachable" false (f Served_twice) ()

(** A replay is by construction an open of an already-served admission, so it
    can never appear without the serve it replays. *)
let replay_implies_serve () =
  sat_case "replayed without served is unreachable" false
    (Formula.And (f Reopened_after_serve, Formula.Not (f Served_once)))
    ()

(** The 15s cleanup arm is a timer of the same [tokio::select!]
    (mod.rs:1426, :1442-1444), not a queued event: no amount of peer traffic
    starves it, so every path reaches the tick. This is what makes the family's
    [Af] claims structural rather than an unquoted fairness axiom. *)
let cleanup_tick_unstarvable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF cleanup_next" true
        (Checker.valid sys (Formula.Af (f Cleanup_due))))

(** Every run out of an accepted admission reaches a state in which the slot is
    free, on every path and under every peer strategy the model allows. *)
let release_is_inevitable () =
  with_sys (fun sys ->
      Alcotest.(check bool) "AF ~reserved" true
        (Checker.valid sys (Formula.Af released)))

(** R2/S3-C, contingency: the positive [K_V1 ~reserved(p,d)] has not collapsed
    into plain truth - it fails at every state where the reservation is still
    held, which is exactly where the peer must not be credited with it. *)
let requester_k_contingent () =
  sat_case "EF ~K_V1(~reserved): knowledge did not collapse" true
    (Formula.Not (Formula.K (Validator.V1, released)))
    ()

(** R2/S3-C, non-singleton view class: at a served state where the responder's
    next loop step is NOT the cleanup tick, V1 still does not know that. The
    cleanup interval's alignment is the responder's (mod.rs:1426), so V1's view
    class at a served state contains at least two reachable states - if it were
    a singleton this would be false and [K_V1 ~reserved] would be worthless. *)
let requester_class_not_singleton () =
  sat_case
    "served /\\ ~cleanup_next /\\ ~K_V1(~cleanup_next): V1's class is not a \
     singleton"
    true
    (Formula.conj
       [
         f Served_once;
         Formula.Not (f Cleanup_due);
         Formula.Not (Formula.K (Validator.V1, Formula.Not (f Cleanup_due)));
       ])
    ()

(** R3/S1-B, ignorance witness (active side): at a clean reservation from a peer
    that MAY still open the stream, V0 cannot rule out that the peer is gone -
    which is only possible because an abandoned reservation with the identical
    responder-side view is reachable. *)
let responder_cannot_rule_out_abandonment () =
  sat_case
    "clean /\\ ~abandoned /\\ ~K_V0(~abandoned): the abandoned twin is reachable"
    true
    (Formula.conj
       [
         Stream_slot_tenure_statements.clean_reservation;
         Formula.Not silent;
         Formula.Not (Formula.K (Validator.V0, Formula.Not silent));
       ])
    ()

(** R3/S1-B, ignorance witness (abandoned side): at a clean reservation from a
    peer that is in fact gone, V0 does not know it - the live twin shares its
    view. The two witnesses together are the concrete reachable pair R3 asks
    for. *)
let responder_cannot_detect_abandonment () =
  sat_case
    "clean /\\ abandoned /\\ ~K_V0(abandoned): the live twin is reachable" true
    (Formula.conj
       [
         Stream_slot_tenure_statements.clean_reservation;
         silent;
         Formula.Not (Formula.K (Validator.V0, silent));
       ])
    ()

(** The scoping of S1 conjunct B is honest, not a blanket blindness claim: once
    the peer acts, the responder's view carries the act and the class collapses
    onto the live branch, so V0 DOES know the peer was not gone. The ignorance
    is claimed exactly where the responder has learned nothing. *)
let responder_learns_once_peer_acts () =
  sat_case "served /\\ K_V0(~abandoned): the ignorance is scoped, not blanket"
    true
    (Formula.And (f Served_once, Formula.K (Validator.V0, Formula.Not silent)))
    ()

(** The Mild penalty is charged on an open that finds no entry
    (handler.rs:1139-1149, error/network.rs:189-191), and that is not the same
    thing as a replay: a peer whose reservation the cleanup evicted while it was
    opening the stream is charged too. The model carries that state rather than
    collapsing charge onto replay, which is what keeps S3 conjunct B a claim
    about replays instead of a definition. *)
let charge_without_replay_reachable () =
  sat_case "charged /\\ ~replayed is reachable" true
    (Formula.And (f Penalty_charged, Formula.Not (f Reopened_after_serve)))
    ()

let () =
  Alcotest.run "stream_slot_tenure"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Stream_slot_tenure_statements.name `Quick
              (prove_one st))
          Stream_slot_tenure_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "consume-on-open" `Quick no_held_served_state;
          Alcotest.test_case "at-most-one-serve" `Quick no_double_serve;
          Alcotest.test_case "replay-implies-serve" `Quick replay_implies_serve;
          Alcotest.test_case "cleanup-tick-unstarvable" `Quick
            cleanup_tick_unstarvable;
          Alcotest.test_case "release-inevitable" `Quick release_is_inevitable;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "requester-k-contingent" `Quick
            requester_k_contingent;
          Alcotest.test_case "requester-class-not-singleton" `Quick
            requester_class_not_singleton;
          Alcotest.test_case "responder-cannot-rule-out-abandonment" `Quick
            responder_cannot_rule_out_abandonment;
          Alcotest.test_case "responder-cannot-detect-abandonment" `Quick
            responder_cannot_detect_abandonment;
          Alcotest.test_case "responder-learns-once-peer-acts" `Quick
            responder_learns_once_peer_acts;
          Alcotest.test_case "charge-without-replay" `Quick
            charge_without_replay_reachable;
        ] );
    ]
