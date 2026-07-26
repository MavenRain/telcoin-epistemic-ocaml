(** The GOSSIP-AUTH family (DESIGN family GOSSIP-AUTH, statement #1) proves
    on the pristine {!Gossip_auth_model} through [prove_nonvacuous] (so the
    antecedent is also checked reachable), the reachable graph stays in its
    justified band, the authorized-publisher gate holds (no outsider frame
    is ever accepted), and the epistemic layer is genuinely
    partial-information: for each subscriber the K_i operand is contingent,
    and the card's false-witness pair - a delivery-window state where V0's
    certificate is published yet the subscriber has not received it and
    cannot know publishing happened, colliding with the crash-post-vote
    state where nothing was published - is reachable on both sides. *)

open Telcoin_epistemic

(** Build the pristine system or fail the test on an impossible
    [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Gossip_auth_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Gossip_auth_model.make ())

(** Render a proof error for the assertion message. *)
let error_to_string = function
  | Gossip_auth_model.Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Gossip_auth_model.Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Gossip_auth_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Gossip_auth_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Gossip_auth_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(* Crude product bound: 6 phases x 3 strategies x 3 outsider values x 4
   delay values = 216; the publish-history bits are branch-determined and
   V0/V3 locals are constant, so they add no factor. The actual reachable
   set is 25 states (1 Propose, 2 Vote, 2 Certify, 4 Deliver-R1, 8
   Deliver-R2, 8 Done). *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Gossip_auth_model.Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 64))

(** The knowledge agents: the honest committee subscribers, the only
    validators placed under K in this family. *)
let subscribers = [ Validator.V1; Validator.V2 ]

(** The authorized-publisher gate's invariant on the pristine model: the
    outsider frame [C'] is never accepted by any subscriber
    (consensus.rs:1491-1514) - the non-epistemic safety conjunct of S1
    holds as a plain reachability invariant. *)
let outsider_frame_rejected () =
  with_sys (fun sys ->
      Alcotest.(check bool) "G (AND_i ~delivered_i(C'))" true
        (Gossip_auth_model.Checker.valid sys
           (Formula.Ag
              (Formula.conj
                 (List.map
                    (fun i ->
                      Formula.Not
                        (f (Gossip_auth_model.Delivered
                              (i, Gossip_auth_model.Cert_c_prime))))
                    subscribers)))))

(** Bounded-delay delivery liveness: once V0 publishes [C], every honest
    subscriber inevitably accepts it (the delayed one repaired at the forced
    second deliver phase) - the leads_to conjunct of S1 as a standalone
    progress check. *)
let publish_reaches_all () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "published(C) ~> AND_i delivered_i(C)" true
        (Gossip_auth_model.Checker.valid sys
           (Formula.leads_to
              (f (Gossip_auth_model.Committee_published Gossip_auth_model.Cert_c))
              (Formula.conj
                 (List.map
                    (fun i ->
                      f (Gossip_auth_model.Delivered (i, Gossip_auth_model.Cert_c)))
                    subscribers)))))

(* The single positive K conjunct of S1 is K_i(committee-published C) for
   each subscriber i, so - per contingency - assert its operand is NOT plain
   truth under i's view partition, else the statement would be
   epistemically vacuous: there is a reachable state (the crash-post-vote
   branch, and every pre-publish state) where the publish bit is false, so
   K_i of it fails. *)
let k_contingent i () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        ("EF ~K_" ^ Validator.to_string i
       ^ "(committee-published C): knowledge did not collapse")
        true
        (Gossip_auth_model.Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( i,
                   f (Gossip_auth_model.Committee_published
                        Gossip_auth_model.Cert_c) )))))

(* wcheck false witness (operand-true side): the delivery-window state where
   V0's certificate IS published (Cooperate + delay-i) yet subscriber i has
   NOT accepted it, and i does not know publishing happened - because that
   view collides with the crash-post-vote state where nothing was published.
   The K-implication holds vacuously here (its antecedent delivered_i(C) is
   false), and this state is exactly why K is contingent, not collapsed. *)
let false_witness_delivery_window i () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        ("EF (published(C) /\\ ~delivered_" ^ Validator.to_string i
       ^ "(C) /\\ ~K_" ^ Validator.to_string i ^ "(published C))")
        true
        (Gossip_auth_model.Checker.satisfiable sys
           (Formula.conj
              [
                f (Gossip_auth_model.Committee_published Gossip_auth_model.Cert_c);
                Formula.Not
                  (f (Gossip_auth_model.Delivered (i, Gossip_auth_model.Cert_c)));
                Formula.Not
                  (Formula.K
                     ( i,
                       f (Gossip_auth_model.Committee_published
                            Gossip_auth_model.Cert_c) ));
              ])))

(* The collision partner (operand-false side): the crash-post-vote state
   where subscriber i has voted the anchor but nothing was ever published
   and nothing delivered - the reachable state that grounds i's ignorance in
   the delivery window above. *)
let no_publish_collision_partner i () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        ("EF (voted_" ^ Validator.to_string i
       ^ "(anchor) /\\ ~published(C) /\\ ~delivered_" ^ Validator.to_string i
       ^ "(C))")
        true
        (Gossip_auth_model.Checker.satisfiable sys
           (Formula.conj
              [
                f (Gossip_auth_model.Anchor_voted i);
                Formula.Not
                  (f (Gossip_auth_model.Committee_published
                        Gossip_auth_model.Cert_c));
                Formula.Not
                  (f (Gossip_auth_model.Delivered (i, Gossip_auth_model.Cert_c)));
              ])))

let () =
  Alcotest.run "gossip_auth"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Gossip_auth_statements.name `Quick
              (prove_one st))
          Gossip_auth_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "outsider-frame-rejected" `Quick
            outsider_frame_rejected;
          Alcotest.test_case "publish-reaches-all" `Quick publish_reaches_all;
        ] );
      ( "contingency",
        List.concat_map
          (fun i ->
            [
              Alcotest.test_case
                ("k-contingent-" ^ Validator.to_string i)
                `Quick (k_contingent i);
              Alcotest.test_case
                ("false-witness-delivery-window-" ^ Validator.to_string i)
                `Quick (false_witness_delivery_window i);
              Alcotest.test_case
                ("no-publish-collision-partner-" ^ Validator.to_string i)
                `Quick (no_publish_collision_partner i);
            ])
          subscribers );
    ]
