(** Confirm-by-mutation for the STREAM_INBOUND_QUOTA family. Each statement has
    its OWN gate deletion, and each row asserts the proof flips to an error on
    the mutated model while the pristine row is the matching positive half.
    Citations are crates/network-libp2p/src/stream/behavior.rs and
    crates/network-libp2p/src/consensus.rs at git HEAD 0c59c15b.

    - S1 is pinned by {!Stream_inbound_quota_model.No_per_peer_keying}, which
      replaces the keyed [self.inbound.entry(peer).or_insert(InboundWindow {
      count: 0, started: now })] (behavior.rs:283) with a single
      behaviour-wide window. The neighbour event - inert under the pristine
      keying, because another identity's opens move another identity's entry -
      then bumps W's meter, so (window_count(R,W) > MAX /\ opened(W,R) <= MAX)
      becomes reachable and W's very first open can be rejected. Both conjuncts
      fail. SIBLING HUNT: the deletion is not repaired. The classification
      [StreamFailure::InboundRateLimited -> Some(Penalty::Medium)]
      (stream/upgrade.rs:159-160) is reported metrics-only and explicitly not
      enforced - "Classified for scoring but reported metrics-only until
      telemetry confirms the classification does not fire on healthy peers (see
      #739)" (consensus.rs:1677-1693) - so no ban evicts the flooder; QUIC's
      [max_concurrent_stream_limit] (consensus.rs:451-452,
      config/network.rs:289-291, default 10_000 at :305) bounds concurrent
      streams per connection and does not separate identities on separate
      connections; and the peer manager's excess-peer logic governs connection
      counts, not open rate. The [entry(peer)] key is the only thing keeping the
      identities apart.
    - S2 is pinned by
      {!Stream_inbound_quota_model.No_window_reset_on_disconnect}, which deletes
      exactly [self.inbound.remove(&peer);] (behavior.rs:258) inside
      [on_disconnected], reached from [ConnectionClosed { peer_id,
      remaining_established: 0, .. }] (behavior.rs:323-330). The redial then
      leaves the count where it was, so exceeding the allowance without a roll
      necessarily crosses the bound and is rate-limited: S2's until-path no
      longer exists. Note what does NOT flip and why: S2's ignorance conjunct
      goes vacuously true under this mutation because its antecedent stops
      being reachable, so the load-bearing half of this pin is the
      reachability conjunct alone. SIBLING HUNT: the only other reset is the
      tumbling roll at behavior.rs:284-287, and the statement's formula
      excludes rolled worlds by construction precisely so the roll cannot stand
      in for the deleted line; the peer manager's excess-reconnection handling
      applies to peers the node itself sheds, not to a peer that closes its own
      connection, so it supplies no reset either.
    - S3 is pinned by {!Stream_inbound_quota_model.No_identity_guard}, which
      deletes the [if let Some(bls) = self.swarm.behaviour().peer_manager
      .peer_to_bls(&peer)] gate at consensus.rs:1665 and forwards the stream
      regardless. Conjunct B refutes at once - an answered stream stops proving
      that R had resolved the opener - and conjunct A refutes as well because
      the silent class collapses to the quota alone. SIBLING HUNT: the
      consumers of [NetworkEvent::InboundStream] dispatch straight on
      [StreamKind] with no membership test
      (consensus/primary/src/network/mod.rs:1507-1510,
      consensus/worker/src/network/mod.rs:466), and the only [Deny] writer on
      that path is the capacity shed at
      consensus/primary/src/network/mod.rs:1892-1909, which WRITES A FRAME and
      runs only after delivery - so nothing one layer up reinstates a silent
      drop for an unresolved identity. DISCLOSED: the behaviour's own queue shed
      (behavior.rs:215-218, exercised by the in-tree test at :594-605), the
      [Err] arm of the [try_send] forward (consensus.rs:1666-1672) and the
      responder's request-read timeout
      (consensus/primary/src/network/mod.rs:1912-1920) are three further silent
      causes the model omits; each only ENLARGES the opener's silent class, so
      omitting them makes conjunct A harder rather than easier, but it does mean
      conjunct B - whose flip does not depend on the class collapsing - is this
      pin's robust half.

    Every antecedent stays REACHABLE under the mutation that pins its
    statement, so no row flips merely because [prove_nonvacuous] found a
    vacuous antecedent. The cross rows assert that the statements a mutation is
    NOT aimed at still prove under it, which is what makes each pin
    attributable rather than a side effect of some other collapse. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Stream_inbound_quota_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Stream_inbound_quota_model.Checker.make
       (Stream_inbound_quota_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Stream_inbound_quota_statements.name name))
    Stream_inbound_quota_statements.all

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
               (Stream_inbound_quota_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Stream_inbound_quota_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Stream_inbound_quota_statements.prove sys st)))

(** Attribution: a statement the mutation is NOT aimed at still proves under
    it, so the pinned row's flip cannot be some other statement's collapse. *)
let survives_under mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " still proves under this unrelated mutation")
            true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Stream_inbound_quota_statements.prove sys st)))

(** The refutation is a refutation, not a vacuity: the pinned statement's
    antecedent is still reachable on the mutated model, so [prove_nonvacuous]
    reached the formula. *)
let antecedent_still_reachable mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ ": antecedent still reachable under the mutation")
            true
            (Stream_inbound_quota_model.Checker.satisfiable sys
               st.Stream_inbound_quota_statements.antecedent))

(** A pristine-proves plus mutated-refutes pair for one statement, with the
    non-vacuity guard that makes the negative half meaningful. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
    Alcotest.test_case (name ^ ":antecedent-alive") `Quick
      (antecedent_still_reachable mut name);
  ]

(** The per-peer isolation statement's name. *)
let s1_name = "inbound-rate-window-charges-only-the-opening-peers-own-streams"

(** The episode-scope statement's name. *)
let s2_name =
  "inbound-quota-is-scoped-to-a-connection-episode-not-to-the-peer-identity"

(** The indistinguishable-drop statement's name. *)
let s3_name = "a-silently-dropped-inbound-stream-hides-which-gate-killed-it"

let () =
  Alcotest.run "stream_inbound_quota_mutation"
    [
      ( "one shared window lets a neighbour spend another peer's allowance",
        pin Stream_inbound_quota_model.No_per_peer_keying s1_name );
      ( "keeping the window across a redial closes the episode-scope evasion",
        pin Stream_inbound_quota_model.No_window_reset_on_disconnect s2_name );
      ( "forwarding an unresolved peer makes an answer stop proving resolution",
        pin Stream_inbound_quota_model.No_identity_guard s3_name );
      ( "attribution: the shared window touches neither the redial nor the \
         identity gate",
        [
          Alcotest.test_case (s2_name ^ ":survives") `Quick
            (survives_under Stream_inbound_quota_model.No_per_peer_keying
               s2_name);
          Alcotest.test_case (s3_name ^ ":survives") `Quick
            (survives_under Stream_inbound_quota_model.No_per_peer_keying
               s3_name);
        ] );
      ( "attribution: keeping the window across a redial leaves the keying and \
         the identity gate alone",
        [
          Alcotest.test_case (s1_name ^ ":survives") `Quick
            (survives_under
               Stream_inbound_quota_model.No_window_reset_on_disconnect s1_name);
          Alcotest.test_case (s3_name ^ ":survives") `Quick
            (survives_under
               Stream_inbound_quota_model.No_window_reset_on_disconnect s3_name);
        ] );
      ( "attribution: deleting the identity gate leaves both rate properties \
         alone",
        [
          Alcotest.test_case (s1_name ^ ":survives") `Quick
            (survives_under Stream_inbound_quota_model.No_identity_guard s1_name);
          Alcotest.test_case (s2_name ^ ":survives") `Quick
            (survives_under Stream_inbound_quota_model.No_identity_guard s2_name);
        ] );
    ]
