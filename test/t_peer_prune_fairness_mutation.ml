(** Confirm-by-mutation for the PEER_PRUNE_FAIRNESS family: each pin asserts
    the pristine proof AND the flip to refuted under one gate deletion, per
    statement, so no pin can pass on the strength of another statement's
    collapse. The last group asserts that each deletion leaves the other
    statements standing, which is what keeps every pin attributable to its own
    gate.

    The four deletions, and the sibling-repair hunt behind each:

    - {!Peer_prune_fairness_model.No_score_sort} deletes
      [connected_peers.sort_by_key(|(_, peer)| (peer.score(),
      peer.is_routable()));] (all_peers.rs:976), leaving the shuffle at :974.
      Eviction order becomes arbitrary, so a HIGH-bucket peer can be dropped
      while a LOW-bucket candidate is still connected. It pins S1. No repair:
      the candidate filter is an order-preserving [filter_map]
      (manager.rs:571-581), the eviction loop is a plain [for] over its output
      with no re-sort (manager.rs:583-594), [disconnect_peer] takes the peer as
      handed (manager.rs:472-489), and [collect_excess_peers]
      (all_peers.rs:996-1034) - the crate's only other eviction-ordering code -
      orders BANNED and DISCONNECTED pruning by [Instant] and never touches the
      connected set.
    - {!Peer_prune_fairness_model.No_tie_shuffle} deletes
      [connected_peers.shuffle(&mut rand::rng());] (all_peers.rs:974). It pins
      S2. No repair: [sort_by_key] is Rust's STABLE sort, so it preserves the
      order it was given on ties and cannot re-randomise; the peer store is a
      [HashMap<PeerIdentity, Peer>] (all_peers.rs:44) whose [RandomState] is
      seeded once per map, so the surviving order is fixed for the life of the
      process and the same tie peer loses at every heartbeat.
    - {!Peer_prune_fairness_model.No_validator_exemption} deletes the
      [!self.is_peer_validator(peer_id) &&] conjunct of the prune filter
      (manager.rs:575). It pins S3. The KNOWN partial repair is the score sort:
      committee entry primes the member to the maximum score
      (all_peers.rs:1232, peer.rs:416-418), so under a small excess the sort
      alone keeps the validator alive even with the conjunct gone. That repair
      is defeated by construction, not ignored: the model's [Tight] regime has
      excess 4 against 4 candidates, so every candidate is evicted and no
      ordering can rescue anyone. [peer_is_important] (manager.rs:665-668)
      guards only the connect-time limit at behavior.rs:266-272 and never
      re-admits a pruned peer; within the round re-admission is blocked anyway
      by the [temporarily_banned] insert on the [DisconnectWithPX] arm
      (manager.rs:340-345, gate at :396-404).
    - {!Peer_prune_fairness_model.No_allowlist_exemption} deletes the
      [&& !peer.is_operator_allowlisted()] conjunct of the same filter
      (manager.rs:575). It also pins S3. Same analysis: operator trust exempts
      the peer from the score model ([TrustBasis::Operator],
      all_peers.rs:847-873) so its score never decays, which is again only a
      sort-level rescue, again defeated by the [Tight] regime.

    The pins were confirmed CONJUNCT BY CONJUNCT before being written, so no
    pin can be passing because some other conjunct of the same statement
    collapsed:

    {v
                               pristine no_score no_shuffle no_val no_allow
      S1  score_ordered         PROVED  REFUTED   PROVED    PROVED  PROVED
      S2.A no_starvation        PROVED  PROVED    REFUTED   PROVED  PROVED
      S2.B exactly_one          PROVED  PROVED    PROVED    PROVED  PROVED
      S3.A validator_carve_out  PROVED  PROVED    PROVED    REFUTED PROVED
      S3.B operator_carve_out   PROVED  PROVED    PROVED    PROVED  REFUTED
      S3.C excess_tolerated     PROVED  PROVED    PROVED    REFUTED REFUTED
      S3.D recognition_gap      PROVED  PROVED    PROVED    PROVED  PROVED
    v}

    Every refutation is a [Refuted] verdict, never a [Vacuous_antecedent]:
    each statement's antecedent stays reachable under the mutation that pins
    it. S2.B and S3.D are stated because they are true and complete their
    statements' content, not because a mutation refutes them; each sits inside
    a conjunction that a mutation does refute. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Peer_prune_fairness_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Peer_prune_fairness_model.Checker.make
       (Peer_prune_fairness_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Peer_prune_fairness_statements.name name))
    Peer_prune_fairness_statements.all

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
               (Peer_prune_fairness_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Peer_prune_fairness_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Peer_prune_fairness_statements.prove sys st)))

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
               (Peer_prune_fairness_statements.prove sys st)))

(** S1's name. *)
let ordering = "excess-prune-drops-the-lowest-scored-candidate-first"

(** S2's name. *)
let tie_break = "tied-candidates-share-the-single-eviction-slot"

(** S3's name. *)
let carve_out = "recognized-exemption-is-the-only-prune-carve-out"

let () =
  Alcotest.run "peer_prune_fairness_mutation"
    [
      ( "deleted score sort makes eviction order arbitrary",
        pin Peer_prune_fairness_model.No_score_sort ordering );
      ( "deleted tie shuffle fixes the victim for the life of the process",
        pin Peer_prune_fairness_model.No_tie_shuffle tie_break );
      ( "deleted validator conjunct lets the prune loop evict a validator",
        pin Peer_prune_fairness_model.No_validator_exemption carve_out );
      ( "deleted allowlist conjunct lets the prune loop evict an allowlisted \
         peer",
        pin Peer_prune_fairness_model.No_allowlist_exemption carve_out );
      ( "each gate deletion leaves the other statements standing",
        [
          Alcotest.test_case "ordering:under-shuffle-deletion" `Quick
            (survives_under Peer_prune_fairness_model.No_tie_shuffle ordering);
          Alcotest.test_case "ordering:under-validator-deletion" `Quick
            (survives_under Peer_prune_fairness_model.No_validator_exemption
               ordering);
          Alcotest.test_case "ordering:under-allowlist-deletion" `Quick
            (survives_under Peer_prune_fairness_model.No_allowlist_exemption
               ordering);
          Alcotest.test_case "tie-break:under-sort-deletion" `Quick
            (survives_under Peer_prune_fairness_model.No_score_sort tie_break);
          Alcotest.test_case "tie-break:under-validator-deletion" `Quick
            (survives_under Peer_prune_fairness_model.No_validator_exemption
               tie_break);
          Alcotest.test_case "tie-break:under-allowlist-deletion" `Quick
            (survives_under Peer_prune_fairness_model.No_allowlist_exemption
               tie_break);
          Alcotest.test_case "carve-out:under-sort-deletion" `Quick
            (survives_under Peer_prune_fairness_model.No_score_sort carve_out);
          Alcotest.test_case "carve-out:under-shuffle-deletion" `Quick
            (survives_under Peer_prune_fairness_model.No_tie_shuffle carve_out);
        ] );
    ]
