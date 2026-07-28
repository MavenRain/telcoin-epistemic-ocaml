(** Confirm-by-mutation ([[feedback-confirm-tests-by-mutation]]) for the
    PEER_TEMP_BAN family. Each mutation deletes exactly one line of the
    temporary-ban cache and each statement is pinned by the line it is about:

    - {!Peer_temp_ban_model.No_expiry_guard} deletes
      [if element.inserted + self.duration > now { self.list.push_front(element);
      break; }] (cache.rs:162-165), so the drain loop pops the whole list and an
      exclusion is served early. Pins "never-served-early". No sibling repairs
      it: [BannedPeerCache::heartbeat] has one call site (manager.rs:600),
      nothing re-inserts a wrongly released peer, and the reputation ban cannot
      stand in - a capacity disconnect never applies a penalty
      (all_peers.rs:702-707), so [AllPeers::peer_banned] (all_peers.rs:905-909)
      is false and the second disjunct of manager.rs:403 is dead.
    - {!Peer_temp_ban_model.No_heartbeat_drain} deletes
      [self.unban_temp_banned_peers();] from [PeerManager::heartbeat]
      (manager.rs:318), so [contains] never stops refusing. Pins
      "always-ends-at-a-heartbeat". The two sibling removers - the committee and
      trusted forgive routes (manager.rs:737-745, :145) - are MODELLED and left
      enabled by this mutation; the pin survives them because the liveness claim
      quantifies over all paths, including the one on which forgiveness never
      comes.
    - {!Peer_temp_ban_model.No_reinsert_refresh} deletes the duplicate-refresh
      else-branch of [insert] (cache.rs:123-128), so a re-banned peer keeps its
      original stamp and queue position. Pins
      "reinsertion-restarts-the-uniform-clock". No caller does remove-then-insert
      ([apply_peer_action] only inserts, manager.rs:331/:336/:342), and the stale
      element does not violate the sorted-by-insertion invariant the drain relies
      on (cache.rs:186-213), so nothing detects it.

    Each row asserts the exact verdict, not merely "not proved": a mutation that
    made an antecedent unreachable would report [Vacuous_antecedent] and would
    LOOK like a flip while proving nothing. The "attribution" group is the
    negative control: deleting the heartbeat drain leaves BOTH other statements
    proving, and deleting the refresh branch leaves the liveness statement
    proving, so those pins are not passing because the mutant is globally
    broken. {!Peer_temp_ban_model.No_expiry_guard} is stated honestly as the
    exception - it refutes all three, because the expiry comparison is the one
    line every conjunct of this family rests on. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Peer_temp_ban_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Peer_temp_ban_model.Checker.make (Peer_temp_ban_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Peer_temp_ban_statements.name name))
    Peer_temp_ban_statements.all

(** The verdict of one statement under one mutation, as a word: [proved],
    [refuted] or [vacuous]. Distinguishing the last two is the point - a pin
    whose antecedent stopped being reachable proves nothing. *)
let verdict mut name k =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          k
            (Result.fold
               ~ok:(fun _ -> "proved")
               ~error:(fun e ->
                 match e with
                 | Peer_temp_ban_model.Checker.Refuted _ -> "refuted"
                 | Peer_temp_ban_model.Checker.Vacuous_antecedent -> "vacuous")
               (Peer_temp_ban_statements.prove sys st)))

(** The negative half of a pin: the statement is REFUTED (not merely
    uncertified) under the mutation. *)
let refuted_under mut name () =
  verdict mut name (fun v ->
      Alcotest.(check string)
        (name ^ " flips to refuted under the mutation")
        "refuted" v)

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  verdict Peer_temp_ban_model.Pristine name (fun v ->
      Alcotest.(check string) (name ^ " proves on pristine") "proved" v)

(** The attribution control: this statement still proves under that mutation, so
    the mutant is not globally broken. *)
let survives_under mut name () =
  verdict mut name (fun v ->
      Alcotest.(check string)
        (name ^ " still proves under the other gate's deletion")
        "proved" v)

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

let () =
  Alcotest.run "peer_temp_ban_mutation"
    [
      ( "deleted expiry guard serves an exclusion early",
        pin Peer_temp_ban_model.No_expiry_guard
          "temp-ban-exclusion-is-never-served-early" );
      ( "deleted heartbeat drain makes the ban permanent",
        pin Peer_temp_ban_model.No_heartbeat_drain
          "temp-ban-exclusion-always-ends-at-a-heartbeat" );
      ( "deleted refresh branch releases on a stale stamp",
        pin Peer_temp_ban_model.No_reinsert_refresh
          "temp-ban-reinsertion-restarts-the-uniform-clock" );
      ( "cross-pins: the stale stamp also destroys the peer's inference",
        [
          Alcotest.test_case "never-early:no-reinsert-refresh" `Quick
            (refuted_under Peer_temp_ban_model.No_reinsert_refresh
               "temp-ban-exclusion-is-never-served-early");
          Alcotest.test_case "uniform-clock:no-expiry-guard" `Quick
            (refuted_under Peer_temp_ban_model.No_expiry_guard
               "temp-ban-reinsertion-restarts-the-uniform-clock");
          Alcotest.test_case "always-ends:no-expiry-guard" `Quick
            (refuted_under Peer_temp_ban_model.No_expiry_guard
               "temp-ban-exclusion-always-ends-at-a-heartbeat");
        ] );
      ( "attribution: each mutant leaves other statements proving",
        [
          Alcotest.test_case "never-early:no-heartbeat-drain" `Quick
            (survives_under Peer_temp_ban_model.No_heartbeat_drain
               "temp-ban-exclusion-is-never-served-early");
          Alcotest.test_case "uniform-clock:no-heartbeat-drain" `Quick
            (survives_under Peer_temp_ban_model.No_heartbeat_drain
               "temp-ban-reinsertion-restarts-the-uniform-clock");
          Alcotest.test_case "always-ends:no-reinsert-refresh" `Quick
            (survives_under Peer_temp_ban_model.No_reinsert_refresh
               "temp-ban-exclusion-always-ends-at-a-heartbeat");
        ] );
    ]
