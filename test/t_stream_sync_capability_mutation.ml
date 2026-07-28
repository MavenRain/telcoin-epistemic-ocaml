(** Confirm-by-mutation for the STREAM_SYNC_CAPABILITY family: each pin asserts
    the pristine proof AND the flip to refuted under the gate deletion, per
    statement, so a pin can never pass on the strength of some other statement's
    collapse. The three gates live in three different crates and the last group
    asserts, for each, that the statements it is not meant to touch still prove.

    - {!Stream_sync_capability_model.No_io_classification_split} deletes the
      distinct [Io] arm of [classify_outbound]
      (network-libp2p/src/stream/handler.rs:148), mapping
      [StreamUpgradeError::Io(e)] to
      [(StreamFailure::UnsupportedProtocol, StreamError::UpgradeFailed)] like
      the [NegotiationFailed] arm at :145-147. The consumer then turns a
      PRE-negotiation transport fault into [EpochPackAttempt::Unsupported]
      (mod.rs:1176-1178) instead of [Failed] (:1179), and a FULL probe writes
      [false] (mod.rs:1091-1093) against a peer that answers. It pins S1. No sibling
      repairs it: the [Failed -> insert(peer, true)] arm (mod.rs:1102-1105) is
      the repair the pristine code uses and is exactly what the deletion
      removes - the model HAS that path, which test/t_stream_sync_capability.ml
      witnesses as [transport-fault-writes-a-capable-slot]; the eligibility
      filters (mod.rs:1066-1069, :626-629) drop the poisoned peer before any
      second probe; the consensus-output path never writes [false] at all
      (:643-653); there is no legacy [/tn-stream] fallback post-#739
      (mod.rs:607-608, :1053-1055); and the epoch clear repairs only at the next
      boundary.
    - {!Stream_sync_capability_model.No_partial_probe_guard} deletes
      [if last_consensus_number.is_none()] at
      consensus/primary/src/network/mod.rs:1091, so every [Unsupported] writes
      [false] (:1092). It pins S2. No sibling repairs it: the repair the guard
      preserves is a LATER FULL PROBE inside the same epoch, and the filter at
      mod.rs:1066-1069 destroys it once [Some(false)] is in the map - which is
      precisely why the model carries a two-probe budget and why S2 conjunct C
      is stated as an [EX] rather than an [EF].
    - {!Stream_sync_capability_model.No_epoch_clear} deletes
      [network_handle.clear_sync_capability();]
      (node/src/manager/node/start_epoch.rs:550). It pins S3. No sibling repairs
      it: the map has no TTL and no eviction (the only writers in the tree are
      the [insert] sites at mod.rs:634, :658, :1074, :1092, :1105 and this
      clear), and no fresh handle resets it incidentally -
      [PrimaryNetworkHandle::new] runs once inside [spawn_node_networks]
      (node.rs:1117-1143), which [run] calls once before the epoch loop
      (node.rs:877), while every epoch merely CLONES the stored handle
      (start_epoch.rs:326-330) over a map held behind an [Arc] (mod.rs:380).

    The pins were confirmed CONJUNCT BY CONJUNCT before being written, so no pin
    can be passing because some other conjunct of the same statement collapsed.
    Proving each conjunct alone against each transition relation gives:

    {v
                                     pristine  no_io_split  no_partial  no_clear
      reachable states                  34          36          30         47
      S1.A K_V0(~answers \/ cut)      PROVED     REFUTED     REFUTED     PROVED
      S1.B ~K_V0(~advertises(w))      PROVED     PROVED      PROVED      PROVED
      S2.A negative slot is full      PROVED     PROVED      REFUTED     PROVED
      S2.B partial never caches no    PROVED     PROVED      REFUTED     PROVED
      S2.C protected peer reachable   PROVED     PROVED      REFUTED     PROVED
      S3.A AF entry_unwritten(w)      PROVED     PROVED      PROVED      REFUTED
      S3.B ~K_V1(cached_unsync(w))    PROVED     PROVED      PROVED      PROVED
      -- rejected, kept as evidence --
      K_V0(~answers_full(w)) alone   REFUTED     REFUTED     REFUTED    REFUTED
    v}

    Three things in that table are reported rather than hidden.

    First, the last row. The shorter, more attractive form of S1 conjunct A -
    "a cached [false] means the peer does not answer" - is REFUTED on the
    PRISTINE model, because mod.rs:1221-1228 caches [false] when a connection
    dies after a successful negotiation, and stream/upgrade.rs:149-156 scores
    exactly those error kinds as not the peer's fault. It is recorded here
    because an earlier draft of this family stated it and the model was
    extended, not the statement rigged: the disjunctive operand is what the code
    actually supports.

    Second, S1 is ALSO refuted by
    {!Stream_sync_capability_model.No_partial_probe_guard}, and that is correct
    rather than a leak: both gates protect the SAME negative verdict, one
    against a mis-timed transport fault and one against an ambiguous request
    variant, so deleting either makes a full-pack-capable peer cacheable as
    unsyncable through a route that is neither disjunct. S1 is pinned on the
    [Io] split because that is the deletion under which S1 alone flips and S2
    survives intact.

    Third, S1 conjunct B and S3 conjunct B are stated because they are TRUE, not
    because a mutation refutes them; each sits inside a conjunction that a
    mutation does refute, and each carries its own R3 witness in
    test/t_stream_sync_capability.ml.

    Every refutation above is a [Refuted] verdict, never a [Vacuous_antecedent]:
    [cached_unsyncable(w)] (S1, S3) and [recent_partial_unsupported] (S2) stay
    reachable under all three mutations, so the pins are genuine counterexamples
    rather than the antecedent falling out of the reachable set. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Stream_sync_capability_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Stream_sync_capability_model.Checker.make
       (Stream_sync_capability_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0
        (String.compare st.Stream_sync_capability_statements.name name))
    Stream_sync_capability_statements.all

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
               (Stream_sync_capability_statements.prove sys st)))

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut Stream_sync_capability_model.Pristine (fun sys ->
          Alcotest.(check bool) (name ^ " proves on pristine") true
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Stream_sync_capability_statements.prove sys st)))

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
               (Stream_sync_capability_statements.prove sys st)))

(** The antecedent of a pinned statement stays reachable under its mutation, so
    the flip above is a [Refuted] verdict and not a [Vacuous_antecedent]. *)
let antecedent_survives mut name () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ ": antecedent is still reachable under the mutation") true
            (Stream_sync_capability_model.Checker.satisfiable sys
               st.Stream_sync_capability_statements.antecedent))

(** S1's name, spelled once. *)
let s1_name =
  "cached-unsyncable-verdict-is-bounded-knowledge-of-the-peers-non-answer"

(** S2's name, spelled once. *)
let s2_name = "only-a-full-pack-probe-writes-the-negative-capability-entry"

(** S3's name, spelled once. *)
let s3_name =
  "epoch-boundary-clear-restores-an-eligibility-the-excluded-peer-cannot-observe"

let () =
  Alcotest.run "stream_sync_capability_mutation"
    [
      ( "deleted Io/negotiation split lets a transport fault cache unsyncable",
        pin Stream_sync_capability_model.No_io_classification_split s1_name );
      ( "deleted partial-probe guard poisons a full-pack-capable peer",
        pin Stream_sync_capability_model.No_partial_probe_guard s2_name );
      ( "deleted epoch clear excludes the peer for the life of the process",
        pin Stream_sync_capability_model.No_epoch_clear s3_name );
      ( "each gate deletion leaves the statements it does not target standing",
        [
          Alcotest.test_case "provenance-statement:under-io-split-deletion"
            `Quick
            (survives_under
               Stream_sync_capability_model.No_io_classification_split s2_name);
          Alcotest.test_case "fairness-statement:under-io-split-deletion" `Quick
            (survives_under
               Stream_sync_capability_model.No_io_classification_split s3_name);
          Alcotest.test_case "fairness-statement:under-partial-guard-deletion"
            `Quick
            (survives_under Stream_sync_capability_model.No_partial_probe_guard
               s3_name);
          Alcotest.test_case "knowledge-statement:under-epoch-clear-deletion"
            `Quick
            (survives_under Stream_sync_capability_model.No_epoch_clear s1_name);
          Alcotest.test_case "provenance-statement:under-epoch-clear-deletion"
            `Quick
            (survives_under Stream_sync_capability_model.No_epoch_clear s2_name);
        ] );
      ( "every flip is a refutation, not a vacuous antecedent",
        [
          Alcotest.test_case "knowledge-statement:antecedent-under-io-split"
            `Quick
            (antecedent_survives
               Stream_sync_capability_model.No_io_classification_split s1_name);
          Alcotest.test_case
            "provenance-statement:antecedent-under-partial-guard" `Quick
            (antecedent_survives
               Stream_sync_capability_model.No_partial_probe_guard s2_name);
          Alcotest.test_case "fairness-statement:antecedent-under-epoch-clear"
            `Quick
            (antecedent_survives Stream_sync_capability_model.No_epoch_clear
               s3_name);
        ] );
    ]
