(** Proof suite for the STREAM_SYNC_CAPABILITY family: the three statements
    prove on the pristine model, the model stays inside its stated size bound,
    each gate's forbidden state is genuinely unreachable, the model really does
    carry the repair paths the real code has (rather than being true by omitting
    them), and - the part that matters most - both knowledge claims and both
    ignorance claims are discharged by explicit witnesses rather than by a
    collapsed view class.

    The [sanity] group carries three UNREACHABILITY tests (the three gates'
    forbidden states) and three REACHABILITY tests whose job is the opposite: to
    show the model is not rigged. [ambiguous-partial-verdict-against-a-capable-
    peer] witnesses the population the guard at mod.rs:1091 exists for;
    [transport-fault-writes-a-capable-slot] witnesses the [Failed ->
    insert(peer, true)] repair at mod.rs:1102-1105 - the sibling path whose
    presence is what makes
    {!Stream_sync_capability_model.No_io_classification_split} a real deletion
    rather than a modelling artefact; and
    [a-post-negotiation-cut-caches-a-capable-peer-unsyncable] witnesses the leak
    the family refuses to paper over, namely that mod.rs:1221-1228 treats
    [UnexpectedEof | ConnectionReset | BrokenPipe] as a peer-attributable
    [Unsupported] while stream/upgrade.rs:149-156 scores those same kinds as
    "transport flaps on WAN are not faults". That is why S1 conjunct A is a
    disjunction: the shorter claim [K_V0(~answers_full_open(w))] is REFUTED on
    the pristine model, which is the intended outcome and not a defect.

    The [contingency] group discharges R2 and R3. For the positive K of S1
    conjunct A it carries both obligations: the knowledge is contingent (its
    negation is satisfiable somewhere reachable) and V0's view class at the
    operative state is NOT a singleton. The non-singleton test is given in two
    forms - the plain one and a SHARP one that also pins the atom false at the
    witness state, so it can only pass if some OTHER reachable state shares V0's
    view and satisfies that atom. The class sizes were measured rather than
    assumed: the class of the V0-view [(Some(&false), other, 1)] holds five
    reachable states - the [Pre_cutover] and [Negotiates_mute] slots written by
    a peer-side [Unsupported] (a negotiation failure at mod.rs:1176-1178 and an
    [Ack] timeout at :1220 collapse to one attempt value and one [false]) and
    the [Negotiates_mute], [Full_only] and [Full_and_partial] slots written by a
    post-negotiation cut. They disagree on [advertises_sync(w)] and on
    [answers_full_open(w)], which is exactly what S1 conjunct B and the
    disjunctive operand of conjunct A are about. *)

open Telcoin_epistemic
open Stream_sync_capability_model

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
        (st.Stream_sync_capability_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Stream_sync_capability_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold ~ok:(fun _ -> "proved") ~error:error_to_string
           (Stream_sync_capability_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The exact pristine reachable count: 34. The hidden disposition never
    changes and the boundary returns every state to its own cleared start, so
    the graph is four disjoint-except-at-the-root fans: 8 states for
    [Pre_cutover] (no post-negotiation cut is offered - the open never
    negotiates), 10 for [Negotiates_mute], 8 for [Full_only] and 8 for
    [Full_and_partial]. The raw product bound is 4 dispositions x 6 slot
    variants x 3 last-probe classes x 3 budgets = 216. *)
let reachable_bounded () =
  with_sys (fun sys ->
      Alcotest.(check int) "reachable states" 34 (Checker.reachable_count sys))

(** The provenance gate's forbidden state: no reachable state holds a negative
    slot that a PARTIAL probe wrote, because the write at mod.rs:1092 sits
    behind [if last_consensus_number.is_none()] (:1091). *)
let no_negative_slot_from_a_partial_probe () =
  with_sys (fun sys ->
      Alcotest.(check bool) "a partial-written negative slot is reachable" false
        (Checker.satisfiable sys
           (Formula.And
              (f Cached_unsyncable, Formula.Not (f Cached_by_full_probe)))))

(** The classification gate's forbidden state, stated exactly as strongly as the
    code supports: no reachable state caches a full-pack-capable peer unsyncable
    OTHER than through a post-negotiation cut (mod.rs:1221-1228). That residue
    is the leak; what the [Io] / [NegotiationFailed] split at handler.rs:145-148
    forbids is the PRE-negotiation fault doing it, because that arm writes
    [true] instead (mod.rs:1179 -> :1105). *)
let no_pre_negotiation_fault_caches_a_capable_peer_unsyncable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a full-pack-capable peer cached unsyncable other than by a cut is \
         reachable"
        false
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Cached_unsyncable;
                f Answers_full_open;
                Formula.Not (f Verdict_from_a_post_negotiation_cut);
              ])))

(** And the leak itself IS reachable, so the disjunctive operand of S1 conjunct
    A is load-bearing rather than decorative: mod.rs:1221-1228 classifies
    [UnexpectedEof | ConnectionReset | BrokenPipe] as [Unsupported] even though
    stream/upgrade.rs:149-156 scores those same kinds as not the peer's fault.
    The shorter claim [K_V0(~answers_full_open(w))] is refuted on the pristine
    model precisely because of this state. *)
let a_post_negotiation_cut_caches_a_capable_peer_unsyncable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a full-pack-capable peer cached unsyncable by a transport cut is \
         reachable"
        true
        (Checker.satisfiable sys
           (Formula.And
              (f Cached_unsyncable, f Verdict_from_a_post_negotiation_cut))))

(** The eligibility filter's forbidden state: once the slot reads [Some(&false)]
    no successor leaves it written, because [filter] drops the peer before any
    probe (mod.rs:1066-1069, identically :626-629) and the only remaining step
    is the boundary clear (start_epoch.rs:547-550). *)
let a_cached_unsyncable_peer_is_never_reprobed_in_epoch () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a successor of a cached-unsyncable state with a written slot is \
         reachable"
        false
        (Checker.satisfiable sys
           (Formula.And
              (f Cached_unsyncable, Formula.Ex (Formula.Not (f Entry_unwritten))))))

(** S2 is not vacuous on the population it is about: a peer that serves full
    packs but cannot decode [EpochPackPartial] (request.rs:67-72) really does
    return the ambiguous partial verdict the guard at mod.rs:1091 refuses to
    cache. *)
let an_ambiguous_partial_verdict_against_a_capable_peer_is_reachable () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "an ambiguous partial verdict against a full-pack-capable peer is \
         reachable"
        true
        (Checker.satisfiable sys
           (Formula.And (f Recent_partial_unsupported, f Answers_full_open))))

(** The model carries the repair path rather than omitting it (R5): a transport
    fault on the open becomes [UpgradeIo] (handler.rs:148), then [Failed]
    (mod.rs:1179), then [insert(peer, true)] (mod.rs:1105) - so even a peer that
    does not advertise the protocol at all can end the epoch cached CAPABLE.
    Deleting that path is exactly what
    {!Stream_sync_capability_model.No_io_classification_split} does. *)
let a_transport_fault_writes_a_capable_slot () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a peer that does not advertise sync cached capable is reachable" true
        (Checker.satisfiable sys
           (Formula.And (f Cached_capable, Formula.Not (f Advertises_sync)))))

(** R2 contingency for S1 conjunct A's positive K: the knowledge is not rigid -
    there are reachable states where V0 does not have it. This is the operand as
    the statement actually uses it, the disjunction that survives a
    post-negotiation cut. *)
let non_answer_knowledge_is_contingent () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "K_V0(~answers_full_open \\/ cut) fails somewhere reachable" true
        (Checker.satisfiable sys
           (Formula.Not
              (Formula.K
                 ( Validator.V0,
                   Formula.Or
                     ( Formula.Not (f Answers_full_open),
                       f Verdict_from_a_post_negotiation_cut ) )))))

(** R2 non-singleton class for [K_V0(~answers_full_open(w))]: at a cached-
    unsyncable state V0 does NOT know that [w] fails to advertise the protocol.
    That is only possible because another reachable state shares V0's view -
    same map answer, same last-probe class, same budget, same epoch - and
    disagrees on [w]'s advertisement, which V0 cannot see. *)
let negative_verdict_view_class_is_not_a_singleton () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "the V0-view class at a cached-unsyncable state holds more than one \
         state"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Cached_unsyncable,
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Advertises_sync))) ))))

(** The same obligation in its SHARP form: the witness state is one where
    [advertises_sync(w)] is FALSE, so the failure of [K_V0(~advertises_sync(w))]
    there cannot come from the state satisfying the atom itself. It can only
    come from a DIFFERENT reachable state in the same V0-view class that does. *)
let negative_verdict_view_class_holds_a_disagreeing_state () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a cached-unsyncable state with a pre-cutover peer still fails to know \
         it"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Cached_unsyncable;
                Formula.Not (f Advertises_sync);
                Formula.Not
                  (Formula.K (Validator.V0, Formula.Not (f Advertises_sync)));
              ])))

(** R3 ignorance witness for S1 conjunct B, true side: a reachable state where
    the slot reads [false], [w] really does advertise the protocol - it
    negotiated and then never [Ack]ed (mod.rs:1220) - and V0 does not know it. *)
let advertisement_ignorance_witness_true_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a cached-unsyncable peer that advertises sync, unknown to V0, is \
         reachable"
        true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Cached_unsyncable;
                f Advertises_sync;
                Formula.Not (Formula.K (Validator.V0, f Advertises_sync));
              ])))

(** R3 ignorance witness for S1 conjunct B, false side: the state that makes the
    first half ignorance rather than knowledge - the same [false] over a peer
    that genuinely is pre-cutover. *)
let advertisement_ignorance_witness_false_side () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a cached-unsyncable peer that does not advertise sync is reachable"
        true
        (Checker.satisfiable sys
           (Formula.And (f Cached_unsyncable, Formula.Not (f Advertises_sync)))))

(** R3 ignorance witness for S3 conjunct B: the excluded peer does not know it
    has been excluded. The map is a private field of the prober's handle
    (mod.rs:380) and the probe is penalty-exempt (handler.rs:211-220). *)
let exclusion_is_invisible_to_the_excluded_peer () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a cached-unsyncable state the peer cannot detect is reachable" true
        (Checker.satisfiable sys
           (Formula.And
              ( f Cached_unsyncable,
                Formula.Not (Formula.K (Validator.V1, f Cached_unsyncable)) ))))

(** The other side of that ignorance: at a state where the peer is cached
    CAPABLE it does not know it is un-excluded either, so V1's uncertainty is
    two-sided rather than an artefact of one state. The witness pair exists
    because a transport fault writes [true] (mod.rs:1105) at the same view. *)
let non_exclusion_is_equally_invisible () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a cached-capable state the peer cannot distinguish from exclusion is \
         reachable"
        true
        (Checker.satisfiable sys
           (Formula.And
              ( f Cached_capable,
                Formula.Not
                  (Formula.K (Validator.V1, Formula.Not (f Cached_unsyncable))) ))))

(** The map's POSITIVE side is deliberately not a knowledge claim, which is why
    no statement asserts one: [Failed] writes [true] (mod.rs:1105) just as
    [Imported] does (:1074), so a [true] slot leaves V0 ignorant of whether the
    peer ever answered. *)
let a_capable_slot_is_not_knowledge_of_an_answer () =
  with_sys (fun sys ->
      Alcotest.(check bool)
        "a cached-capable peer that answers, unknown to V0, is reachable" true
        (Checker.satisfiable sys
           (Formula.conj
              [
                f Cached_capable;
                f Answers_full_open;
                Formula.Not (Formula.K (Validator.V0, f Answers_full_open));
              ])))

let () =
  Alcotest.run "stream_sync_capability"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Stream_sync_capability_statements.name `Quick
              (prove_one st))
          Stream_sync_capability_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "no-negative-slot-from-a-partial-probe" `Quick
            no_negative_slot_from_a_partial_probe;
          Alcotest.test_case
            "no-pre-negotiation-fault-caches-a-capable-peer-unsyncable" `Quick
            no_pre_negotiation_fault_caches_a_capable_peer_unsyncable;
          Alcotest.test_case
            "a-post-negotiation-cut-caches-a-capable-peer-unsyncable" `Quick
            a_post_negotiation_cut_caches_a_capable_peer_unsyncable;
          Alcotest.test_case "cached-unsyncable-peer-is-never-reprobed-in-epoch"
            `Quick a_cached_unsyncable_peer_is_never_reprobed_in_epoch;
          Alcotest.test_case "ambiguous-partial-verdict-is-reachable" `Quick
            an_ambiguous_partial_verdict_against_a_capable_peer_is_reachable;
          Alcotest.test_case "transport-fault-writes-a-capable-slot" `Quick
            a_transport_fault_writes_a_capable_slot;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "non-answer-knowledge-is-contingent" `Quick
            non_answer_knowledge_is_contingent;
          Alcotest.test_case "negative-verdict-view-class-is-not-a-singleton"
            `Quick negative_verdict_view_class_is_not_a_singleton;
          Alcotest.test_case
            "negative-verdict-view-class-holds-a-disagreeing-state" `Quick
            negative_verdict_view_class_holds_a_disagreeing_state;
          Alcotest.test_case "advertisement-ignorance-witness-true-side" `Quick
            advertisement_ignorance_witness_true_side;
          Alcotest.test_case "advertisement-ignorance-witness-false-side" `Quick
            advertisement_ignorance_witness_false_side;
          Alcotest.test_case "exclusion-is-invisible-to-the-excluded-peer"
            `Quick exclusion_is_invisible_to_the_excluded_peer;
          Alcotest.test_case "non-exclusion-is-equally-invisible" `Quick
            non_exclusion_is_equally_invisible;
          Alcotest.test_case "a-capable-slot-is-not-knowledge-of-an-answer"
            `Quick a_capable_slot_is_not_knowledge_of_an_answer;
        ] );
    ]
