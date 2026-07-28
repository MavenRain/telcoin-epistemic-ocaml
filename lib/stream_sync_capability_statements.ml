(** The STREAM_SYNC_CAPABILITY statements: three readings of one three-valued
    per-peer map over the interpreted system of {!Stream_sync_capability_model}
    - what a cached negative verdict entitles the prober to KNOW about the
    candidate peer and, just as importantly, what it does NOT entitle it to know
    (S1); which probe is allowed to write that verdict at all (S2); and the
    anti-starvation half, that the verdict cannot outlive its epoch even though
    the peer it excludes can never see it (S3).

    The three are pinned by three gate deletions in three different crates -
    network-libp2p's upgrade classifier, consensus/primary's cache writer and
    node's epoch-start sequence - and
    test/t_stream_sync_capability_mutation.ml asserts the separation explicitly:
    each statement survives the two gate deletions that are not its own.

    READING GUIDE for the K operands - why neither positive K is a projection of
    its own knower's view, and why neither is rigid.

    - [K_V0(~answers_full_open(w) \/ verdict_from_post_negotiation_cut(w))] in
      S1 conjunct A. V0's view is [(map answer, last-probe classification,
      probes spent)] ({!Stream_sync_capability_model.view}); it contains neither
      [w]'s disposition nor which of the three [Unsupported] routes produced a
      negative slot, because the [EpochPackAttempt] that classified the exchange
      dies inside the probe closure (mod.rs:1071-1116) and only a [bool] reaches
      the map (mod.rs:380). Both disjuncts are therefore hidden, and the operand
      is not rigid: it is FALSE at every reachable state whose peer is
      [Full_only] or [Full_and_partial] and whose slot is not a cut verdict,
      which includes two of the four initial worlds.

      WHY THE DISJUNCTION AND NOT THE SHORTER CLAIM. The obvious statement -
      [K_V0(~answers_full_open(w))], "a cached [false] means the peer does not
      answer" - is FALSE of this code, and the model is built so that it comes
      out false rather than being rigged past. The [Io] / [NegotiationFailed]
      split exists at the OPEN (handler.rs:145-148) but is not applied at the
      READ: mod.rs:1221-1228 classifies [UnexpectedEof | ConnectionReset |
      BrokenPipe] as [Unsupported], while the stream layer's own penalty
      taxonomy scores those same kinds as not the peer's fault ("transport flaps
      on WAN are not faults", stream/upgrade.rs:149-156). So a connection that
      dies between a successful negotiation and the first frame caches [false]
      against a peer that answers. That route is modelled
      ({!Stream_sync_capability_model.Link_cut_after_open}) and it refutes the
      shorter claim on the PRISTINE model; the disjunction is exactly what
      survives it, and it still fails under the mutation, because a fault that
      lands BEFORE negotiation is neither disjunct.

      What makes the disjunction KNOWN at a cached-[false] state is the
      classification gate: only [StreamError::UpgradeFailed] becomes
      [Unsupported] (mod.rs:1176-1178) while [UpgradeIo] becomes [Failed]
      (handler.rs:148 -> mod.rs:1179), and [Failed] writes [true] (mod.rs:1105).
      Delete the [Io] split and a pre-negotiation fault is cached [false] with
      V0's view unchanged - that is the refutation.

      NON-DEGENERACY (R2): at a cached-[false] state V0's view class is never a
      singleton. The class of [(Some(&false), other, 1)] alone contains the
      [Pre_cutover] and [Negotiates_mute] copies (a negotiation failure at
      mod.rs:1176-1178 and an [Ack] timeout at :1220 collapse to the same
      [Unsupported] and the same [false]) plus the [Negotiates_mute],
      [Full_only] and [Full_and_partial] copies whose slot came from a
      post-negotiation cut. test/t_stream_sync_capability.ml discharges the
      obligation in its sharp form:
      [cached_unsyncable /\ ~advertises_sync(w) /\ ~K_V0(~advertises_sync(w))]
      is satisfiable, which is possible only if some OTHER reachable state
      shares V0's view and satisfies [advertises_sync(w)].

    - [~K_V0(~advertises_sync(w))] in S1 conjunct B. This is the bound on the
      knowledge, and it is the conjunct that keeps S1 conjunct A honest. A
      cached [false] does NOT license "the peer is pre-cutover and does not
      speak the protocol": the doc at mod.rs:373-376 says [false] means the peer
      "did not answer a sync open (a pre-cutover peer that fails negotiation, OR
      one that negotiated but never [Ack]ed)", and the [Ack]-timeout route at
      mod.rs:1220 produces exactly the second kind. The ignorance witness is the
      pair of reachable states above, identical in V0's view and disagreeing on
      whether [w] advertises the protocol at all.

    - [~K_V1(cached_unsyncable(w))] in S3 conjunct B. The excluded peer cannot
      detect its own exclusion. V1's view is [(own disposition, inbound sync
      opens offered)] - deliberately generous, since [w]'s swarm does see
      inbound opens - and the map is a private field of [v]'s handle
      (mod.rs:380) that is never serialized into a frame (request.rs:38-84) and
      never reported back, while the sync probe is penalty-exempt on the
      [UnsupportedProtocol] branch (handler.rs:211-220) so not even [w]'s peer
      score carries the verdict. The witness pair is a cached-[false] state and
      a cached-[true] state with the same disposition and the same open count -
      the second reachable because a transport fault at the open writes [true]
      (mod.rs:1179 -> :1105). That asymmetry is why the recovery in S3 conjunct
      A has to be an unconditional prober-side reset rather than anything the
      peer could ask for.

    Buckets reuse the frozen {!Statements} vocabulary. *)

open Stream_sync_capability_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** unique across every family *)
  bucket : Statements.bucket;  (** Safety | Liveness | Fairness | Security *)
  formula : atom Formula.t;  (** the claim, proved with [prove_nonvacuous] *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - cached-unsyncable-verdict-is-bounded-knowledge-of-the-peers-non-answer
    [security].

    The capability map's negative verdict is a knowledge claim about ANOTHER
    node, and the whole of its soundness rests on one three-way split in
    [classify_outbound] (network-libp2p/src/stream/handler.rs:142-152):
    [NegotiationFailed] becomes [StreamError::UpgradeFailed] (:145-147) while
    [Io(e)] becomes [StreamError::UpgradeIo] (:148). The public error type states
    the reason (stream/upgrade.rs:85-88): [UpgradeIo] is "Distinct from
    [StreamError::UpgradeFailed]: the peer may well speak the protocol, so a
    caller probing protocol support should treat this as transient rather than as
    'unsupported'". The consumer honours the split exactly once, at
    mod.rs:1173-1181, where ONLY [UpgradeFailed] becomes
    [EpochPackAttempt::Unsupported] and everything else becomes [Failed] - and
    [Failed] writes [true] into the map (mod.rs:1102-1105), not [false].

    - Conjunct A (positive knowledge, honestly bounded): whenever [v]'s slot for
      [w] reads [Some(&false)], V0 KNOWS that EITHER [w] does not answer a
      full-pack open OR the exchange was cut by the transport after the protocol
      had already been negotiated. What the [Io] split buys is the exclusion of
      the third possibility - a transport fault BEFORE negotiation completed,
      which the pristine code caches as [true] rather than [false]
      (handler.rs:148 -> mod.rs:1179 -> :1105). Both disjuncts are hidden from
      V0 and the operand is false at reachable states; V0's view class at the
      operative state holds five states, not one - see the reading guide and the
      [contingency] group of test/t_stream_sync_capability.ml.
    - Conjunct B (the bound on the other axis): the same [false] does NOT
      entitle V0 to conclude that [w] fails to advertise [/tn-primary-sync].
      Two routes reach [Unsupported] after a SUCCESSFUL negotiation - the
      [SYNC_ACK_TIMEOUT] elapsing (mod.rs:1210-1220) and the read error
      (mod.rs:1221-1228) - and the field doc at mod.rs:373-376 names the first
      kind explicitly. Stating this is what stops conjunct A from being read as
      the stronger, false claim.

    MUTATION PIN.
    {!Stream_sync_capability_model.No_io_classification_split} deletes the
    distinct [Io] arm at handler.rs:148, so a transport fault at the open
    arrives as [UpgradeFailed]. Conjunct A then fails at the state where a
    [Full_and_partial] peer's full probe hit a PRE-negotiation fault: the slot
    reads [false] while [w] answers full-pack opens perfectly well AND the
    verdict is not a post-negotiation cut, so neither disjunct holds and V0's
    view is byte-for-byte what it was. Conjunct B is UNTOUCHED by that deletion,
    so the pin is attributable to conjunct A alone. No sibling path repairs the
    deletion: the [Failed -> insert(peer, true)] arm (mod.rs:1105) is the repair
    the pristine code uses and it is precisely what the deletion removes; the
    eligibility filters at mod.rs:1066-1069 and :626-629 drop the peer before
    any second probe could correct the entry; the consensus-output path's
    [Unsupported] arm writes nothing at all (mod.rs:643-653); there is no legacy
    [/tn-stream] fallback post-#739 (mod.rs:607-608, :1053-1055); and the
    epoch-boundary clear (mod.rs:409-416, start_epoch.rs:547-550) - which IS
    modelled - repairs only at the next boundary, strictly after the state that
    refutes the conjunct. *)
let s1 =
  let negative_verdict_is_knowledge_of_non_answer =
    Formula.Ag
      (Formula.Implies
         ( atom Cached_unsyncable,
           Formula.K
             ( Validator.V0,
               Formula.Or
                 ( Formula.Not (atom Answers_full_open),
                   atom Verdict_from_a_post_negotiation_cut ) ) ))
  in
  let negative_verdict_is_not_knowledge_of_non_advertisement =
    Formula.Ag
      (Formula.Implies
         ( atom Cached_unsyncable,
           Formula.Not
             (Formula.K (Validator.V0, Formula.Not (atom Advertises_sync))) ))
  in
  {
    name = "cached-unsyncable-verdict-is-bounded-knowledge-of-the-peers-non-answer";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( negative_verdict_is_knowledge_of_non_answer,
          negative_verdict_is_not_knowledge_of_non_advertisement );
    antecedent = atom Cached_unsyncable;
  }

(** S2 - only-a-full-pack-probe-writes-the-negative-capability-entry [safety].

    Two failures are indistinguishable at the frame layer: a peer that does not
    speak the sync protocol, and a peer that speaks it and serves full packs but
    cannot decode the newer [EpochPackPartial] request variant
    (request.rs:67-72). Only the first is proof of absence, so the write is
    guarded: [if last_consensus_number.is_none() { self.sync_capability.lock()
    .insert(peer, false); }] (mod.rs:1091-1093), under the comment at :1084-1090
    that names the ambiguity - "A PARTIAL [Unsupported] is ambiguous: the peer
    may be on an earlier item that serves full packs but cannot decode the newer
    [EpochPackPartial] variant, so it must not cache [false] and hide that peer
    from full-pack sync."

    - Conjunct A: every negative slot in the map was written by a FULL-pack
      probe. This is the guard read as an invariant on provenance.
    - Conjunct B: an ambiguous partial verdict never coincides with a negative
      slot. This is the same guard read forward: the partial path "dedups
      without poisoning" (mod.rs:1089-1090) - it honours a [false] a full probe
      wrote, because the eligibility filter at :1066-1069 drops the peer before
      the probe ever runs, and it caches [true] on success (:1074), but it never
      writes [false] itself.
    - Conjunct C: and the peer the guard protects stays REACHABLE. At a state
      where a full-pack-capable peer has just returned an ambiguous partial
      verdict and the epoch's probe budget is not yet spent
      ([MAX_EPOCH_SYNC_PROBES], mod.rs:148, :1070), a next step exists in which
      the map records it capable. That is the repair the guard is holding open,
      and it is what the deletion destroys.

    MUTATION PIN. {!Stream_sync_capability_model.No_partial_probe_guard}
    deletes the [if last_consensus_number.is_none()] test at mod.rs:1091, so
    every [Unsupported] writes [false]. All three conjuncts fail at the state
    where a [Full_only] peer answered a partial probe with [Unsupported]:
    conjunct A because the slot's provenance is a partial probe, conjunct B
    because that slot is negative, and conjunct C because the eligibility filter
    at mod.rs:1066-1069 now drops the peer, so the later full probe that would
    have found it capable no longer exists. No sibling path repairs it: the
    consensus-output path filters on the same [Some(false)] (:626-629) and never
    writes [false] (:643-653); [MAX_EPOCH_SYNC_PROBES = 3] bounds the fan-out so
    other peers do not make up for it; and the epoch clear repairs it only at
    the next boundary, while a node that needs an epoch pack needs it inside
    this epoch. Neither of the other two gate deletions refutes any conjunct of
    S2 - see test/t_stream_sync_capability_mutation.ml. *)
let s2 =
  let negative_slots_come_from_a_full_probe =
    Formula.Ag
      (Formula.Implies (atom Cached_unsyncable, atom Cached_by_full_probe))
  in
  let an_ambiguous_partial_verdict_never_caches_false =
    Formula.Ag
      (Formula.Implies
         (atom Recent_partial_unsupported, Formula.Not (atom Cached_unsyncable)))
  in
  let the_protected_peer_stays_reachable =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [
               atom Recent_partial_unsupported;
               atom Answers_full_open;
               Formula.Not (atom Probe_budget_spent);
             ],
           Formula.Ex (atom Cached_capable) ))
  in
  {
    name = "only-a-full-pack-probe-writes-the-negative-capability-entry";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          negative_slots_come_from_a_full_probe;
          an_ambiguous_partial_verdict_never_caches_false;
          the_protected_peer_stays_reachable;
        ];
    antecedent = atom Recent_partial_unsupported;
  }

(** S3 - epoch-boundary-clear-restores-an-eligibility-the-excluded-peer-cannot-observe
    [fairness].

    A negative capability verdict is never permanent. Every epoch start runs
    [network_handle.clear_sync_capability();]
    (node/src/manager/node/start_epoch.rs:547-550), which is
    [self.sync_capability.lock().clear()] (mod.rs:409-416) under the doc
    "Called at each epoch boundary: committees rotate and binaries are upgraded
    there, so a peer that did not answer the sync protocol last epoch is
    re-probed for it this epoch." Without it one probe would exclude a peer from
    all three sync paths for the lifetime of the process, because the map has no
    TTL and no eviction.

    - Conjunct A (the anti-starvation guarantee): from every state at which [w]
      is cached unsyncable, the slot is INEVITABLY emptied - not merely possibly
      emptied. The peer returns to "not yet probed", the state the eligibility
      filter at mod.rs:1067 lets through.
    - Conjunct B (why the recovery must be unconditional): the excluded peer
      cannot observe its own exclusion, so there is no path by which it could
      ask to be re-probed. See the reading guide for the grounding of V1's view
      and the witness pair.

    MUTATION PIN. {!Stream_sync_capability_model.No_epoch_clear} deletes the
    call at start_epoch.rs:550. The boundary still advances the epoch and still
    resets the prober's own bookkeeping, but the slot survives, so a cached
    [false] cycles forever and conjunct A is refuted; conjunct B is untouched,
    which keeps the pin attributable. No sibling path repairs it: there is no
    TTL and no eviction (the only writers in the tree are the [insert] sites at
    mod.rs:634, :658, :1074, :1092, :1105 and this clear); no fresh handle
    resets the map incidentally, because [PrimaryNetworkHandle::new] runs once
    inside [spawn_node_networks] (node.rs:1117-1143), which [run] calls once
    before the epoch loop (node.rs:877), and every epoch merely CLONES the
    stored handle (start_epoch.rs:326-330) over a map held behind an [Arc]
    (mod.rs:380); both probe loops apply the same [Some(&false)] filter
    (:626-629, :1066-1069); and there is no legacy fallback route post-#739
    (mod.rs:607-608, :1053-1055).

    NOT MANUFACTURED LIVENESS (R8). The epoch boundary is modelled as always
    enabled - epochs end - and the mutation does NOT delete the boundary. It
    deletes the clear that runs at it, which is a real gate with a real call
    site, so the [AF] is refuted by losing the recovery rather than by losing
    the opportunity to recover. *)
let s3 =
  let the_negative_slot_is_inevitably_emptied =
    Formula.Ag
      (Formula.Implies (atom Cached_unsyncable, Formula.Af (atom Entry_unwritten)))
  in
  let the_excluded_peer_cannot_observe_its_exclusion =
    Formula.Ag
      (Formula.Implies
         ( atom Cached_unsyncable,
           Formula.Not (Formula.K (Validator.V1, atom Cached_unsyncable)) ))
  in
  {
    name =
      "epoch-boundary-clear-restores-an-eligibility-the-excluded-peer-cannot-observe";
    bucket = Statements.Fairness;
    formula =
      Formula.And
        ( the_negative_slot_is_inevitably_emptied,
          the_excluded_peer_cannot_observe_its_exclusion );
    antecedent = atom Cached_unsyncable;
  }

(** The family's statements. *)
let all = [ s1; s2; s3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure degrades
    every row to [proved = false] rather than raising. *)
let reports () =
  let row proved st = { Report.name = st.name; bucket = st.bucket; proved } in
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, r) ->
          row (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) r) st)
        (prove_all sys))
    ~error:(fun Checker.Empty_init -> List.map (row false) all)
    (make ())
