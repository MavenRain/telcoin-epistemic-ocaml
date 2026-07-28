(** The BOOT-ORDER family statements, encoded over the {!Boot_order_model}
    interpreted system. Every mechanism claim was re-verified against
    Telcoin-Association/telcoin-network at git 0c59c15b (working tree) while
    writing this module; file citations are to that checkout.

    What was mined: the three ordering obligations of one node's startup
    sequence. Each of the three cells the sequence writes - the finalized
    marker, the [recent_blocks] window, the swarm listener - is read by a
    later step that has no way to detect that the write is missing, so the
    only thing standing between a restart and a silent corruption is the order
    of a handful of calls inside [EpochManager::run] and the first
    [run_epoch].

    {b Reading guide for the K operands.}

    - S3's positive [K_V1 (listener-bound)] is knowledge of ANOTHER node's
      act. It is not a projection of the peer's own view in any degenerate
      sense: the model carries the sibling path that makes the naive version
      false - the booting node's swarms are spawned and running from
      node.rs:877, long before any bind, so the peer can hold an established
      connection FROM the booting node while that node's listener is unbound.
      At the peer's [linked, not-dialed-in] view class both truth values of
      [listener-bound] are reachable, so knowledge there genuinely fails; only
      the peer's OWN completed dial of the advertised listen address
      discriminates. The operand is contingent (false at every pre-bind state)
      and the operative view class holds several reachable states, both
      discharged by tests in test/t_boot_order.ml.
    - S3's [not K_V0 (close-on-replay)] is the design rationale of the
      [network_initialized] field stated as ignorance: at the moment the boot
      is deciding how to gate its one-time network setup, the booting node
      does not yet know whether this iteration will replay-and-close, because
      that is only resolved once [run_epoch] has computed [self.epoch_boundary]
      (run_epoch.rs:140) and the replay has compared [committed_at() >=
      self.epoch_boundary] (start_epoch.rs:91). The witness pair is the two
      initial startup shapes: at every pre-replay phase the two branches carry
      an identical [V0] view and disagree on [close-on-replay].

    S1 and S2 carry NO K on purpose. Both assert a property the pristine model
    makes inevitable ([totals-complete] after the restore, [not
    double-executed] everywhere), so any [K_V0] of them would be rigid inside
    the operative view class and epistemically empty; they are stated as the
    plain ordering facts they are. *)

open Boot_order_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so a statement is never certified on
          the strength of an unreachable antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** [A\[p W q\]], the kernel identity for weak until: no path ever reaches a
    [p]-violating state without having passed a [q]-state first. *)
let weak_until p q =
  Formula.Not (Formula.Eu (Formula.Not q, Formula.And (Formula.Not p, Formula.Not q)))

(** S1 - finalized-marker-heal-precedes-every-startup-state-rebuild [safety].

    Conjunct A - [AG (restore-ran -> totals-complete)]: whenever the startup
    accumulator restore has run, the totals it rebuilt cover the whole epoch.
    The restore pins every chain-derived input to the finalized header
    (crates/node/src/manager/node.rs:195 [finalized_header()], :200
    [epoch_state_at_header], :234-235
    [blocks_for_range(epoch_info.blockHeight..=block.number)]) and folds the
    per-worker gas totals at :253-260 and the leader count at :262-268, so a
    marker left lagging by a crash between the blocks-commit and the
    finalize-commit transactions (crates/tn-reth/src/lib.rs:855-864) would end
    the scan short and produce quietly-low totals with no error anywhere.

    Conjunct B - [A\[not restore-ran W marker-at-tip\]]: the ordering itself.
    No state is reachable in which the marker reader has run while the marker
    still lags: crates/node/src/manager/node.rs:864
    [reth_env.heal_finalized_to_persisted_tip()?;] is sequenced ahead of the
    epoch read at :866 and the restore at :869, and the heal routes through
    [finalize_block] (crates/tn-reth/src/lib.rs:915) precisely so the
    in-memory watches the later readers consult are moved too (:866-870). The
    restore is the modeled representative of the marker readers; the others
    (crates/node/src/engine/inner.rs:242-260, :263-276, :150) sit strictly
    later on the same path.

    Mutation pin: [No_marker_heal] deletes node.rs:864, removing the marker
    write from the [Process_start -> Heal_done] step. On the crash-window
    initial state the marker stays lagging, the restore rebuilds [short], and
    both conjuncts fail. No sibling path repairs it: that line is the sole
    production call site of the single definition at tn-reth/src/lib.rs:885,
    no other marker reader re-derives the marker from the tip, and the
    cross-view guard at node.rs:209-220 fires only across an epoch boundary.
    The one genuine partial repair, [run_epoch]'s epoch-entry re-derivation of
    the worker count and base fees (run_epoch.rs:166-192), is modeled as the
    [Entry_seeded] phase and is deliberately NOT what this statement is about:
    it repairs the fees, not the gas totals or the leader counts. *)
let s1 =
  let restore_is_complete =
    Formula.Ag (Formula.Implies (atom Restore_ran, atom Totals_complete))
  in
  let heal_precedes_the_reader =
    weak_until (Formula.Not (atom Restore_ran)) (atom Marker_healed_to_tip)
  in
  {
    name = "finalized-marker-heal-precedes-every-startup-state-rebuild";
    bucket = Statements.Safety;
    formula = Formula.And (restore_is_complete, heal_precedes_the_reader);
    antecedent = Formula.And (atom Restore_ran, atom Totals_complete);
  }

(** S2 - recent-blocks-restore-precedes-the-replay-watermark [safety].

    Conjunct A - [A\[not replay-ran W recent-blocks-seeded\]]: restart replay
    never runs before the in-memory [recent_blocks] window has been primed
    from the executed chain. The priming is
    crates/node/src/manager/node.rs:906 [self.try_restore_state(&engine)],
    which walks [engine.last_executed_output_blocks] (:1276) and pushes each
    into the watch (:1290-1292); the replay is run_epoch.rs:220-239, whose
    watermark comes from start_epoch.rs:77
    [state_sync::get_missing_consensus], i.e. from
    crates/state-sync/src/lib.rs:154-155 and nowhere else.

    Conjunct B - [AG (not double-executed)]: consequently the replay never
    re-forwards an output the engine has already executed. On an empty window
    [last_executed_consensus_block] returns the DEFAULT header
    (crates/consensus/primary/src/recent_blocks.rs:76-79), whose
    [parent_beacon_block_root] is [None], so the function returns [None]
    (crates/consensus/primary/src/consensus_bus.rs:685-687), the watermark
    collapses to 0 and state-sync/src/lib.rs:170 replays [1..=last_db].

    Mutation pin: [No_recent_blocks_prime] deletes node.rs:906, so the window
    is still empty when the replay derives its watermark: conjunct A fails at
    the [Replay_done] state and conjunct B fails with it. No sibling path
    repairs it - the engine has no idempotence check of any kind
    (crates/engine/src/lib.rs:196-286: it queues at :245-259 and executes on
    [self.parent_header] at :262-268), [check_output_continuity] is by design
    not applied to the replay path (run_epoch.rs:878-891, its doc at :880-882
    saying replay "legitimately re-forward[s] numbers at or below
    last_forwarded"), and [spawn_engine_update_task] (node.rs:1305-1322) only
    pushes NEW engine updates. The one startup anchor that does survive an
    empty window, [last_consensus_parent]'s max() at
    state-sync/src/lib.rs:131-144 (primed at node.rs:832-833), feeds the LIVE
    path's continuity check only, which is exactly why the priming gap is
    invisible there and bites only [get_missing_consensus].

    S1's gate is not a hidden co-dependency of this one, and that was checked
    rather than assumed: [try_restore_state] primes the window through
    [last_executed_output_blocks], which reads
    [self.reth_env.last_block_number()] - the persisted canonical tip
    (crates/node/src/engine/inner.rs:285) - not the finalized marker read by
    [last_executed_output] (:252) and [last_executed_blocks] (:264). A marker
    left lagging therefore cannot truncate the window or lower the watermark,
    which is why [No_marker_heal] leaves this statement proving (asserted in
    test/t_boot_order_mutation.ml's targeting group) and tn-reth/src/lib.rs:
    872-875 can claim replay is unaffected by the heal.

    The antecedent is [replay-ran] alone - the operative situation - because a
    seeded-window antecedent would be unreachable under the very mutation that
    deletes the seeding, and the pin would then report vacuity instead of the
    genuine refutation it is. *)
let s2 =
  let prime_precedes_replay =
    weak_until (Formula.Not (atom Replay_ran)) (atom Recent_blocks_seeded)
  in
  let no_double_execution = Formula.Ag (Formula.Not (atom Double_executed)) in
  {
    name = "recent-blocks-restore-precedes-the-replay-watermark";
    bucket = Statements.Safety;
    formula = Formula.And (prime_precedes_replay, no_double_execution);
    antecedent = atom Replay_ran;
  }

(** S3 - swarm-listener-binds-exactly-once-even-when-startup-replays-and-closes
    [liveness].

    Conjunct A - [AF (listener-bound)]: on EVERY startup shape the one-time
    per-process swarm setup eventually runs. The hard shape is a restart that
    replays a persisted epoch-boundary output: that iteration returns at
    crates/node/src/manager/node/run_epoch.rs:230
    ([close_epoch] :228, [clear_consensus_db_for_next_epoch] :229) before
    [configure_consensus] (:245) and [create_consensus] (:258) are ever
    reached, so a gate keyed on [RunEpochMode::Initial] would skip the bind
    forever. The real gate at :255 is
    [epoch_mode.initial_epoch() || !self.network_initialized], with the flag
    set only after [create_consensus] returns (:269), so the setup is merely
    deferred to the next iteration.

    Conjunct B - [AG (listener-bound -> AG (bound-exactly-once))]: and it runs
    exactly once. [start_listening] has exactly two non-test call sites
    (start_epoch.rs:514 primary, :675 worker), both under the same
    [if initial_epoch] guard fed by that flag.

    Conjunct C - [AG (peer-dialed-in -> K_V1 (listener-bound))]: a peer that
    has itself completed a dial of this node's advertised listen address
    KNOWS the listener is bound. The operand is another node's act, and the
    claim is keyed on the peer's own inbound dial rather than on connectivity
    for a concrete reason: the booting node's swarms run from node.rs:877
    ([spawn_node_networks], node.rs:1106-1180) - before the priming at :906
    and long before any bind - so an outbound connection from the booting node
    proves nothing about its reachability. That sibling path is in the model,
    and at the peer's linked-but-not-dialed-in view class both truth values of
    [listener-bound] are reachable, so this knowledge is contingent, not
    structural. crates/network-libp2p carries no relay/dcutr/autonat
    behaviour, so an unbound node has no other route to reachability.

    Conjunct D - [AG (not replay-ran -> not K_V0 (close-on-replay))]: at every
    pre-replay state the booting node does NOT know whether this iteration is
    the replay-and-close shape. That is why the setup gate cannot be keyed on
    the epoch mode: the shape is resolved only once [run_epoch] has computed
    [self.epoch_boundary] (run_epoch.rs:140) and the replay has compared
    [consensus_output.committed_at() >= self.epoch_boundary]
    (start_epoch.rs:91), strictly after the boot decisions this family is
    about. Witness pair: the two initial startup shapes carry an identical
    [V0] view at every pre-replay phase and disagree on [close-on-replay].

    Mutation pins. [Initial_only_network_gate] deletes the
    [|| !self.network_initialized] disjunct at run_epoch.rs:255: on the
    boundary startup shape the first iteration returns early and every
    following one carries [RunEpochMode::NewEpoch], so the bind never happens
    and conjunct A is refuted. [Rebind_on_replay] inserts the naive fix - a
    bind on the early-return path itself - so the deferred setup binds a
    second listener and conjunct B is refuted. Neither is silently repaired:
    there is no second bind route, no unbind, and no dedup anywhere in
    crates/network-libp2p; the acknowledged sibling on this same restart path,
    [if initial_epoch || !engine.are_workers_initialized().await]
    (start_epoch.rs:395), repairs the worker COMPONENTS and says so in its
    comment (:390-394), which is evidence the hazard is real and evidence that
    the listener is not covered by it. *)
let s3 =
  let eventually_bound = Formula.Af (atom Listener_bound) in
  let bound_exactly_once =
    Formula.Ag
      (Formula.Implies
         (atom Listener_bound, Formula.Ag (atom Bound_exactly_once)))
  in
  let dial_grounds_knowledge =
    Formula.Ag
      (Formula.Implies
         ( atom Peer_dialed_in,
           Formula.K (Validator.V1, atom Listener_bound) ))
  in
  let shape_unknown_at_gate_time =
    Formula.Ag
      (Formula.Implies
         ( Formula.Not (atom Replay_ran),
           Formula.Not (Formula.K (Validator.V0, atom Close_on_replay)) ))
  in
  {
    name = "swarm-listener-binds-exactly-once-even-when-startup-replays-and-closes";
    bucket = Statements.Liveness;
    formula =
      Formula.conj
        [
          eventually_bound;
          bound_exactly_once;
          dial_grounds_knowledge;
          shape_unknown_at_gate_time;
        ];
    antecedent = Formula.And (atom Peer_dialed_in, atom Listener_bound);
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
