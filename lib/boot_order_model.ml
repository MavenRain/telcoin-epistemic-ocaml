(** Finite interpreted system for the BOOT-ORDER family: one node's startup
    sequence, from process start through the first [run_epoch] iteration, and
    the three cells that sequence writes before anything reads them.

    Mechanisms modeled, keyed to Telcoin-Association/telcoin-network (git
    0c59c15b, working tree):

    - {b the finalized-marker heal.} Blocks commit in
      [RethEnv::finish_executing_output] and the finalized/safe markers commit
      in [RethEnv::finalize_block] - two separate database transactions - so a
      crash between them restarts the node with [finalized marker < persisted
      canonical tip] (crates/tn-reth/src/lib.rs:855-864). Startup repairs that
      before anything reads the marker: crates/node/src/manager/node.rs:864
      [reth_env.heal_finalized_to_persisted_tip()?;] runs ahead of the epoch
      read at :866 and the accumulator restore at :869. The heal itself is
      crates/tn-reth/src/lib.rs:885-916 - one RO provider snapshot, [tip =
      provider.last_block_number()?] (:890), [finalized =
      provider.last_finalized_block_number()?.unwrap_or(0)] (:893), error when
      [finalized > tip] (:895-897), no-op when equal (:898-903), otherwise
      [self.finalize_block(header)] (:915). It has exactly ONE production call
      site (node.rs:864; the other hits are doc references and
      crates/node/tests/it/main.rs).
    - {b the accumulator restore.} [catchup_accumulator]
      (crates/node/src/manager/node.rs:189-272) pins every chain-derived input
      to the finalized header: :195 [if let Some(block) =
      reth_env.finalized_header()?], :200 [epoch_state_at_header(&block)],
      :234-235 [blocks_for_range(epoch_state.epoch_info.blockHeight..=
      block.number)], the per-worker gas fold at :253-260, and the leader
      count at :262-268. It never re-reads the persisted canonical tip, so a
      marker left lagging yields a SHORTER scan range and quietly-low gas
      totals with no error anywhere. The cross-view guard at :209-220 is not a
      repair: its own comment says it fires only when the two views disagree
      ACROSS an epoch boundary.
    - {b the recent-blocks priming.} node.rs:906
      [self.try_restore_state(&engine).await?;] backfills the in-memory
      [recent_blocks] watch from the executed chain (node.rs:1272-1296, the
      push at :1290-1292). The restart replay's lower watermark is read from
      that watch and from nowhere else: crates/node/src/manager/node/
      start_epoch.rs:77 calls [state_sync::get_missing_consensus], which
      derives [last_executed_block] at crates/state-sync/src/lib.rs:154-155
      and replays [last_executed_block.number + 1..=last_db_block.number]
      (:170); [last_executed_consensus_block]
      (crates/consensus/primary/src/consensus_bus.rs:672-688) reads
      [recent_blocks().borrow().latest_execution_block()] (:676), and on an
      empty window that returns a DEFAULT header
      (crates/consensus/primary/src/recent_blocks.rs:76-79) whose
      [parent_beacon_block_root] is [None], so the function returns [None]
      (:685-687), the watermark collapses to 0, and the whole epoch is
      re-forwarded. The priming and the heal are genuinely INDEPENDENT gates,
      which is why the model keeps them so: [last_executed_output_blocks]
      reads [self.reth_env.last_block_number()] - the persisted canonical tip
      (crates/node/src/engine/inner.rs:285) - and not the finalized marker
      that [last_executed_output] (:252) and [last_executed_blocks] (:264)
      read, so a marker left lagging does not truncate the window and cannot
      lower the replay watermark. tn-reth/src/lib.rs:872-875 states the same
      independence from the other direction.
    - {b the one-time network setup.} crates/node/src/manager/node/
      run_epoch.rs:255 [let network_first_init = epoch_mode.initial_epoch() ||
      !self.network_initialized;], threaded into [create_consensus] (:258-267)
      and landing on the two swarm binds, start_epoch.rs:507-515 (primary) and
      :669-676 (worker), plus the bootstrap registration at :780-782. The flag
      is set only after [create_consensus] returns (:269). The hard startup
      shape is the replay-and-close early return at :225-231, reached BEFORE
      [configure_consensus] (:245) and [create_consensus] (:258), which is why
      the gate cannot be keyed on [RunEpochMode::Initial] (the field's own doc
      says so verbatim, node.rs:99-111).

    {b Components.} The boot phase (a sequential chain), the finalized marker,
    the rebuilt accumulator, the [recent_blocks] window, the replay outcome,
    the hidden replay-and-close branch, the [network_initialized] flag, the
    listener bind counter, and the two directions of this node's link with one
    peer.

    {b Role mapping.} [V0] is the BOOTING NODE's epoch-manager control path -
    the agent that runs the sequence above. Its view is the state that path
    actually holds: the boot phase, whether its own [recent_blocks] watch has
    been seeded, its [network_initialized] flag, its bind count, and its p2p
    links in both directions. NOT in [V0]'s view: (a) the finalized-marker /
    persisted-tip pair, which lives behind [RethEnv]'s provider - the heal at
    tn-reth/src/lib.rs:885-916 is the only reader that ever compares them and
    it only warns (:908-914); (b) the rebuilt accumulator contents, which live
    behind [GasAccumulator] and are never re-derived for comparison (the
    short-scan failure is silent by construction); (c) whether the replay
    double-executed - the engine has no idempotence check at all
    (crates/engine/src/lib.rs:196-286 queues at :245-259 and executes on
    [self.parent_header] at :262-268) and reports nothing; (d) whether the
    persisted-but-unexecuted output is the epoch close, which is only resolved
    once [run_epoch] computes [self.epoch_boundary] (run_epoch.rs:140) and the
    replay compares [committed_at() >= self.epoch_boundary]
    (start_epoch.rs:91) - i.e. strictly after the boot decisions this family
    is about.

    [V1] is a PEER of the booting node. Its view is exactly its own two
    connection facts: whether the booting node dialed it (an inbound
    connection from V0's point of view is an outbound one from V1's) and
    whether V1's own dial of the booting node's advertised listen address
    succeeded. It sees nothing of the booting node's phase, marker, window or
    flags. [V2]..[V9] are idle non-agents with the constant blank view and
    never appear under K.

    {b Why the view projection is what it is.} The family's one positive
    knowledge claim is about a fact of ANOTHER node - that the booting node
    bound its swarm listener - and the model deliberately carries the sibling
    path that makes the naive version of that claim false: the swarms are
    spawned and running from node.rs:877 ([spawn_node_networks],
    node.rs:1106-1180), which is BEFORE the priming at :906 and long before
    any bind, so the booting node can hold an established outbound connection
    to a peer while its own listener is unbound. A peer that is merely
    connected therefore knows nothing about dialability; only a peer that
    itself completed a dial of the advertised listen address does. There is no
    transport-level repair for the unbound case: crates/network-libp2p has no
    relay/dcutr/autonat behaviour (the "relayer" identities in
    crates/network-libp2p/src/types.rs:221-257 are gossip forwarders, not
    transport relays).

    {b Hidden branching.} Two initial states, one per crash shape: the
    two-transaction crash window (marker lagging, mid-epoch unexecuted output)
    and the boundary crash (marker clean, the persisted unexecuted output IS
    the epoch close, so the first iteration replays-and-closes and returns
    early). The branch is invisible to [V0] until the replay resolves it,
    which is exactly the ignorance the [network_initialized] gate exists to
    tolerate. *)

(** The boot pipeline position. Each phase is one completed step of the real
    sequence: [Process_start] is the process with its engine started
    (node.rs:850-858) and nothing yet read; [Heal_done] is past
    [heal_finalized_to_persisted_tip] (node.rs:864); [Restore_done] is past
    [catchup_accumulator] (node.rs:869) - the marker reader; [Prime_done] is
    past [try_restore_state] (node.rs:906); [Entry_seeded] is past
    [run_epoch]'s epoch-entry seeding of worker count and base fees
    (run_epoch.rs:166-192); [Replay_done] is past [replay_missed_consensus]
    (run_epoch.rs:220-239); [Close_reentry] is the replay-and-close early
    return (run_epoch.rs:225-231) that never reaches [create_consensus];
    [Setup_done] is past [create_consensus] (run_epoch.rs:258-269);
    [Epoch_live] is the running epoch loop and is terminal (the kernel
    stutter-closes it). *)
type phase =
  | Process_start
  | Heal_done
  | Restore_done
  | Prime_done
  | Entry_seeded
  | Replay_done
  | Close_reentry
  | Setup_done
  | Epoch_live

(** Total order index for {!phase}. *)
let phase_index = function
  | Process_start -> 0
  | Heal_done -> 1
  | Restore_done -> 2
  | Prime_done -> 3
  | Entry_seeded -> 4
  | Replay_done -> 5
  | Close_reentry -> 6
  | Setup_done -> 7
  | Epoch_live -> 8

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The finalized marker relative to the persisted canonical tip:
    [Marker_lagging] is the two-transaction crash window
    (tn-reth/src/lib.rs:855-864), [Marker_at_tip] is the healed or
    never-lagging marker. *)
type marker = Marker_lagging | Marker_at_tip

(** Total order index for {!marker}. *)
let marker_index = function Marker_lagging -> 0 | Marker_at_tip -> 1

(** Total order on {!marker}. *)
let marker_compare a b = Int.compare (marker_index a) (marker_index b)

(** What the accumulator restore rebuilt: [Rebuild_pending] before the restore
    ran, [Rebuild_short] when the scan range ended at a lagging marker
    (node.rs:234-235 with a stale [block.number]) so the per-worker gas totals
    and the leader-count bound (node.rs:262-268) drop the gap blocks, and
    [Rebuild_full] when the range ended at the true tip. *)
type rebuild = Rebuild_pending | Rebuild_short | Rebuild_full

(** Total order index for {!rebuild}. *)
let rebuild_index = function
  | Rebuild_pending -> 0
  | Rebuild_short -> 1
  | Rebuild_full -> 2

(** Total order on {!rebuild}. *)
let rebuild_compare a b = Int.compare (rebuild_index a) (rebuild_index b)

(** The in-memory [recent_blocks] watch: [Window_empty] is the process-start
    state the priming exists to fix (node.rs:1266-1271), [Window_seeded] is
    primed from the executed chain (node.rs:1290-1292). *)
type window = Window_empty | Window_seeded

(** Total order index for {!window}. *)
let window_index = function Window_empty -> 0 | Window_seeded -> 1

(** Total order on {!window}. *)
let window_compare a b = Int.compare (window_index a) (window_index b)

(** The restart replay's outcome: [Replay_pending] before it ran,
    [Replay_clean] when its watermark came from a seeded window, and
    [Replay_double] when the empty window collapsed the watermark to 0
    (state-sync/src/lib.rs:154-155 via consensus_bus.rs:685-687) and the
    replay re-forwarded output the engine had already executed
    (state-sync/src/lib.rs:170). *)
type replay = Replay_pending | Replay_clean | Replay_double

(** Total order index for {!replay}. *)
let replay_index = function
  | Replay_pending -> 0
  | Replay_clean -> 1
  | Replay_double -> 2

(** Total order on {!replay}. *)
let replay_compare a b = Int.compare (replay_index a) (replay_index b)

(** How many times the one-time per-process swarm setup has bound a listener
    (start_epoch.rs:507-515, :669-676). Capped at two: the model never needs a
    third, and a bare counter would be an unbounded state component. *)
type binds = Bind_none | Bind_once | Bind_twice

(** Total order index for {!binds}. *)
let binds_index = function
  | Bind_none -> 0
  | Bind_once -> 1
  | Bind_twice -> 2

(** Total order on {!binds}. *)
let binds_compare a b = Int.compare (binds_index a) (binds_index b)

(** One more bind, saturating at {!Bind_twice}. *)
let bind_succ = function
  | Bind_none -> Bind_once
  | Bind_once -> Bind_twice
  | Bind_twice -> Bind_twice

(** Has any listener been bound. *)
let bound_already = function
  | Bind_none -> false
  | Bind_once | Bind_twice -> true

(** The joint global state of the booting node plus its link with the peer
    [V1]. [close_pending] is the hidden crash shape (is the persisted
    unexecuted output the epoch close), [net_init] is the real
    [network_initialized] field (node.rs:111), [linked] is the booting node's
    own outbound connection to the peer (possible from the swarm spawn at
    node.rs:877 onward, well before any bind), and [inbound_ok] records that
    the peer's own dial of the booting node's advertised listen address
    succeeded. *)
type state = {
  phase : phase;
  marker : marker;
  rebuilt : rebuild;
  window : window;
  replay : replay;
  close_pending : bool;
  net_init : bool;
  binds : binds;
  linked : bool;
  inbound_ok : bool;
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c0 = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = marker_compare s1.marker s2.marker in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = rebuild_compare s1.rebuilt s2.rebuilt in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = window_compare s1.window s2.window in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = replay_compare s1.replay s2.replay in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Bool.compare s1.close_pending s2.close_pending in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = Bool.compare s1.net_init s2.net_init in
              if Bool.not (Int.equal c6 0) then c6
              else
                let c7 = binds_compare s1.binds s2.binds in
                if Bool.not (Int.equal c7 0) then c7
                else
                  let c8 = Bool.compare s1.linked s2.linked in
                  if Bool.not (Int.equal c8 0) then c8
                  else Bool.compare s1.inbound_ok s2.inbound_ok

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view.

    [View_boot (phase, window, net_init, binds, linked, inbound_ok)] is the
    booting node [V0]: the control state its epoch manager actually holds. It
    does NOT carry the marker/tip pair, the rebuilt accumulator contents, the
    replay's double-execution outcome, or the hidden replay-and-close branch -
    see the module header for the file:line justification of each exclusion.

    [View_peer (linked, inbound_ok)] is the peer [V1]: exactly its two
    connection facts about the booting node and nothing else.

    [View_idle] is the constant blank view of the non-agents [V2]..[V9]. *)
type view =
  | View_boot of phase * window * bool * binds * bool * bool
  | View_peer of bool * bool
  | View_idle

(** Total order on the booting node's view tuple. *)
let view_boot_compare (p1, w1, n1, b1, l1, i1) (p2, w2, n2, b2, l2, i2) =
  let c0 = phase_compare p1 p2 in
  if Bool.not (Int.equal c0 0) then c0
  else
    let c1 = window_compare w1 w2 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Bool.compare n1 n2 in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = binds_compare b1 b2 in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare l1 l2 in
          if Bool.not (Int.equal c4 0) then c4 else Bool.compare i1 i2

(** Total order on the peer's view pair. *)
let view_peer_compare (l1, i1) (l2, i2) =
  let c0 = Bool.compare l1 l2 in
  if Bool.not (Int.equal c0 0) then c0 else Bool.compare i1 i2

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_boot _ | View_peer _) -> -1
  | (View_boot _ | View_peer _), View_idle -> 1
  | View_boot (p1, w1, n1, b1, l1, i1), View_boot (p2, w2, n2, b2, l2, i2) ->
      view_boot_compare (p1, w1, n1, b1, l1, i1) (p2, w2, n2, b2, l2, i2)
  | View_boot _, View_peer _ -> -1
  | View_peer _, View_boot _ -> 1
  | View_peer (l1, i1), View_peer (l2, i2) ->
      view_peer_compare (l1, i1) (l2, i2)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. [V0] is the booting node, [V1] its peer; [V2]..[V9] are
    idle non-agents with the constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_boot (s.phase, s.window, s.net_init, s.binds, s.linked, s.inbound_ok)
  | Validator.V1 -> View_peer (s.linked, s.inbound_ok)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_marker_heal
      (** delete crates/node/src/manager/node.rs:864
          ([reth_env.heal_finalized_to_persisted_tip()?;]), so the
          [Process_start -> Heal_done] step no longer moves the marker to the
          tip and the restore's scan range ends at the stale marker
          ([Rebuild_short] instead of [Rebuild_full]). No sibling path repairs
          it: node.rs:864 is the SOLE production call site of the single
          definition at crates/tn-reth/src/lib.rs:885, and every other marker
          reader consumes the marker without re-deriving it from the tip
          (crates/node/src/engine/inner.rs:242-260, :263-276, :150); the
          cross-view guard at node.rs:209-220 fires only across an epoch
          boundary, by its own comment. The one genuine partial repair -
          [run_epoch]'s epoch-entry re-derivation of worker count and base
          fees (run_epoch.rs:166-192) - IS modeled, as the [Entry_seeded]
          phase, and does not touch the per-worker gas totals or the leader
          counts the restore rebuilds. *)
  | No_recent_blocks_prime
      (** delete crates/node/src/manager/node.rs:906
          ([self.try_restore_state(&engine).await?;]), so the [Restore_done ->
          Prime_done] step leaves [recent_blocks] empty, the replay watermark
          collapses to 0 (consensus_bus.rs:685-687 via
          recent_blocks.rs:76-79, state-sync/src/lib.rs:154-155) and the
          replay re-forwards already-executed output (state-sync/src/
          lib.rs:170), adding a [Replay_double] state. No sibling path repairs
          it: the engine has no idempotence check whatsoever
          (crates/engine/src/lib.rs:196-286), [check_output_continuity] is by
          design NOT applied to the replay path (run_epoch.rs:878-891, doc at
          :880-882), and [spawn_engine_update_task] (node.rs:1305-1322) only
          pushes NEW engine updates so it cannot back-fill the window before
          the first replay. The startup prime of
          [last_forwarded_consensus_number] (node.rs:832-833) reads
          [last_consensus_parent], which takes the MAX of the db-latest and
          executed anchors (state-sync/src/lib.rs:131-144) and so survives an
          empty window - but it feeds only the live path's continuity check,
          which the replay path is excluded from. *)
  | Initial_only_network_gate
      (** delete the [|| !self.network_initialized] disjunct at
          crates/node/src/manager/node/run_epoch.rs:255, leaving
          [epoch_mode.initial_epoch()]. On the replay-and-close startup shape
          the first iteration returns early at :225-231 before
          [create_consensus], and the following iteration carries
          [RunEpochMode::NewEpoch], so the bind transition disappears
          entirely. No sibling path repairs it: [start_listening] has exactly
          two non-test call sites (start_epoch.rs:514 and :675), both under
          the same [if initial_epoch] guard; the acknowledged sibling on this
          very path repairs the WORKER COMPONENTS only
          ([if initial_epoch || !engine.are_workers_initialized().await]
          at start_epoch.rs:395); the peer layer's [update_committees] and kad
          work operate on an already-bound swarm; and crates/network-libp2p
          has no relay/dcutr/autonat transport that could make an unbound node
          reachable. *)
  | Rebind_on_replay
      (** insert a [start_listening] on the replay-and-close early-return path
          (crates/node/src/manager/node/run_epoch.rs:225-231) - the naive fix
          for the deferred bind - so the [Replay_done -> Close_reentry] step
          binds and the following [create_consensus] binds again (the flag at
          run_epoch.rs:269 is still only set after [create_consensus]
          returns), reaching [Bind_twice]. Nothing absorbs the duplicate:
          there is no unbind, dedup or listener-release path anywhere in
          crates/network-libp2p, and [start_listening]'s error is propagated
          with [?] at start_epoch.rs:514, so a duplicate is either a second
          listener or a hard startup failure - the model takes the
          second-listener reading. *)

(** The heal step of node.rs:864: the marker is repaired to the persisted
    canonical tip (tn-reth/src/lib.rs:905-915), except where the mutation
    deletes the call. *)
let heal_marker mut m =
  match mut with
  | Pristine | No_recent_blocks_prime | Initial_only_network_gate
  | Rebind_on_replay ->
      Marker_at_tip
  | No_marker_heal -> m

(** The accumulator restore of node.rs:189-272: the scan range ends at the
    finalized header (:234-235), so the rebuild is complete exactly when the
    marker is at the tip. *)
let restore_rebuild m =
  match m with
  | Marker_at_tip -> Rebuild_full
  | Marker_lagging -> Rebuild_short

(** The [recent_blocks] priming of node.rs:906/:1290-1292, except where the
    mutation deletes the call. *)
let prime_window mut =
  match mut with
  | Pristine | No_marker_heal | Initial_only_network_gate | Rebind_on_replay ->
      Window_seeded
  | No_recent_blocks_prime -> Window_empty

(** The replay of run_epoch.rs:220-239: its watermark comes from the
    [recent_blocks] window and from nowhere else, so an empty window
    re-forwards already-executed output. *)
let replay_outcome w =
  match w with
  | Window_seeded -> Replay_clean
  | Window_empty -> Replay_double

(** [network_first_init] of run_epoch.rs:255, with the mutation deleting the
    [|| !self.network_initialized] disjunct. *)
let network_first_init mut ~initial_epoch ~net_init =
  match mut with
  | Pristine | No_marker_heal | No_recent_blocks_prime | Rebind_on_replay ->
      initial_epoch || Bool.not net_init
  | Initial_only_network_gate -> initial_epoch

(** Whether the replay-and-close early return also binds a listener - false in
    the real code (it returns at run_epoch.rs:230 before [create_consensus]),
    true under the naive-fix mutation. *)
let reentry_binds mut =
  match mut with
  | Pristine | No_marker_heal | No_recent_blocks_prime
  | Initial_only_network_gate ->
      false
  | Rebind_on_replay -> true

(** The [create_consensus] step (run_epoch.rs:258-269): run the one-time
    network setup iff the gate says so, then set [network_initialized]
    unconditionally (:269 runs whether or not the setup was performed). *)
let setup_step mut ~initial_epoch s =
  {
    s with
    phase = Setup_done;
    net_init = true;
    binds =
      (if network_first_init mut ~initial_epoch ~net_init:s.net_init then
         bind_succ s.binds
       else s.binds);
  }

(** The booting node's own step, one completed call of the real sequence per
    transition. [Epoch_live] is terminal; the kernel stutter-closes it.

    The [Close_reentry -> Setup_done] step abstracts the whole following
    [run_epoch] iteration: it re-runs the entry seeding (run_epoch.rs:166-192)
    and a second [replay_missed_consensus] (:220-239, [NewEpoch] also replays
    - run_epoch.rs:66-71) before [create_consensus]. Neither re-write changes a
    modeled cell: the fees are already reseeded, the epoch's consensus DB was
    cleared at :229 so the second replay finds nothing, and neither can heal a
    marker, prime a window or bind a listener. *)
let boot_step mut s =
  match s.phase with
  | Process_start ->
      [ { s with phase = Heal_done; marker = heal_marker mut s.marker } ]
  | Heal_done ->
      [ { s with phase = Restore_done; rebuilt = restore_rebuild s.marker } ]
  | Restore_done -> [ { s with phase = Prime_done; window = prime_window mut } ]
  | Prime_done -> [ { s with phase = Entry_seeded } ]
  | Entry_seeded ->
      [ { s with phase = Replay_done; replay = replay_outcome s.window } ]
  | Replay_done ->
      if s.close_pending then
        [
          {
            s with
            phase = Close_reentry;
            binds = (if reentry_binds mut then bind_succ s.binds else s.binds);
          };
        ]
      else [ setup_step mut ~initial_epoch:true s ]
  | Close_reentry -> [ setup_step mut ~initial_epoch:false s ]
  | Setup_done -> [ { s with phase = Epoch_live } ]
  | Epoch_live -> []

(** The booting node's outbound connection to the peer. The swarms are created
    and running from node.rs:877 ([spawn_node_networks], node.rs:1106-1180),
    which is after the accumulator restore and before the priming, so an
    outbound link is available from [Restore_done] onward - independently of
    whether any listener has been bound. This is the sibling path that makes a
    naive "the peer is connected, so the node is reachable" claim false. *)
let link_step s =
  if s.linked then []
  else
    match s.phase with
    | Process_start | Heal_done -> []
    | Restore_done | Prime_done | Entry_seeded | Replay_done | Close_reentry
    | Setup_done | Epoch_live ->
        [ { s with linked = true } ]

(** The peer's own dial of the booting node's advertised listen address
    (the counterpart of start_epoch.rs:684-690's dial loop): it can only
    succeed once a listener is actually bound. *)
let inbound_step s =
  if s.inbound_ok then []
  else if bound_already s.binds then [ { s with inbound_ok = true } ]
  else []

(** The transition relation: the boot advances, the peer link comes up, and
    the peer's dial lands - interleaved, one component per step. *)
let next_with mut s = boot_step mut s @ link_step s @ inbound_step s

(** The pristine transition relation. *)
let next = next_with Pristine

(** Initial state 1 - the two-transaction crash window: the node died between
    the blocks-commit and the finalize-commit (tn-reth/src/lib.rs:855-859), so
    the marker lags the persisted canonical tip, and the persisted
    unexecuted consensus output is mid-epoch. *)
let initial =
  {
    phase = Process_start;
    marker = Marker_lagging;
    rebuilt = Rebuild_pending;
    window = Window_empty;
    replay = Replay_pending;
    close_pending = false;
    net_init = false;
    binds = Bind_none;
    linked = false;
    inbound_ok = false;
  }

(** Initial state 2 - the boundary crash: the marker committed cleanly, but
    the persisted-but-unexecuted output IS the epoch close, so the first
    [run_epoch] iteration replays-and-closes and returns at run_epoch.rs:230
    before [create_consensus] ever runs. This is precisely the crash window
    [replay_missed_consensus] exists for. *)
let initial_boundary_replay = { initial with marker = Marker_at_tip; close_pending = true }

(** Both startup shapes; the checker quantifies over every one of them. *)
let inits = [ initial; initial_boundary_replay ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Marker_healed_to_tip
      (** the finalized marker equals the persisted canonical tip - the
          post-condition of node.rs:864 *)
  | Restore_ran
      (** [catchup_accumulator] has run (node.rs:869), i.e. the startup marker
          reader has consumed the marker (node.rs:195) and rebuilt the
          per-worker gas totals and leader counts (:253-268) *)
  | Totals_complete
      (** the rebuilt totals cover the whole epoch: the scan range
          (node.rs:234-235) ended at the true tip rather than at a stale
          marker *)
  | Fees_reseeded
      (** [run_epoch]'s epoch-entry seeding has re-derived the worker count
          and per-worker base fees from the previous epoch's closing block
          (run_epoch.rs:166-192) - the acknowledged partial repair, which
          covers the FEES and not the restore's gas totals or leader counts *)
  | Recent_blocks_seeded
      (** the in-memory [recent_blocks] watch has been primed from the
          executed chain (node.rs:906, :1290-1292) *)
  | Replay_ran
      (** [replay_missed_consensus] has run (run_epoch.rs:220-239) *)
  | Double_executed
      (** the replay re-forwarded consensus output the engine had already
          executed (state-sync/src/lib.rs:170 off a collapsed watermark) *)
  | Close_on_replay
      (** the persisted-but-unexecuted output is the epoch close, so this
          iteration replays-and-closes (run_epoch.rs:225-231) - the hidden
          startup shape *)
  | Listener_bound
      (** [start_listening] has bound this node's swarm listener
          (start_epoch.rs:514, :675) *)
  | Bound_exactly_once
      (** the one-time per-process setup has bound exactly one listener *)
  | Peer_linked
      (** the booting node holds an outbound connection to the peer - possible
          from the swarm spawn at node.rs:877 onward, with or without a bound
          listener *)
  | Peer_dialed_in
      (** the peer's own dial of this node's advertised listen address
          succeeded, so the node is genuinely reachable *)
  | Epoch_running  (** the epoch loop is live (run_epoch.rs:270 onward) *)

(** Has the boot reached or passed [Restore_done]. *)
let restore_done p =
  match p with
  | Process_start | Heal_done -> false
  | Restore_done | Prime_done | Entry_seeded | Replay_done | Close_reentry
  | Setup_done | Epoch_live ->
      true

(** Has the boot reached or passed [Entry_seeded]. *)
let entry_seeded p =
  match p with
  | Process_start | Heal_done | Restore_done | Prime_done -> false
  | Entry_seeded | Replay_done | Close_reentry | Setup_done | Epoch_live -> true

(** Has the boot reached or passed [Replay_done]. *)
let replay_done p =
  match p with
  | Process_start | Heal_done | Restore_done | Prime_done | Entry_seeded ->
      false
  | Replay_done | Close_reentry | Setup_done | Epoch_live -> true

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Marker_healed_to_tip -> (
      match s.marker with Marker_at_tip -> true | Marker_lagging -> false)
  | Restore_ran -> restore_done s.phase
  | Totals_complete -> (
      match s.rebuilt with
      | Rebuild_full -> true
      | Rebuild_pending | Rebuild_short -> false)
  | Fees_reseeded -> entry_seeded s.phase
  | Recent_blocks_seeded -> (
      match s.window with Window_seeded -> true | Window_empty -> false)
  | Replay_ran -> replay_done s.phase
  | Double_executed -> (
      match s.replay with
      | Replay_double -> true
      | Replay_pending | Replay_clean -> false)
  | Close_on_replay -> s.close_pending
  | Listener_bound -> bound_already s.binds
  | Bound_exactly_once -> (
      match s.binds with
      | Bind_once -> true
      | Bind_none | Bind_twice -> false)
  | Peer_linked -> s.linked
  | Peer_dialed_in -> s.inbound_ok
  | Epoch_running -> (
      match s.phase with
      | Epoch_live -> true
      | Process_start | Heal_done | Restore_done | Prime_done | Entry_seeded
      | Replay_done | Close_reentry | Setup_done ->
          false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Marker_healed_to_tip -> "marker-at-tip"
  | Restore_ran -> "restore-ran"
  | Totals_complete -> "totals-complete"
  | Fees_reseeded -> "fees-reseeded"
  | Recent_blocks_seeded -> "recent-blocks-seeded"
  | Replay_ran -> "replay-ran"
  | Double_executed -> "double-executed"
  | Close_on_replay -> "close-on-replay"
  | Listener_bound -> "listener-bound"
  | Bound_exactly_once -> "bound-exactly-once"
  | Peer_linked -> "peer-linked"
  | Peer_dialed_in -> "peer-dialed-in"
  | Epoch_running -> "epoch-running"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} at every
    reachable world by test/t_boot_order_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: both startup shapes as initial states,
    mutation-parameterized transitions, the two-agent view, atom valuation. *)
let spec_of mut = { Checker.init = inits; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
