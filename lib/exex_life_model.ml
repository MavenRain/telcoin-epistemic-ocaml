(** Finite interpreted system for the EXEX_LIFE family: the Execution-Extension
    (ExEx) notification surface of ONE consensus-following telcoin-network host.
    File citations refer to Telcoin-Association/telcoin-network (HEAD 0c59c15b);
    every cited span was opened in this checkout.

    THE MODELED HOST. V1 is an Observer or an inactive CVV - the only two node
    modes that reach [handle_sync_output] (subscriber.rs:100-129 spawns
    [catch_up_rejoin_consensus] / [follow_consensus]; subscriber.rs:169-174
    states outright that the active-validator path deliberately omits ExEx
    delivery) and the only ones for which [notify_exex_certificate] fires
    (handler.rs:274 gates it on [!is_active_cvv]). A host on the ExEx delivery
    path therefore publishes no [ConsensusResult] of its own, which is why V2 is
    given a network-side view rather than a "compare V1's votes" view.

    THE THREE MECHANISMS, all reachable from the two [notify_exex_*] producers
    on {!Consensus_bus} (consensus_bus.rs:582-608):

    - THE EPOCH WINDOW on ExEx output delivery. [handle_sync_output] no-ops when
      [consensus_output.sub_dag().leader_epoch() > self.inner.committee.epoch()]
      (subscriber.rs:143-147), and the state-sync forward drain returns the
      withheld header before its single [sync_output().send(output)] under the
      identical predicate (state-sync/src/lib.rs:324-327 then :380), whose
      caller re-tests it and terminates the epoch-scoped streaming task
      (state-sync/src/lib.rs:231-233). Three textual copies of ONE rule, modeled
      as the single [ep = Ep_e1] conjunct of the [t_out] guard.

    - THE COMMITTEE GATE on ExEx certificate delivery. [process_gossip] wraps
      cert verification, the state-sync hand-off, the inactive-CVV storage write
      and [notify_exex_certificate] in [if let Some(committee) =
      self.get_committee(epoch).await] (handler.rs:251-279); the else arm only
      warns and drops (handler.rs:280-286) and nothing behind it ever re-opens
      that certificate. [get_committee] has THREE sources (handler.rs:215-223):
      the current committee, the next epoch's [next_committee_keys], and -
      the branch an earlier revision of this model wrongly hardwired away -
      [self.consensus_chain.epochs().get_committee_keys(epoch)] (handler.rs:221),
      which falls back to [record_by_epoch(epoch - 1).next_committee]
      (storage/src/epoch_records.rs:354-367). The epoch-(E+1) RECORD alone
      therefore answers for epoch E+2 while [committee.epoch()] still reads E,
      and the node-scoped [spawn_epoch_record_collector] (node.rs:888-895) is
      exactly what supplies it: [collect_epoch_records] back-fills from epoch 0
      and deliberately runs past the node's own latest epoch
      (state-sync/src/epoch.rs:46-150, whose [Err] arm says "We delibrately go
      past the latest epoch"). So an epoch-(E+2) certificate at a host
      configured at epoch E is unevaluable only WHILE that record is missing;
      once it lands the certificate verifies or is rejected with no epoch
      advance at all. [Certificate::validate_received] is no substitute - it
      merely re-arms [SignatureVerificationState::Unverified] and checks nothing
      (types/src/primary/certificate.rs:294-301).

    - THE SPAWN POLICY of the ExEx task. With the shipped default
      [exex_critical = false] (config/src/node.rs) the node takes the
      [spawner.spawn_task(label, run_isolated_exex_future(..))] branch
      (node.rs:953-957, and the manager's copy at node.rs:982-989);
      [run_isolated_exex_future] [catch_unwind]s and ALWAYS resolves [Ok(())]
      (manager/exex.rs:15-36), while the task manager independently [continue]s
      over every non-critical outcome, [Ok] or join error
      (task_manager.rs:456-479). The opt-in branch instead spawns
      [run_critical_exex_future] (node.rs:945-952, manager/exex.rs:49-63), whose
      failure - or even clean finish, via [TaskJoinError::CriticalExitOk] -
      unwinds [until_exit] and cancels the whole node (node.rs:1082-1099).

    MODELLING SCOPE - the PUSH surface only. Every atom below is about a
    [TnExExNotification] actually handed to an installed ExEx by one of the two
    [notify_exex_*] producers. Nothing here is a claim about what an ExEx could
    read for ITSELF: [TnExExContext::consensus_chain] hands out a read-only
    [ConsensusChain] (context.rs:36-38, :98-104), and that DB is written by
    routes that consult no ExEx gate whatsoever - the closed-epoch pack fetchers
    write into the very handle the context clones (node.rs:1033-1056,
    state-sync/src/consensus.rs:100-135 [request_epochs], :288-306
    [request_epoch_pack] then [consensus_header_by_number]), and state-sync's own
    forward drain SOURCES outputs out of it
    ([consensus_chain.consensus_output_by_number], state-sync/src/lib.rs:305-310)
    BEFORE it applies the epoch window at :324-327. A withheld output can
    therefore be sitting in the consensus DB already: what the epoch window
    bounds is the notification stream, not the database.

    COMPONENTS (five, all monotone, so the reachable graph is a finite DAG whose
    terminals the kernel stutter-closes):
    - [ep] : V1's [ConsensusConfig] committee epoch, advanced only by reading the
      committee and [epoch_start] back out of the executed canonical tip
      ([configure_consensus], start_epoch.rs:238-266);
    - [net] : the highest epoch in which a quorum EXCLUDING V1 committed a
      sub-DAG. With four validators and f = 1, V0/V2/V3 are 3 = 2f+1, so the
      network advances without V1 - this is the hidden global component;
    - [out] : the highest sub-DAG leader epoch of a [ConsensusOutput] handed to
      the ExEx ([notify_exex_consensus_output], subscriber.rs:175);
    - [cert] : the fate of ONE gossiped epoch-(E+2) certificate, carrying BOTH
      its hidden nature (genuine = 2f+1 real epoch-(E+2) members signed it) and
      the trace V1 observes locally;
    - [exex] : the outcome of V1's ExEx future.

    ROLE MAPPING (knowledge agents must have a real, non-constant view; a
    blank-view party may never appear under K):
    - V1 is the ExEx HOST and a knowledge agent. Its view is
      ([ep], [out], [cert_trace cert], [exex]): its own committee epoch, how far
      its own ExEx output stream has been delivered, the OBSERVABLE trace of the
      gossiped certificate, and its own task's outcome (manager/exex.rs:20-33
      logs finish / error / panic locally). It does NOT see [net], and it does
      NOT see the genuine/forged discriminator while [get_committee] returned
      [None]: both natures produce the byte-identical
      [warn!("failed to get committee for epoch {epoch}, ignoring certificate!")]
      with no storage write and no ExEx signal (handler.rs:259 and :261-268 both
      sit INSIDE the [Some] arm).
    - V2 is a COMMITTEE PEER and a knowledge agent. Its view is
      ([net], responding/silent): the network epoch it itself helps commit, plus
      whether V1 still answers on the wire. It sees NOTHING of V1's ExEx state:
      [TnExExContext] holds no network handle and keeps its fields private
      precisely so third-party code cannot back-pressure the manager
      (context.rs:12-39), and the [TnExExManagerHandle] carrying
      [TnExExEvent::FinishedHeight] is intentionally dropped unread
      (node.rs:964-974).
    - V0 and V3 are idle: constant blank view, never under K. *)

(** V1's locally configured [ConsensusConfig] committee epoch
    (start_epoch.rs:238-266). Monotone: an epoch is entered by executing the
    epoch-closing block, never left backwards. *)
type ep =
  | Ep_e  (** the host is still configured at epoch E *)
  | Ep_e1  (** the host has entered epoch E+1 *)

(** Total order index for {!ep}. *)
let ep_index = function Ep_e -> 0 | Ep_e1 -> 1

(** Total order on {!ep}. *)
let ep_compare a b = Int.compare (ep_index a) (ep_index b)

(** [true] iff the host has entered epoch E+1. *)
let ep_is_e1 = function Ep_e -> false | Ep_e1 -> true

(** The highest epoch in which a quorum EXCLUDING V1 (V0/V2/V3 = 3 = 2f+1 with
    f = 1) committed a sub-DAG. This is the hidden global component: it is
    deliberately absent from V1's view. *)
type net =
  | Net_e  (** the network has committed nothing past epoch E *)
  | Net_e1  (** a quorum outside V1 committed in epoch E+1 *)
  | Net_e2  (** a quorum outside V1 committed in epoch E+2 *)

(** Total order index for {!net}. *)
let net_index = function Net_e -> 0 | Net_e1 -> 1 | Net_e2 -> 2

(** Total order on {!net}. *)
let net_compare a b = Int.compare (net_index a) (net_index b)

(** [true] iff a quorum outside V1 has committed in epoch E+1 or later. *)
let net_at_least_e1 = function
  | Net_e -> false
  | Net_e1 -> true
  | Net_e2 -> true

(** [true] iff a quorum outside V1 has committed in epoch E+2. *)
let net_is_e2 = function Net_e -> false | Net_e1 -> false | Net_e2 -> true

(** The highest sub-DAG leader epoch of a [ConsensusOutput] handed to the ExEx
    by [notify_exex_consensus_output] (subscriber.rs:175). *)
type out =
  | Out_e  (** no epoch-(E+1) output has reached the ExEx *)
  | Out_e1  (** an epoch-(E+1) [ConsensusOutput] reached the ExEx *)

(** Total order index for {!out}. *)
let out_index = function Out_e -> 0 | Out_e1 -> 1

(** Total order on {!out}. *)
let out_compare a b = Int.compare (out_index a) (out_index b)

(** [true] iff an epoch-(E+1) [ConsensusOutput] has been delivered to the ExEx. *)
let out_is_e1 = function Out_e -> false | Out_e1 -> true

(** The fate of ONE gossiped epoch-(E+2) certificate at V1, carrying both its
    hidden nature and the trace V1 observes. A GENUINE certificate presupposes
    [net = Net_e2] - the real epoch-(E+2) committee must actually have signed
    something - which is exactly why the nature is correlated with the hidden
    component and cannot be read off V1's view. *)
type cert =
  | Cert_none  (** no epoch-(E+2) certificate has reached V1 yet *)
  | Cert_unknown_genuine
      (** 2f+1 real epoch-(E+2) members signed it, but all THREE sources of
          [get_committee(E+2)] were empty at [committee.epoch() = E] - in
          particular the epoch-(E+1) record had not been collected yet, so
          [get_committee_keys] found neither [record_by_epoch(E+2)] nor
          [record_by_epoch(E+1).next_committee]
          (storage/src/epoch_records.rs:354-367) - so it was warn-dropped
          (handler.rs:280-286) *)
  | Cert_unknown_forged
      (** a lone Byzantine node fabricated it; [get_committee(E+2)] returned
          [None] and it was warn-dropped by the SAME code path, producing the
          byte-identical local trace *)
  | Cert_verified_genuine
      (** [get_committee] answered (current epoch, [next_committee_keys], or -
          with NO epoch advance - the epoch-record fallback of handler.rs:221),
          [verify_cert] succeeded and [notify_exex_certificate] fired
          (handler.rs:274-276) *)
  | Cert_invalid_forged
      (** [get_committee] answered - again possibly from the epoch record alone -
          and [verify_cert] failed: the [Err] arm only warns (handler.rs:278),
          so no ExEx signal is emitted *)
  | Cert_leaked_genuine
      (** reachable ONLY under {!No_committee_gate}: a genuine but unevaluable
          certificate forwarded to the ExEx with no committee to check it *)
  | Cert_leaked_forged
      (** reachable ONLY under {!No_committee_gate}: a fabricated, unevaluable
          certificate forwarded to the ExEx *)

(** Total order index for {!cert}. *)
let cert_index = function
  | Cert_none -> 0
  | Cert_unknown_genuine -> 1
  | Cert_unknown_forged -> 2
  | Cert_verified_genuine -> 3
  | Cert_invalid_forged -> 4
  | Cert_leaked_genuine -> 5
  | Cert_leaked_forged -> 6

(** Total order on {!cert}. *)
let cert_compare a b = Int.compare (cert_index a) (cert_index b)

(** [true] iff an epoch-(E+2) certificate reached V1 while [get_committee]
    returned [None] and has not since been re-evaluated (handler.rs:251, the
    else arm at :280-286). *)
let cert_is_unverifiable = function
  | Cert_unknown_genuine -> true
  | Cert_unknown_forged -> true
  | Cert_leaked_genuine -> true
  | Cert_leaked_forged -> true
  | Cert_none -> false
  | Cert_verified_genuine -> false
  | Cert_invalid_forged -> false

(** [true] iff [TnExExNotification::CertificateAccepted] was emitted for this
    certificate ([notify_exex_certificate], consensus_bus.rs:593-600). *)
let cert_signals_exex = function
  | Cert_verified_genuine -> true
  | Cert_leaked_genuine -> true
  | Cert_leaked_forged -> true
  | Cert_none -> false
  | Cert_unknown_genuine -> false
  | Cert_unknown_forged -> false
  | Cert_invalid_forged -> false

(** [true] iff 2f+1 distinct members of the REAL epoch-(E+2) committee signed
    this certificate's header. This is the hidden Byzantine discriminator. *)
let cert_is_quorum_genuine = function
  | Cert_unknown_genuine -> true
  | Cert_verified_genuine -> true
  | Cert_leaked_genuine -> true
  | Cert_none -> false
  | Cert_unknown_forged -> false
  | Cert_invalid_forged -> false
  | Cert_leaked_forged -> false

(** The outcome of V1's ExEx future (manager/exex.rs:15-63). *)
type exex =
  | Exex_live  (** the ExEx future is still running *)
  | Exex_dead_isolated
      (** it finished, errored or panicked and was contained by
          [run_isolated_exex_future]; the task manager [continue]s over the
          non-critical result (task_manager.rs:459-461, :470-472) *)
  | Exex_dead_fatal
      (** reachable ONLY under {!Spawn_exex_critical}: the same event went
          through [run_critical_exex_future] and unwound the node
          (task_manager.rs:456-479, node.rs:1082-1099) *)

(** Total order index for {!exex}. *)
let exex_index = function
  | Exex_live -> 0
  | Exex_dead_isolated -> 1
  | Exex_dead_fatal -> 2

(** Total order on {!exex}. *)
let exex_compare a b = Int.compare (exex_index a) (exex_index b)

(** [true] iff V1's ExEx future has resolved - finished, errored or panicked. *)
let exex_is_stopped = function
  | Exex_live -> false
  | Exex_dead_isolated -> true
  | Exex_dead_fatal -> true

(** [true] iff V1's node itself shut down because a critical task exited. *)
let exex_is_fatal = function
  | Exex_live -> false
  | Exex_dead_isolated -> false
  | Exex_dead_fatal -> true

(** The joint global state of the modeled host plus the network around it. *)
type state = { ep : ep; net : net; out : out; cert : cert; exex : exex }

(** Total deterministic comparison over ALL state fields, in the order
    [ep], [net], [out], [cert], [exex]. *)
let state_compare s1 s2 =
  let c = ep_compare s1.ep s2.ep in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = net_compare s1.net s2.net in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = out_compare s1.out s2.out in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = cert_compare s1.cert s2.cert in
        if Bool.not (Int.equal c3 0) then c3 else exex_compare s1.exex s2.exex

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** [true] iff V1's node is still running. Only the critical-spawn outcome takes
    it down; an isolated ExEx death leaves the host up by construction
    (manager/exex.rs:15-36 always resolves [Ok(())], task_manager.rs:459-461). *)
let node_up s = Bool.not (exex_is_fatal s.exex)

(** The LOCALLY OBSERVABLE trace of the gossiped certificate - what V1 can
    actually distinguish. The collapse of the two [Tr_dropped] preimages (and of
    the two [Tr_leaked] preimages) is the entire epistemic content of S2 and
    half of S1: both natures take the same [else] arm and emit the same warn,
    with no storage write and no ExEx notification (handler.rs:280-286). *)
type trace =
  | Tr_none  (** nothing arrived *)
  | Tr_dropped  (** the warn-and-drop trace of an unevaluable certificate *)
  | Tr_leaked
      (** the trace produced only under {!No_committee_gate}: forwarded to the
          ExEx without any committee to verify against *)
  | Tr_verified  (** verified against a committee and signalled to the ExEx *)
  | Tr_invalid  (** checked against a committee and rejected *)

(** Total order index for {!trace}. *)
let trace_index = function
  | Tr_none -> 0
  | Tr_dropped -> 1
  | Tr_leaked -> 2
  | Tr_verified -> 3
  | Tr_invalid -> 4

(** Total order on {!trace}. *)
let trace_compare a b = Int.compare (trace_index a) (trace_index b)

(** Project a certificate's fate onto the trace V1 can observe, collapsing the
    hidden genuine/forged discriminator wherever [get_committee] answered
    [None]. *)
let cert_trace = function
  | Cert_none -> Tr_none
  | Cert_unknown_genuine -> Tr_dropped
  | Cert_unknown_forged -> Tr_dropped
  | Cert_leaked_genuine -> Tr_leaked
  | Cert_leaked_forged -> Tr_leaked
  | Cert_verified_genuine -> Tr_verified
  | Cert_invalid_forged -> Tr_invalid

(** What a committee peer can tell about V1 on the wire. *)
type liveness =
  | Responding  (** V1's node is up and answering *)
  | Silent  (** V1's node went down *)

(** Total order index for {!liveness}. *)
let liveness_index = function Responding -> 0 | Silent -> 1

(** Total order on {!liveness}. *)
let liveness_compare a b = Int.compare (liveness_index a) (liveness_index b)

(** V1's wire-observable liveness. Note this is the ONLY channel by which V1's
    ExEx trouble could ever reach a peer, and pristine it never moves. *)
let node_liveness s = if node_up s then Responding else Silent

(** A validator's local view. [View_v1] is the ExEx host's projection -
    ([ep], [out], [cert_trace cert], [exex]) - which holds NO component of [net]
    and no genuine/forged discriminator. [View_v2] is a committee peer's
    projection - ([net], liveness) - which holds no component of V1's ExEx,
    epoch, output or certificate state. [View_idle] is the constant blank view
    of the non-agents V0 and V3. *)
type view =
  | View_v1 of ep * out * trace * exex
  | View_v2 of net * liveness
  | View_idle

(** Total deterministic order over ALL fields of V1's view. *)
let view_v1_compare (ea, oa, ta, xa) (eb, ob, tb, xb) =
  let c = ep_compare ea eb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = out_compare oa ob in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = trace_compare ta tb in
      if Bool.not (Int.equal c2 0) then c2 else exex_compare xa xb

(** Total deterministic order over ALL fields of V2's view. *)
let view_v2_compare (na, la) (nb, lb) =
  let c = net_compare na nb in
  if Bool.not (Int.equal c 0) then c else liveness_compare la lb

(** Total order on views: [View_idle] < [View_v1] < [View_v2], field-wise within
    each constructor. All nine cross-constructor arms are spelled: no wildcard
    on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_v1 _ | View_v2 _) -> -1
  | (View_v1 _ | View_v2 _), View_idle -> 1
  | View_v1 (ea, oa, ta, xa), View_v1 (eb, ob, tb, xb) ->
      view_v1_compare (ea, oa, ta, xa) (eb, ob, tb, xb)
  | View_v1 _, View_v2 _ -> -1
  | View_v2 _, View_v1 _ -> 1
  | View_v2 (na, la), View_v2 (nb, lb) -> view_v2_compare (na, la) (nb, lb)

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 (the ExEx host) and V2 (a committee peer) are the
    knowledge agents with real, non-constant views; V0 and V3 are idle
    non-agents with the constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V1 -> View_v1 (s.ep, s.out, cert_trace s.cert, s.exex)
  | Validator.V2 -> View_v2 (s.net, node_liveness s)
  | Validator.V0 | Validator.V3 -> View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_epoch_window
      (** delete the epoch window on ExEx output delivery - ALL THREE textual
          copies of the same predicate: subscriber.rs:143-147
          ([if consensus_output.sub_dag().leader_epoch() >
          self.inner.committee.epoch() { return Ok(()) }]),
          state-sync/src/lib.rs:324-327 ([if consensus_header.sub_dag
          .leader_epoch() > epoch { return Ok(consensus_header) }], immediately
          before the sole [consensus_bus.sync_output().send(output)] at :380),
          and state-sync/src/lib.rs:231-233 (the caller re-tests the returned
          header and terminates the epoch-scoped streaming task). Modeled as
          dropping the [ep = Ep_e1] conjunct of the [t_out] guard, which ADDS
          (Ep_e, Net_e1, Out_e, _, _) -> (Ep_e, Net_e1, Out_e1, _, _) and
          (Ep_e, Net_e2, Out_e, _, _) -> (Ep_e, Net_e2, Out_e1, _, _) and removes
          nothing: the ExEx is handed an epoch-(E+1) output while its host is
          still configured at epoch E.

          SIBLING HUNT. state-sync/src/lib.rs:324-327 is a REAL sibling that
          enforces the identical rule one stage earlier, so deleting only
          subscriber.rs:143 would be silently repaired - which is why this
          mutation deletes all three sites at once. Four further routes are
          ruled out: (1) [notify_exex_consensus_output] has exactly ONE call
          site in the tree (subscriber.rs:175); the active-CVV path
          [handle_consensus_output] never notifies an ExEx; (2) exactly ONE
          sender exists on [sync_output] (state-sync/src/lib.rs:380), directly
          after the gate; (3) the replay seam yields only [ChainExecuted]
          ([ReplayStream], exex/src/replay.rs:41-62) and exex/src/notification.rs
          states that missed [ConsensusOutput] is NOT recoverable by replay;
          (4) the ExEx's read-only [ConsensusChain] (context.rs:36-38) is NOT a
          closed back-door - do not claim it is. The closed-epoch pack fetchers
          write into the very handle the context clones (node.rs:1033-1056,
          state-sync/src/consensus.rs:100-135 and :288-306), and the forward
          drain reads outputs back OUT of it
          (state-sync/src/lib.rs:305-310, "already in a local pack") one stage
          BEFORE testing the window at :324-327, so a withheld output may well be
          in the DB. It still repairs nothing here, because it emits no
          [TnExExNotification] at all and the modeled atom [Exex_output_e1] is
          the notification, not the database (see MODELLING SCOPE above). *)
  | No_committee_gate
      (** delete the committee requirement on ExEx certificate delivery:
          handler.rs:251, the [if let Some(committee) =
          self.get_committee(epoch).await { .. } else { warn!(..) }] Option gate
          whose else arm is handler.rs:280-286. With no committee the
          certificate cannot be verified ([verify_cert] needs a key set), so the
          mutant forwards it to the ExEx as-is. On the [ep = Ep_e] branch of
          [t_cert_arrive] this REMOVES the successors [Cert_unknown_genuine] /
          [Cert_unknown_forged] and ADDS [Cert_leaked_genuine] /
          [Cert_leaked_forged] in their place - states satisfying
          [Cert_unverifiable] and [Exex_cert_signal] simultaneously, which is
          impossible pristine.

          SIBLING HUNT. Five routes, none repairs the deletion:
          (1) [notify_exex_certificate] (consensus_bus.rs:593-600) is the SOLE
          producer of [CertificateAccepted] and has exactly ONE call site
          (handler.rs:275); (2) [Certificate::validate_received]
          (types/src/primary/certificate.rs:294-301) is not a verifier - it only
          re-arms [SignatureVerificationState::Unverified] - so it cannot
          re-establish genuineness on either side of the gate;
          (3) [state_sync.process_peer_certificate] (handler.rs:259) sits INSIDE
          the [Some] arm and is additionally gated on [is_cvv()]; (4) the
          inactive-CVV storage write [node_storage().write(cert.clone())]
          (handler.rs:261-268) is also inside the [Some] arm and is additionally
          gated on the certificate's epoch equalling the host's, so THIS handler
          never persists an unevaluable certificate, and the replay seam is no
          repair either (replay.rs:41-62 yields only [ChainExecuted]). What is
          NOT claimed - an earlier revision of this comment claimed it and it is
          false - is that the consensus DB is unreachable to an ExEx: it is
          reachable (context.rs:36-38) and other routes do write it (MODELLING
          SCOPE above). The surviving point is narrower: no such route emits
          [CertificateAccepted];
          (5) [EpochRecordDb::get_committee_keys]
          (storage/src/epoch_records.rs:354-367), [get_committee]'s third source,
          only changes WHICH certificates are unevaluable - when it answers, the
          [Some] arm runs and this mutation is irrelevant to them. It needs NO
          epoch advance, and is now modeled as such: the epoch-record branch of
          [t_cert_arrive] and the [epoch_record_committee_available] disjunct of
          [t_cert_regossip]'s guard. The mutation is therefore evaluated against
          a model that already contains that resolution path. *)
  | Spawn_exex_critical
      (** delete the shipped [exex_critical = false] default (config/src/node.rs)
          by always taking the [spawn_critical_task] arm: node.rs:945-952 instead
          of the non-critical [spawner.spawn_task(label,
          run_isolated_exex_future(..))] at node.rs:953-957, together with the
          manager's copy of the same branch at node.rs:976-989. [t_exex_stop]'s
          successor becomes [Exex_dead_fatal] instead of [Exex_dead_isolated],
          which REMOVES every V1-local transition ([t_ep], [t_out],
          [t_cert_arrive], [t_cert_regossip]) from every post-failure state while
          leaving [t_net] enabled - the other validators keep committing.

          SIBLING HUNT. Six routes, two of which show why the OBVIOUS gates are
          the wrong ones: (1) deleting only the [catch_unwind] in
          [run_isolated_exex_future] (manager/exex.rs:19) is SILENTLY REPAIRED,
          because the task manager ignores every non-critical outcome including
          a join error ([if !info.critical { continue }],
          task_manager.rs:470-472); (2) deleting only the [Err] arm of
          [run_critical_exex_future] (manager/exex.rs:58-61) is also silently
          repaired, since a critical task resolving [Ok(())] still yields
          [TaskJoinError::CriticalExitOk] (task_manager.rs:457-466); (3) the
          manager follows the SAME branch (node.rs:976-990), so a mutation
          touching only the per-ExEx tasks would leave the manager isolated -
          flipping the branch flips both, which is why the branch is the gate;
          (4) there is no restart supervisor: [node_task_manager.until_exit]
          returning [Err] makes the whole node run return [Err] and cancels
          [run_epochs] (node.rs:1082-1099); (5) backpressure as an alternate way
          for a sick ExEx to stall its host is ruled out - [ExExHandle::send] is
          [try_send]-only with a drop-and-lagged marker (exex/src/manager.rs) and
          [notify_exex] is a non-blocking broadcast guarded by
          [receiver_count() > 0] (consensus_bus.rs:587-591); (6) the reverse
          channel leaks nothing to peers - [TnExExEvent::FinishedHeight] goes
          into a watch whose [TnExExManagerHandle] is intentionally dropped
          unread (node.rs:964-974) and the context holds no network handle
          (context.rs:26-39). *)

(** The other validators' consensus progress. Enabled even when V1's node is
    down: V0/V2/V3 are 3 = 2f+1 with f = 1, so the network commits without V1.
    Keeping this enabled at [Exex_dead_fatal] is load-bearing - it stops the
    mutant's fatal states from being instantly terminal, so the refutation of
    S3's [Af] is attributable to the FROZEN HOST, not to a dead model. *)
let t_net s =
  match s.net with
  | Net_e -> [ { s with net = Net_e1 } ]
  | Net_e1 -> [ { s with net = Net_e2 } ]
  | Net_e2 -> []

(** V1 crosses the epoch boundary by executing the epoch-closing block and
    reading the new committee plus [epoch_start] back out of the executed
    canonical tip ([configure_consensus], start_epoch.rs:238-266). Requires the
    node to be up and the network to have produced epoch-(E+1) consensus. *)
let t_ep s =
  if node_up s && Bool.not (ep_is_e1 s.ep) && net_at_least_e1 s.net then
    [ { s with ep = Ep_e1 } ]
  else []

(** The epoch window on ExEx output delivery: the single modeled stand-in for
    the three textual copies of [leader_epoch() > epoch -> bail]
    (subscriber.rs:143-147, state-sync/src/lib.rs:324-327 and :231-233).
    {!No_epoch_window} deletes all three. *)
let out_window_open mut s =
  match mut with
  | Pristine -> ep_is_e1 s.ep
  | No_committee_gate -> ep_is_e1 s.ep
  | Spawn_exex_critical -> ep_is_e1 s.ep
  | No_epoch_window -> true

(** Hand an epoch-(E+1) [ConsensusOutput] to the ExEx
    ([notify_exex_consensus_output], subscriber.rs:175). Needs the node up, the
    network to have committed in epoch E+1 at all, and the epoch window open. *)
let t_out mut s =
  if
    node_up s
    && Bool.not (out_is_e1 s.out)
    && net_at_least_e1 s.net
    && out_window_open mut s
  then [ { s with out = Out_e1 } ]
  else []

(** The genuine / forged pair of certificate fates produced when
    [get_committee(E+2)] returns [None] at [committee.epoch() = E]. Pristine both
    take the warn-and-drop else arm (handler.rs:280-286); under
    {!No_committee_gate} both are forwarded to the ExEx unverified. *)
let unevaluable_fates mut =
  match mut with
  | Pristine -> (Cert_unknown_genuine, Cert_unknown_forged)
  | No_epoch_window -> (Cert_unknown_genuine, Cert_unknown_forged)
  | Spawn_exex_critical -> (Cert_unknown_genuine, Cert_unknown_forged)
  | No_committee_gate -> (Cert_leaked_genuine, Cert_leaked_forged)

(** [true] iff V1 can answer [get_committee(E+2)] WITHOUT advancing its own
    epoch, because the epoch-(E+1) record is already in its store.
    [get_committee]'s third branch is
    [self.consensus_chain.epochs().get_committee_keys(epoch)]
    (handler.rs:215-223), which falls back to
    [record_by_epoch(epoch - 1).next_committee]
    (storage/src/epoch_records.rs:354-367); the node-scoped
    [spawn_epoch_record_collector] (node.rs:888-895) back-fills records from
    epoch 0 and deliberately runs past the node's own latest epoch
    (state-sync/src/epoch.rs:46-150), verifying each against the previous
    record's [next_committee] and its certificate - while [ConsensusConfig]'s
    epoch advances only by executing the epoch-closing block
    (start_epoch.rs:238-266). The enabling condition here is [net >= Net_e1],
    not [net = Net_e2]: the epoch-(E+1) record exists exactly once epoch E+1 has
    CLOSED, and that closing sub-DAG is itself an epoch-(E+1) commit by the
    quorum outside V1. Tying it to [Net_e2] instead would make every EVALUATED
    trace - including the rejection of a forgery - leak [net_reached(E+2)] to
    V1, which the real code does not do. *)
let epoch_record_committee_available s = net_at_least_e1 s.net

(** One gossiped epoch-(E+2) certificate arrives at V1 ([process_gossip],
    handler.rs:230-287). At [ep = Ep_e1] the epoch is current+1 and
    [next_committee_keys] answers (handler.rs:218-219), so the certificate is
    verified or rejected. At [ep = Ep_e] the epoch is current+2 and the answer
    depends on the THIRD source: while the epoch-(E+1) record is missing
    [get_committee] returns [None] and the certificate is unevaluable, but once
    [epoch_record_committee_available] holds the same certificate is verified or
    rejected with no epoch advance at all - both branches are offered, because
    nothing orders the record collection against the gossip. A GENUINE
    certificate is only possible when [net = Net_e2]: the real epoch-(E+2)
    committee must actually have signed something, and a lone forger cannot
    manufacture that signature set ([verify_cert] fails, handler.rs:278). *)
let t_cert_arrive mut s =
  if Bool.not (node_up s) then []
  else
    match s.cert with
    | Cert_none -> (
        match s.ep with
        | Ep_e ->
            let genuine, forged = unevaluable_fates mut in
            List.concat
              [
                [ { s with cert = forged } ];
                (if net_is_e2 s.net then [ { s with cert = genuine } ] else []);
                (if epoch_record_committee_available s then
                   { s with cert = Cert_invalid_forged }
                   :: (if net_is_e2 s.net then
                         [ { s with cert = Cert_verified_genuine } ]
                       else [])
                 else []);
              ]
        | Ep_e1 ->
            { s with cert = Cert_invalid_forged }
            :: (if net_is_e2 s.net then [ { s with cert = Cert_verified_genuine } ]
                else []))
    | Cert_unknown_genuine -> []
    | Cert_unknown_forged -> []
    | Cert_verified_genuine -> []
    | Cert_invalid_forged -> []
    | Cert_leaked_genuine -> []
    | Cert_leaked_forged -> []

(** A certificate that was warn-dropped as unevaluable resolves on a LATER
    gossip of the same header, once [get_committee(E+2)] can answer: either
    because the host has entered epoch E+1 and [next_committee_keys] answers
    (handler.rs:218-219), or - with no epoch advance whatsoever - because the
    epoch-(E+1) record has since been collected
    ([epoch_record_committee_available], handler.rs:221,
    storage/src/epoch_records.rs:354-367). Both disjuncts are modeled, since the
    record branch is precisely what the earlier revision of this family wrongly
    dismissed as "the same path as an epoch advance". This is the modeled
    resolution path, and it is why S2 asserts no inevitability: nothing
    guarantees the re-gossip happens. *)
let t_cert_regossip s =
  if
    Bool.not
      (node_up s && (ep_is_e1 s.ep || epoch_record_committee_available s))
  then []
  else
    match s.cert with
    | Cert_unknown_genuine -> [ { s with cert = Cert_verified_genuine } ]
    | Cert_leaked_genuine -> [ { s with cert = Cert_verified_genuine } ]
    | Cert_unknown_forged -> [ { s with cert = Cert_invalid_forged } ]
    | Cert_leaked_forged -> [ { s with cert = Cert_invalid_forged } ]
    | Cert_none -> []
    | Cert_verified_genuine -> []
    | Cert_invalid_forged -> []

(** V1's ExEx future resolves - finished, errored or panicked
    (manager/exex.rs:19-34 logs all three identically). Pristine that is
    contained; under {!Spawn_exex_critical} the very same event takes the node
    down. *)
let t_exex_stop mut s =
  match s.exex with
  | Exex_live -> (
      match mut with
      | Pristine -> [ { s with exex = Exex_dead_isolated } ]
      | No_epoch_window -> [ { s with exex = Exex_dead_isolated } ]
      | No_committee_gate -> [ { s with exex = Exex_dead_isolated } ]
      | Spawn_exex_critical -> [ { s with exex = Exex_dead_fatal } ])
  | Exex_dead_isolated -> []
  | Exex_dead_fatal -> []

(** The transition relation under a mutation. Every transition strictly
    increases the rank [ep + net + out + cert-stage + exex-stage], so the
    reachable graph is a finite DAG whose terminals the kernel stutter-closes. *)
let next_with mut s =
  List.concat
    [
      t_net s;
      t_ep s;
      t_out mut s;
      t_cert_arrive mut s;
      t_cert_regossip s;
      t_exex_stop mut s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: the host is configured at epoch E, the network has
    committed nothing past E, the ExEx has been handed nothing, no certificate
    has arrived, and the ExEx future is running. *)
let initial =
  { ep = Ep_e; net = Net_e; out = Out_e; cert = Cert_none; exex = Exex_live }

(** The atom vocabulary this family's statements quantify over. Constructor
    names are deliberately distinct from the state-component constructors above
    (the library uses [include_subdirs unqualified], so the module is flat). *)
type atom =
  | Host_epoch_e1
      (** [ep = Ep_e1] : V1's [ConsensusConfig] committee epoch is E+1
          (start_epoch.rs:238-266) *)
  | Net_reached_e1
      (** [net >= Net_e1] : a quorum excluding V1 committed a sub-DAG in epoch
          E+1 *)
  | Net_reached_e2
      (** [net = Net_e2] : a quorum excluding V1 committed a sub-DAG in epoch
          E+2 *)
  | Exex_output_e1
      (** [out = Out_e1] : the ExEx was handed a
          [TnExExNotification::ConsensusOutput] whose sub-DAG leader epoch is
          E+1 (subscriber.rs:175) *)
  | Cert_unverifiable
      (** an epoch-(E+2) gossip certificate reached V1 while
          [get_committee(E+2)] returned [None] and has not since been
          re-evaluated (handler.rs:251, :280-286) *)
  | Exex_cert_signal
      (** [TnExExNotification::CertificateAccepted] was emitted for that
          certificate (consensus_bus.rs:593-600) *)
  | Cert_quorum_genuine
      (** 2f+1 distinct members of the REAL epoch-(E+2) committee signed the
          certificate's header - the hidden Byzantine discriminator *)
  | Exex_task_stopped
      (** V1's ExEx future resolved: finished, errored or panicked
          (manager/exex.rs:19-34) *)
  | Host_halted
      (** V1's node shut down because a critical task exited
          (task_manager.rs:456-479, node.rs:1082-1099); unreachable pristine *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Host_epoch_e1 -> ep_is_e1 s.ep
  | Net_reached_e1 -> net_at_least_e1 s.net
  | Net_reached_e2 -> net_is_e2 s.net
  | Exex_output_e1 -> out_is_e1 s.out
  | Cert_unverifiable -> cert_is_unverifiable s.cert
  | Exex_cert_signal -> cert_signals_exex s.cert
  | Cert_quorum_genuine -> cert_is_quorum_genuine s.cert
  | Exex_task_stopped -> exex_is_stopped s.exex
  | Host_halted -> exex_is_fatal s.exex

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Host_epoch_e1 -> "host_epoch=E+1"
  | Net_reached_e1 -> "net_reached(E+1)"
  | Net_reached_e2 -> "net_reached(E+2)"
  | Exex_output_e1 -> "exex_output(E+1)"
  | Cert_unverifiable -> "cert_unverifiable"
  | Exex_cert_signal -> "exex_cert_signal"
  | Cert_quorum_genuine -> "cert_quorum_genuine"
  | Exex_task_stopped -> "exex_task_stopped"
  | Host_halted -> "host_halted"

(** The exact CTLK checker over this family's ordered state and view. *)
module Checker = System.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, the two-agent view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
