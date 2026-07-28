(** Finite interpreted system for the OUTPUT_FORWARD_GATE family: the seam
    between consensus and execution, i.e. the epoch manager's live-forwarding
    loop and the engine's bounded FIFO backlog. It answers "in what order, and
    how many times, does a committed consensus output reach the EVM". File
    citations refer to Telcoin-Association/telcoin-network (this checkout, git
    HEAD [0c59c15b], working tree).

    The modeled mechanism, one epoch of a single node, over the two consensus
    output numbers 1 and 2:

    - COMMIT: the subscriber saves each output to the consensus chain and then
      broadcasts it ([save_consensus .. ; consensus_output().send(output)],
      subscriber.rs:286-323). The channel is a tokio broadcast of depth 100
      (consensus_bus.rs:317) whose sender never blocks and never reports a lost
      message ([let _ = self.send(value); Ok(())], sync.rs:172-188).

    - DELIVER: the forwarder's receiver is the [TnReceiver] impl at
      sync.rs:200-222. On overflow it does NOT surface the loss to its caller -
      [Err(Lagged(n)) => { warn!(..); continue; }] logs and resumes at the
      oldest message still buffered, so a lagged forwarder simply observes a
      later number and nothing else (sync.rs:205-217). Three delivery routes are
      modeled: the in-order live message; a RE-BROADCAST of an
      already-forwarded output (the previous epoch's shutdown drain re-emits
      saved outputs best-effort at subscriber.rs:394-403, and the state-sync
      path re-broadcasts every reconstructed output at subscriber.rs:154-180);
      and the lagged jump.

    - CLASSIFY (the gate under audit): run_epoch.rs:574
      [match check_output_continuity(self.last_forwarded_consensus_number,
      output.number())] with three arms - [Stale] warns and [continue]s
      (:575-583), [Gap] returns [Err(..)] (:584-591), [Next] falls through
      (:592). The classifier is [if number <= last_forwarded { Stale } else if
      number == last_forwarded + 1 { Next } else { Gap }]
      (run_epoch.rs:883-891). The watermark advances only after a successful
      send and is assigned unconditionally from the output's own number
      ([to_engine.send(output).await?; self.last_forwarded_consensus_number =
      last_forwarded_consensus_number], run_epoch.rs:535-551, doc :527-529), so
      forwarding a stale number moves the watermark BACKWARDS - the model does
      that too. A [Gap] error propagates through [res.inspect_err(..)?]
      (run_epoch.rs:352-354) and out of the epoch loop before [close_epoch] and
      before the leftover drain, so [Errored] is terminal for the forwarder.

    - QUEUE and EXECUTE: the engine pushes each received output onto [queued]
      ([self.queued.push_back(output)], engine/lib.rs:245-252, gated on
      [self.queued.len() < MAX_QUEUED_OUTPUTS] with the bound at engine/lib.rs:38
      and the upstream mpsc at node.rs:60-68), spawns at most one execution task
      at a time ([if self.pending_task.is_none() && !self.queued.is_empty()],
      engine/lib.rs:227-230) and takes the FRONT of the queue
      ([self.queued.pop_front()], engine/lib.rs:124). Execution increments the
      leader's reward count unconditionally, once per delivered output
      ([gas_accumulator.rewards_counter().inc_leader_count(output.leader().author())],
      payload_builder.rs:30) - even the empty-output early return still counts
      it (payload_builder.rs:84-97), which is why a second delivery of the same
      number is destructive on ANY output shape.

    Components: (1) [rebroadcast], the hidden environment branch fixed at init -
    whether a re-broadcast of output 1 is sitting UNREAD in the broadcast ring;
    (2) [src], how far the subscriber has committed and broadcast; (3) [w], the
    forwarder's watermark; (4) [pending], the one message the forwarder has
    received and not yet classified; (5) [skipped], whether it has dropped a
    stale delivery; (6) the two gate-violation flags, both unreachable on the
    pristine model; (7) [status]; (8) the engine's bounded FIFO [queue]; (9)
    [exec], the execution order (most recent first, duplicates recorded).

    The engine's spawn (engine/lib.rs:227-230) and completion arm
    (engine/lib.rs:262-268) are merged into ONE atomic dequeue-and-execute step:
    [pending_task] is a single [Option] so at most one output is ever in flight,
    and no statement here distinguishes "executing" from "executed".

    Role mapping (a knowledge agent must have a real, non-constant view; a
    blank-view party may never appear under K):
    - V1 is the epoch manager's FORWARDER (run_epoch.rs:561-619). It sees its own
      watermark, the delivery in hand, whether it has skipped a stale one, the
      epoch status, and the LAST execution update it consumed. It does NOT see
      [src] (what the subscriber has committed but not yet handed it), the
      hidden [rebroadcast] branch, or the engine's backlog.
    - V2 is the same node's execution ENGINE (engine/lib.rs:49-80). Its entire
      memory is [queued] plus [parent_header], "the [SealedHeader] of the last
      fully-executed block" (engine/lib.rs:66-69, written at :268) - it keeps NO
      set of executed consensus numbers, which is exactly why the de-duplication
      must happen upstream and why deleting the [Stale] arm is unrepairable.
      V1 and V2 are two observers inside one validator process, separated by the
      [to_engine] mpsc (node.rs:838) and the [engine_update] mpsc
      (engine/lib.rs:76-79); the knowledge that crosses that boundary is
      precisely what S3 conjunct B is about.
    - V0 and V3..V9 are idle non-agents: constant blank view, never under K.

    Modeling admissions (R5), stated so no statement here is true by omission:

    1. V1's execution observation is the LAST update it consumed, not the whole
       executed set. That mirrors what the code actually consumes:
       run_epoch.rs:232-238 waits on [wait_for_consensus_execution(last_hash)]
       for the LAST replayed output only - "Only wait for consensus that was
       actually forwarded to the engine" - and infers the rest. The underlying
       [RecentBlocks] ring would let the manager query an earlier hash too
       (consensus_bus.rs:653-667), so this projection is the code's usage rather
       than the maximum information available. Handing V1 the whole executed set
       would make S3 conjunct B a projection of V1's own view (R1) - the exact
       degeneracy this family must avoid.

    2. The statements are scoped to the LIVE-forwarding path, as the code itself
       scopes the gate: "Used only on the live-forwarding path .. the replay and
       leftover-drain paths legitimately re-forward numbers at or below
       [last_forwarded] and must not be checked" (run_epoch.rs:878-882). Those
       two siblings are modeled by their EFFECT (a re-broadcast arriving at the
       live loop), not by a second forwarding entry point, because neither
       selects a stale number: [replay_missed_consensus] replays only the
       committed-but-unexecuted gap (start_epoch.rs:59-107) and phase 2 of the
       leftover drain loads exactly [(last_sent + 1)..=latest_db]
       (close_epoch.rs:137-159). Phase 1 of that drain
       (close_epoch.rs:119-131) is genuinely unguarded - it forwards whatever
       [try_recv] yields with no continuity check - so it is an out-of-scope
       exposure of the epoch-close path, NOT a repair of the live gate, and no
       statement here claims anything about it.

    3. [queue_capacity] is 2, abstracting [MAX_QUEUED_OUTPUTS = 8]
       (engine/lib.rs:38) plus [TO_ENGINE_CAPACITY = 64] (node.rs:68) into one
       bounded FIFO. Two slots is the smallest capacity at which the FIFO
       discipline is observable at all (a one-slot queue cannot reorder).

    4. The forwarding loop is modeled WITHOUT the race it actually sits in: the
       [tokio::select!] at run_epoch.rs:344-392 runs [wait_for_epoch_boundary]
       against node shutdown and the epoch task manager exiting, either of which
       drops the loop's future - possibly with a received message still
       unjudged. Adding that third exit would roughly double the graph, so it is
       out of scope, and S2 conjunct A is stated as a WEAK until precisely so
       that it does not depend on the omission: [AF epoch_errored] would also
       prove here and would be true only because this branch is missing. The
       preempted branch cannot smuggle a gap through, either - the received
       message dies with the dropped future, and phase 2 of the leftover drain
       forwards exactly [(last_sent + 1)..=latest_db] (close_epoch.rs:137-159),
       contiguous by construction.

    Terminality of [Errored] is faithful rather than convenient: the [Gap]
    error leaves [run_epoch] at run_epoch.rs:352-354 and the epoch loop aborts
    on it ([epoch_result.inspect_err(..)?], node.rs:1225-1227), ending the
    node. *)

(** Whether the previous epoch's shutdown drain (subscriber.rs:394-403) or a
    state-sync re-broadcast (subscriber.rs:154-180) left a copy of an
    already-forwarded output in the broadcast ring for this receiver. This is
    the hidden environment branch: it is fixed at init, invisible in every
    agent's view while it is [Buffered], and it is the reason the [Stale] arm
    exists at all. *)
type rebroadcast =
  | Absent  (** no re-broadcast will ever reach this forwarder *)
  | Buffered
      (** a re-broadcast of output 1 sits UNREAD in the 100-slot broadcast ring
          (consensus_bus.rs:317); nobody downstream can see it *)
  | Handed  (** it has been handed to the forwarder by [recv] *)

(** Total order index for {!rebroadcast}. *)
let rebroadcast_index = function Absent -> 0 | Buffered -> 1 | Handed -> 2

(** Total order on {!rebroadcast}. *)
let rebroadcast_compare a b =
  Int.compare (rebroadcast_index a) (rebroadcast_index b)

(** [true] iff a re-broadcast is still unread in the ring. *)
let rebroadcast_is_buffered = function
  | Absent -> false
  | Buffered -> true
  | Handed -> false

(** [true] iff the re-broadcast has been handed to the forwarder. *)
let rebroadcast_is_handed = function
  | Absent -> false
  | Buffered -> false
  | Handed -> true

(** The epoch's forwarding status. *)
type status =
  | Running  (** [wait_for_epoch_boundary] is still consuming output *)
  | Errored
      (** the [Gap] arm returned [Err] (run_epoch.rs:584-591) and the [?] at
          run_epoch.rs:352-354 propagated it out of [run_epoch] before
          [close_epoch] and before the leftover drain: the forwarder is gone for
          good and the process restarts to replay from the DB *)

(** Total order index for {!status}. *)
let status_index = function Running -> 0 | Errored -> 1

(** Total order on {!status}. *)
let status_compare a b = Int.compare (status_index a) (status_index b)

(** [true] iff the forwarder is still running. *)
let status_is_running = function Running -> true | Errored -> false

(** [true] iff the epoch halted on the continuity gap. *)
let status_is_errored = function Running -> false | Errored -> true

(** A one-message slot: the forwarder's received-but-unclassified output, or the
    engine's last-executed number ([parent_header]). *)
type slot =
  | Empty  (** nothing received / nothing executed yet *)
  | Holds of int  (** consensus output number [n] *)

(** Total order on {!slot}: every constructor pair spelled. *)
let slot_compare a b =
  match (a, b) with
  | Empty, Empty -> 0
  | Empty, Holds _ -> -1
  | Holds _, Empty -> 1
  | Holds x, Holds y -> Int.compare x y

(** [true] iff the slot is empty. *)
let slot_is_empty = function Empty -> true | Holds _ -> false

(** Total, deterministic order on integer lists (queue and execution order). *)
let rec int_list_compare a b =
  match (a, b) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs, y :: ys ->
      let c = Int.compare x y in
      if Bool.not (Int.equal c 0) then c else int_list_compare xs ys

(** The two consensus output numbers modeled: 1 and 2. Two is the smallest
    window in which staleness (a re-delivery below the watermark), a gap (a jump
    over the watermark's successor) and overtaking (two queued outputs executing
    out of order) are all expressible. *)
let max_number = 2

(** The engine's bounded backlog, abstracting [MAX_QUEUED_OUTPUTS = 8]
    (engine/lib.rs:38) and [TO_ENGINE_CAPACITY = 64] (node.rs:68) into one
    bounded FIFO. A full queue blocks the forwarder's [to_engine.send(..).await]
    (run_epoch.rs:548), which is the modeled backpressure. *)
let queue_capacity = 2

(** The joint global state: the hidden ring branch, the subscriber's commit
    position, the forwarder's watermark and received message, the two
    gate-violation flags, the epoch status, and the engine's backlog and
    execution order. *)
type state = {
  rebroadcast : rebroadcast;  (** the hidden branch, constant after init *)
  src : int;
      (** how many outputs the subscriber has saved to the consensus chain and
          broadcast (subscriber.rs:286-323), 0 .. {!max_number} *)
  w : int;
      (** [last_forwarded_consensus_number] (node.rs:132), 0 .. {!max_number};
          assigned unconditionally from the forwarded output's own number
          (run_epoch.rs:535, :550) *)
  pending : slot;  (** the message [recv] returned and the gate has not judged *)
  skipped : bool;
      (** the [Stale] arm ran at least once: "skipping already-forwarded
          consensus output" (run_epoch.rs:576-582) *)
  stale_forwarded : bool;
      (** a number at or below the watermark was handed to the engine -
          unreachable on the pristine model *)
  gap_forwarded : bool;
      (** a number above watermark + 1 was handed to the engine - unreachable on
          the pristine model *)
  status : status;
  queue : int list;  (** the engine's [queued] VecDeque, front first *)
  exec : int list;
      (** the order in which outputs were executed, most recent first; a repeat
          records a second [inc_leader_count] (payload_builder.rs:30) *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = rebroadcast_compare s1.rebroadcast s2.rebroadcast in
  if Bool.not (Int.equal c 0) then c
  else
    let c = Int.compare s1.src s2.src in
    if Bool.not (Int.equal c 0) then c
    else
      let c = Int.compare s1.w s2.w in
      if Bool.not (Int.equal c 0) then c
      else
        let c = slot_compare s1.pending s2.pending in
        if Bool.not (Int.equal c 0) then c
        else
          let c = Bool.compare s1.skipped s2.skipped in
          if Bool.not (Int.equal c 0) then c
          else
            let c = Bool.compare s1.stale_forwarded s2.stale_forwarded in
            if Bool.not (Int.equal c 0) then c
            else
              let c = Bool.compare s1.gap_forwarded s2.gap_forwarded in
              if Bool.not (Int.equal c 0) then c
              else
                let c = status_compare s1.status s2.status in
                if Bool.not (Int.equal c 0) then c
                else
                  let c = int_list_compare s1.queue s2.queue in
                  if Bool.not (Int.equal c 0) then c
                  else int_list_compare s1.exec s2.exec

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** The engine's [parent_header] projection: the last output it executed
    (engine/lib.rs:66-69, :268), which is the whole of its memory of the past. *)
let last_exec s = match s.exec with [] -> Empty | n :: _ -> Holds n

(** A validator's local view.

    [View_forwarder (w, pending, skipped, status, last_update)] is the epoch
    manager's forwarder: its watermark, the message in hand, whether it has
    skipped a stale delivery, the epoch status, and the last execution update it
    consumed. It does NOT see [src], the hidden ring branch or the engine's
    backlog.

    [View_engine (queue, parent)] is the engine: its backlog and its
    [parent_header]. It does NOT see the watermark, the commit position, whether
    a delivery was a re-broadcast, or whether the forwarder skipped anything.

    [View_idle] is the constant blank view of the non-agents V0 and V3..V9. *)
type view =
  | View_forwarder of int * slot * bool * status * slot
  | View_engine of int list * slot
  | View_idle

(** Total order on the forwarder's five-component view. *)
let view_forwarder_compare (w1, p1, k1, st1, u1) (w2, p2, k2, st2, u2) =
  let c = Int.compare w1 w2 in
  if Bool.not (Int.equal c 0) then c
  else
    let c = slot_compare p1 p2 in
    if Bool.not (Int.equal c 0) then c
    else
      let c = Bool.compare k1 k2 in
      if Bool.not (Int.equal c 0) then c
      else
        let c = status_compare st1 st2 in
        if Bool.not (Int.equal c 0) then c else slot_compare u1 u2

(** Total order on the engine's two-component view. *)
let view_engine_compare (q1, p1) (q2, p2) =
  let c = int_list_compare q1 q2 in
  if Bool.not (Int.equal c 0) then c else slot_compare p1 p2

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_forwarder _ | View_engine _) -> -1
  | (View_forwarder _ | View_engine _), View_idle -> 1
  | View_forwarder (w1, p1, k1, s1, u1), View_forwarder (w2, p2, k2, s2, u2) ->
      view_forwarder_compare (w1, p1, k1, s1, u1) (w2, p2, k2, s2, u2)
  | View_forwarder _, View_engine _ -> -1
  | View_engine _, View_forwarder _ -> 1
  | View_engine (q1, p1), View_engine (q2, p2) ->
      view_engine_compare (q1, p1) (q2, p2)

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 is the forwarder and V2 the engine - the two observers
    the [to_engine] and [engine_update] channels separate. V0 and V3..V9 are
    idle non-agents with the constant blank view and never appear under K. *)
let view v s =
  match v with
  | Validator.V1 ->
      View_forwarder (s.w, s.pending, s.skipped, s.status, last_exec s)
  | Validator.V2 -> View_engine (s.queue, last_exec s)
  | Validator.V0 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_stale_arm
      (** delete the [OutputContinuity::Stale] arm at run_epoch.rs:575-583 so a
          delivery at or below the watermark falls through to
          [process_output]. This ADDS transitions in which an already-forwarded
          number is queued a second time, executed a second time and
          leader-counted a second time, and in which the watermark moves
          BACKWARDS (run_epoch.rs:550 assigns the output's own number
          unconditionally). No sibling path repairs it: the engine keeps no set
          of executed numbers and makes no number or hash comparison - its
          fields are exactly [queued] and [parent_header] plus plumbing
          (engine/lib.rs:49-80), its run loop only pushes and pops
          (engine/lib.rs:227-230, :245-252), and [execute_consensus_output]
          checks only that the batch and digest counts agree
          (payload_builder.rs:51-76) while incrementing the leader count
          unconditionally at payload_builder.rs:30 - the empty-output early
          return at :84-97 still counts it. [heal_finalized_to_persisted_tip]
          explicitly never moves the execution tip so "replay is unaffected"
          (tn-reth/lib.rs:872-875), and [replay_missed_consensus] is deliberately
          NOT continuity-checked (run_epoch.rs:878-882) so it cannot backstop. *)
  | No_gap_arm
      (** delete the [OutputContinuity::Gap] arm at run_epoch.rs:584-591 so a
          lagged delivery is treated as [Next]. This ADDS transitions in which
          the engine executes a number while an earlier COMMITTED number was
          never forwarded at all, and REMOVES the transition to [Errored]. No
          sibling path notices: [output.parent_hash()] is used exactly once in
          the whole engine and reth layer, as a tracing span field
          (payload_builder.rs:41), so nothing compares the output's parent
          linkage against the last executed one; the engine extends
          [parent_header] from whatever it pops (engine/lib.rs:227-230,
          :262-268). The CVV-side [wait_for_execution(base_execution_block)]
          (consensus/state.rs:421-422) runs in the consensus task and gates the
          NEXT commit, so it can only fire after the hole is already executed. *)
  | Queue_pop_back
      (** replace [self.queued.pop_front()] with [pop_back()] at
          engine/lib.rs:124 (delete the FIFO discipline). This ADDS transitions
          in which a later-numbered output executes before an earlier queued
          one. No sibling path re-orders it: [execute_consensus_output] has no
          number or parent-consensus-hash comparison (payload_builder.rs:22-76),
          the upstream mpsc (node.rs:838) is FIFO but only feeds
          [queued.push_back] (engine/lib.rs:249) and cannot constrain what the
          engine pops, and [check_output_continuity] (run_epoch.rs:574) runs
          BEFORE the send so it constrains enqueue order only and never observes
          the mutation. *)

(** Which arm of the continuity match a forward came from, so the violation
    flags are set by construction rather than by a boolean argument. *)
type arm =
  | Live  (** the [Next] arm (run_epoch.rs:592): a legitimate in-order forward *)
  | Restale  (** the deleted [Stale] arm fell through (mutation only) *)
  | Overgap  (** the deleted [Gap] arm fell through (mutation only) *)

(** The subscriber commits the next output to the consensus chain and broadcasts
    it (subscriber.rs:286-323). Stops once the forwarder has errored: the [?] at
    run_epoch.rs:352-354 ends the epoch and the process. *)
let commit_step s =
  if status_is_running s.status && s.src < max_number then
    [ { s with src = s.src + 1 } ]
  else []

(** [recv] hands the forwarder the next live message in order
    (run_epoch.rs:567). *)
let deliver_live_step s =
  if status_is_running s.status && slot_is_empty s.pending && s.src >= s.w + 1
  then [ { s with pending = Holds (s.w + 1) } ]
  else []

(** [recv] hands the forwarder the re-broadcast copy of output 1 that was
    sitting unread in the ring (subscriber.rs:394-403, :154-180). Guarded on
    [w >= 1] because it is a copy of an output the live path already forwarded -
    that is what makes it stale rather than new. *)
let deliver_rebroadcast_step s =
  if
    status_is_running s.status
    && slot_is_empty s.pending
    && rebroadcast_is_buffered s.rebroadcast
    && s.w >= 1
  then [ { s with pending = Holds 1; rebroadcast = Handed } ]
  else []

(** The ring overran this receiver: [Err(Lagged(n))] is logged and swallowed and
    [recv] resumes at a later message (sync.rs:205-217), so the forwarder
    observes a number above [w + 1] and never learns what it lost. *)
let deliver_lagged_step s =
  if status_is_running s.status && slot_is_empty s.pending && s.src >= s.w + 2
  then [ { s with pending = Holds s.src } ]
  else []

(** [process_output]: send to the engine, then advance the watermark
    (run_epoch.rs:535-551). Blocked while the backlog is full - that is
    [to_engine.send(output).await] parking on backpressure (node.rs:60-68,
    engine/lib.rs:31-38). The watermark takes the forwarded number itself, so a
    stale forward moves it backwards. *)
let send_step s n arm =
  if List.length s.queue < queue_capacity then
    [
      {
        s with
        pending = Empty;
        queue = s.queue @ [ n ];
        w = n;
        stale_forwarded =
          (match arm with
          | Live -> s.stale_forwarded
          | Restale -> true
          | Overgap -> s.stale_forwarded);
        gap_forwarded =
          (match arm with
          | Live -> s.gap_forwarded
          | Restale -> s.gap_forwarded
          | Overgap -> true);
      };
    ]
  else []

(** The [Stale] arm (run_epoch.rs:575-583): warn and [continue], dropping the
    delivery. Under {!No_stale_arm} it falls through to the forward instead. *)
let stale_arm mut s n =
  match mut with
  | Pristine | No_gap_arm | Queue_pop_back ->
      [ { s with pending = Empty; skipped = true } ]
  | No_stale_arm -> send_step s n Restale

(** The [Gap] arm (run_epoch.rs:584-591): return [Err], which ends the epoch at
    run_epoch.rs:352-354. Under {!No_gap_arm} it falls through to the forward
    instead. *)
let gap_arm mut s n =
  match mut with
  | Pristine | No_stale_arm | Queue_pop_back ->
      [ { s with pending = Empty; status = Errored } ]
  | No_gap_arm -> send_step s n Overgap

(** The continuity gate itself (run_epoch.rs:574 with the classifier at
    run_epoch.rs:883-891): judge the message in hand against the watermark. *)
let classify_step mut s =
  match s.pending with
  | Empty -> []
  | Holds n ->
      if Bool.not (status_is_running s.status) then []
      else if n <= s.w then stale_arm mut s n
      else if Int.equal n (s.w + 1) then send_step s n Live
      else gap_arm mut s n

(** Which element the engine dequeues, and what is left: the front
    (engine/lib.rs:124) or, under {!Queue_pop_back}, the back. Returned as a
    list so an empty queue needs no option. *)
let dequeue mut q =
  match q with
  | [] -> []
  | first :: rest -> (
      match mut with
      | Pristine | No_stale_arm | No_gap_arm -> [ (first, rest) ]
      | Queue_pop_back -> (
          match List.rev q with
          | [] -> []
          | last :: rev_rest -> [ (last, List.rev rev_rest) ]))

(** The engine spawns and completes one execution (engine/lib.rs:227-230,
    :120-124, :262-268 merged into one atomic step). It runs regardless of the
    epoch status: on shutdown the engine drains its backlog before returning
    (engine/lib.rs:205-215). Executing a number already in [exec] records the
    second unconditional [inc_leader_count] (payload_builder.rs:30). *)
let execute_step mut s =
  List.map
    (fun (taken, remaining) ->
      { s with queue = remaining; exec = taken :: s.exec })
    (dequeue mut s.queue)

(** The transition relation: one component acts per step. *)
let next_with mut s =
  List.concat
    [
      commit_step s;
      deliver_live_step s;
      deliver_rebroadcast_step s;
      deliver_lagged_step s;
      classify_step mut s;
      execute_step mut s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** Initial state of the world in which no re-broadcast ever arrives: nothing
    committed, nothing forwarded, nothing executed. *)
let initial =
  {
    rebroadcast = Absent;
    src = 0;
    w = 0;
    pending = Empty;
    skipped = false;
    stale_forwarded = false;
    gap_forwarded = false;
    status = Running;
    queue = [];
    exec = [];
  }

(** Initial state of the world in which a copy of output 1 is already sitting
    unread in the broadcast ring, left there by the previous epoch's shutdown
    drain (subscriber.rs:394-403). The branch is resolved here and never written
    afterwards, so [Ag] evaluated at one init explores only that world's cone
    while [K] and the [prove_nonvacuous] reachability check range over the union
    - which is what makes the forwarder's view classes non-singleton. *)
let initial_rebroadcast_buffered = { initial with rebroadcast = Buffered }

(** Is [n] anywhere in the engine's pipeline (queued but not yet executed)? *)
let is_queued n s = List.exists (fun q -> Int.equal q n) s.queue

(** Has [n] been executed at least once? *)
let is_executed n s = List.exists (fun e -> Int.equal e n) s.exec

(** Has [n] been handed to the engine at all - still queued, or already
    executed? Nothing ever leaves [exec], so this is exactly "the forwarder sent
    it". *)
let is_forwarded n s = is_queued n s || is_executed n s

(** Some consensus number was executed twice, i.e. [inc_leader_count]
    (payload_builder.rs:30) ran twice for one output. *)
let has_double_execution s =
  List.exists
    (fun n ->
      List.length (List.filter (fun e -> Int.equal e n) s.exec) >= 2)
    [ 1; 2 ]

(** The highest number executed so far, or 0. *)
let executed_max s = List.fold_left (fun acc n -> Int.max acc n) 0 s.exec

(** Execution skipped a consensus number that is written in stone in the
    consensus chain: some committed [m] below the executed maximum was never
    executed and is not waiting anywhere in the engine's backlog. Numbers still
    queued are deliberately excluded - a deferred output is an ordering
    question, not a hole. *)
let has_execution_hole s =
  let top = executed_max s in
  List.exists
    (fun m ->
      m <= s.src && m < top
      && Bool.not (is_executed m s)
      && Bool.not (is_queued m s))
    [ 1; 2 ]

(** The order in which numbers were executed for the FIRST time, oldest first. A
    re-execution is a duplication question, not an ordering one, so only first
    executions count here. *)
let first_execution_order s =
  List.fold_left
    (fun acc n ->
      if List.exists (fun a -> Int.equal a n) acc then acc else acc @ [ n ])
    []
    (List.rev s.exec)

(** A later-numbered output overtook an earlier one: the first-execution order
    is not strictly increasing. *)
let has_overtaking s =
  let order = first_execution_order s in
  List.exists
    (fun (i, n) ->
      List.exists
        (fun (j, m) -> j > i && m < n)
        (List.mapi (fun j m -> (j, m)) order))
    (List.mapi (fun i n -> (i, n)) order)

(** The delivery in hand is a gap: its number is above [w + 1], so
    [check_output_continuity] classifies it [Gap] (run_epoch.rs:888-889). *)
let gap_in_hand s =
  match s.pending with Empty -> false | Holds n -> n > s.w + 1

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Rebroadcast_unread
      (** a re-broadcast of an already-forwarded output is sitting UNREAD in the
          broadcast ring: the hidden environment fact, in no agent's view *)
  | Rebroadcast_handed
      (** [recv] handed that re-broadcast to the forwarder, so the gate has
          judged (or is about to judge) it *)
  | Stale_skipped
      (** the [Stale] arm ran: "skipping already-forwarded consensus output"
          (run_epoch.rs:576-582) *)
  | Stale_forwarded
      (** a number at or below the watermark reached the engine *)
  | Gap_pending
      (** a lagged delivery above [w + 1] is in the forwarder's hand *)
  | Gap_forwarded  (** a number above [w + 1] reached the engine *)
  | Epoch_errored
      (** the [Gap] arm returned [Err] and the epoch ended
          (run_epoch.rs:584-591 -> :352-354) *)
  | Executed_1  (** consensus output 1 has been executed *)
  | Forwarded_1  (** consensus output 1 was handed to the engine *)
  | Receipt_2
      (** the last execution update the forwarder consumed names output 2,
          i.e. [parent_header] is the block 2 produced *)
  | Double_executed
      (** some number was executed - and leader-counted - twice *)
  | Exec_hole
      (** the executed chain skipped a committed consensus number that is
          nowhere in the engine's backlog *)
  | Exec_out_of_order
      (** first executions did not happen in consensus-number order *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Rebroadcast_unread -> rebroadcast_is_buffered s.rebroadcast
  | Rebroadcast_handed -> rebroadcast_is_handed s.rebroadcast
  | Stale_skipped -> s.skipped
  | Stale_forwarded -> s.stale_forwarded
  | Gap_pending -> gap_in_hand s
  | Gap_forwarded -> s.gap_forwarded
  | Epoch_errored -> status_is_errored s.status
  | Executed_1 -> is_executed 1 s
  | Forwarded_1 -> is_forwarded 1 s
  | Receipt_2 -> Int.equal 0 (slot_compare (last_exec s) (Holds 2))
  | Double_executed -> has_double_execution s
  | Exec_hole -> has_execution_hole s
  | Exec_out_of_order -> has_overtaking s

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Rebroadcast_unread -> "rebroadcast_unread"
  | Rebroadcast_handed -> "rebroadcast_handed"
  | Stale_skipped -> "stale_skipped"
  | Stale_forwarded -> "stale_forwarded"
  | Gap_pending -> "gap_pending"
  | Gap_forwarded -> "gap_forwarded"
  | Epoch_errored -> "epoch_errored"
  | Executed_1 -> "executed_1"
  | Forwarded_1 -> "forwarded_1"
  | Receipt_2 -> "receipt_2"
  | Double_executed -> "double_executed"
  | Exec_hole -> "exec_hole"
  | Exec_out_of_order -> "exec_out_of_order"

(** The CTLK checker over this family's ordered state and view: the presheaf-
    topos denotation, pinned to agree with {!System} by
    test/t_output_forward_gate_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the two hidden-ring initial states,
    mutation-parameterized transitions, the forwarder/engine view, the atom
    valuation. *)
let spec_of mut =
  {
    Checker.init = [ initial; initial_rebroadcast_buffered ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
