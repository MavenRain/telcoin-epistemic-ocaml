(** Finite interpreted system for the ENGINE_QUEUE family: the tn-engine event
    loop's bounded backlog and its SINGLE execution slot, i.e. everything that
    happens to a [ConsensusOutput] between arriving on the [to_engine] channel
    and its executed header becoming the next [parent_header]. File citations
    refer to Telcoin-Association/telcoin-network (this checkout, git HEAD
    [0c59c15b], working tree; every line below was re-opened here).

    THE MODELED MECHANISM, one node, one epoch, over three committed outputs.

    - SUPPLY. The epoch manager forwards one output at a time with
      [to_engine.send(output).await?] (node/run_epoch.rs:547-551) into an mpsc of
      depth [TO_ENGINE_CAPACITY = 64] (node.rs:60-68, channel built at
      node.rs:838). The send is AWAITED, so a full channel blocks the forwarder
      and [last_forwarded_consensus_number] does not advance (run_epoch.rs:548-550
      with the rationale at :527-529). That is what "backpressure" means here, and
      it is why {!upstream} is a component of the state rather than an oracle.

    - INGEST. [output = self.consensus_output_stream.next(), if !consensus_closed
      && self.queued.len() < MAX_QUEUED_OUTPUTS] (engine/lib.rs:245) then
      [self.queued.push_back(output)] (engine/lib.rs:249). The bound is
      [pub const MAX_QUEUED_OUTPUTS: usize = 8] (engine/lib.rs:31-38) whose doc
      states the intent verbatim: "Once the queue is full the engine stops polling
      the consensus stream, pushing backpressure into the [to_engine] channel (and
      ultimately the EpochManager forwarder) instead of buffering here." The model
      scales the bound to {!bound} [= 2] so the saturated regime is reachable in a
      handful of states; the shape of the gate, not the number 8, is what the
      statements quantify over.

    - GRANT. [if self.pending_task.is_none() && !self.queued.is_empty() {
      self.pending_task = Some(self.spawn_execution_task()); }]
      (engine/lib.rs:227-230) with the in-code rationale at :223-226: "only insert
      task if there is none ... it's important that the previous consensus output
      finishes executing before inserting the next task to ensure the parent
      sealed header is finalized". The grant is BY REMOVAL - [if let Some(output)
      = self.queued.pop_front()] (engine/lib.rs:124) - and the captured parent is
      [let parent = self.parent_header.clone()] (engine/lib.rs:126), moved into
      [BuildArguments::new(reth_env, output, parent)] (:128) and then into a
      blocking task (:133-147). [pending_task] is a single [Option], not a
      collection (engine/lib.rs:52-54).

    - EXECUTE. The task calls [execute_consensus_output]
      (engine/payload_builder.rs:22-198). Two shapes matter and the model carries
      both: an output WITH batches chains a block per batch off the captured
      parent ([canonical_header = execute_payload(...)], payload_builder.rs:167-175)
      and commits them ([save_blocks(...); commit()], tn-reth/lib.rs:941-944); an
      EMPTY output whose epoch is not closing SKIPS execution entirely and returns
      the parent unchanged after emitting its engine update
      (payload_builder.rs:84-97). Modelling only the first shape would make "the
      tip strictly advances" look true; it is not, and {!Ob} is the skipped one.

    - RELEASE. [Some(res) = OptionFuture::from(self.pending_task.as_mut()), if
      self.pending_task.is_some() => { ... self.pending_task = None;
      self.parent_header = finalized_header; }] (engine/lib.rs:262-268). This is
      the ONLY writer of [parent_header] after construction, and the only place
      the slot is released.

    - FAILURE. The release arm opens with [let finalized_header =
      res.map_err(Into::into).and_then(|res| res)?] (engine/lib.rs:264): any
      execution error - and there are ordinary ones, e.g.
      [ConsensusOutputUnevenBatches] (payload_builder.rs:57-76),
      [UnknownAuthority] (:104-107) and the engine-update channel closing
      (:92-95) - propagates straight out of [run], and the loop is a CRITICAL
      task whose body ends in [Ok(res?)] (node/src/engine/inner.rs:75-87), so the
      engine does not restart and the backlog is never drained. The model carries
      this as an absorbing {!stopped} state, and both liveness conjuncts in the
      family are stated modulo it. Without it, "the backlog always drains" would
      be true only because the model omitted the one path on which it does not -
      the exact defect rule R5 forbids. Only the AWAITED task's error is fatal: a
      detached task's [tx.send] failure is merely logged (engine/lib.rs:143-145).

    COMPONENTS.

    - {!upstream}: outputs still sitting in the [to_engine] mpsc, in order.
    - {!queued}: the engine's [VecDeque] backlog, head first (engine/lib.rs:51).
    - {!slot}: the in-flight execution task(s). [Idle] is [pending_task = None];
      [Awaiting] is the single [Some(_)]; [Awaiting_with_detached] is the
      two-task shape only the {!No_slot_exclusion} deletion can produce.
    - {!tip}: the height of [self.parent_header] (engine/lib.rs:69).
    - {!head}: the height of the highest block actually written to the database
      by any task (tn-reth/lib.rs:941-944). Pristine these are always equal; they
      are separate fields because the deleted-guard mutant is exactly the case in
      which a task commits blocks whose header the engine never installs.
    - {!a_grants}: how many times {!Oa} has been handed the slot.
    - {!b_done}: {!Ob}'s execution has resolved and its engine update was emitted.
    - {!stopped}: the awaited task returned an error, so engine/lib.rs:264
      propagated it out of [run] and the critical task ended the engine. An
      absorbing state: the backlog and the upstream channel keep whatever they
      held, because nothing drains them after that.
    - {!peer}: a second validator's engine backlog, abstracted to "at its bound or
      not". It is the only non-local component and it is what the family's two
      ignorance claims are about.

    ROLE MAPPING. V0 is the node whose engine this is: a knowledge agent whose
    view is its ENTIRE local engine ({!View_engine}) and nothing else - queue
    depth is exported only as the local Prometheus gauge
    [ENGINE_METRICS.queued_outputs.set(self.queued.len() as f64)]
    (engine/lib.rs:251, :271) and is serialized into no header, certificate, vote
    or request/response payload, so a peer's occupancy is simply absent from V0's
    view. V1 is a peer validator: a knowledge agent whose view is its own backlog
    occupancy PLUS V0's last PUBLISHED execution tip - the engine update
    ([engine_update_tx.try_send((leader_round, consensus_num_hash, Some(head)))],
    tn-reth/lib.rs:962-973) drives [recent_blocks.push_latest]
    (node.rs:1305-1322, recent_blocks.rs:40-60), which is the one execution fact
    that does leave the node. Giving V1 that channel is deliberate: it is the
    strongest peer view the real code supports, so "V1 cannot tell whether V0's
    slot is occupied" is not an artifact of an impoverished view. V2..V9 are
    idle non-agents with the constant blank {!View_idle} and never appear under
    [K].

    SCOPE relative to the output_forward_gate family, which models the hop
    immediately upstream: that family's gates are [check_output_continuity]'s
    [Stale]/[Gap] arms (run_epoch.rs:574-592) and [pop_front] vs [pop_back]
    (engine/lib.rs:124), i.e. WHICH outputs reach the engine and in what order.
    This family's gates are the three that govern the slot itself - the queue
    bound at engine/lib.rs:245, the [pending_task.is_none()] conjunct at
    engine/lib.rs:227, and the REMOVAL in [pop_front] at engine/lib.rs:124 - i.e.
    how many may execute at once, how deep the backlog may grow, and how many
    times one output may be served. Each can be deleted without touching the
    others. *)

(** One committed consensus output. The three are the whole modelled window, in
    commit order; each carries a leader author, which the scheduler never reads.
    That the model fixes each output's payload shape rather than resampling it is
    a determinism choice, not a restriction: both shapes are present. *)
type out =
  | Oa
      (** V0's leader round: an output WITH batches, so execution chains a block
          and advances the tip (payload_builder.rs:137-185). *)
  | Ob
      (** V1's leader round: an EMPTY output whose epoch is not closing, so
          [execute_consensus_output] skips execution, emits the engine update
          with no block and returns the parent unchanged
          (payload_builder.rs:84-97). Its presence is what stops "the tip
          advances on every completion" from being modelled as true. *)
  | Oc  (** V0's next leader round: another output with batches. *)

(** Total order index for {!out}. *)
let out_index = function Oa -> 0 | Ob -> 1 | Oc -> 2

(** Total order on {!out}. *)
let out_compare a b = Int.compare (out_index a) (out_index b)

(** Total order on {!out} lists (lexicographic, length-then-content free: the
    element order is what the FIFO discipline is about). *)
let rec out_list_compare a b =
  match (a, b) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs, y :: ys ->
      let c = out_compare x y in
      if Bool.not (Int.equal c 0) then c else out_list_compare xs ys

(** An in-flight execution task: the output moved into it
    ([BuildArguments::new(reth_env, output, parent)], engine/lib.rs:128) and the
    height of the [parent_header] it cloned at spawn time (engine/lib.rs:126).
    The parent is captured once and never re-read, which is the whole point. *)
type task = { on : out; parent : int }

(** Total deterministic comparison over both {!task} fields. *)
let task_compare t1 t2 =
  let c = out_compare t1.on t2.on in
  if Bool.not (Int.equal c 0) then c else Int.compare t1.parent t2.parent

(** The engine's execution slot, i.e. the state of [pending_task]
    (engine/lib.rs:52-54). *)
type slot =
  | Idle  (** [pending_task = None]: the loop may grant the slot. *)
  | Awaiting of task
      (** [pending_task = Some(rx)]: exactly one task in flight and the engine is
          awaiting its oneshot. *)
  | Awaiting_with_detached of task * task
      (** TWO tasks in flight: the awaited one and a DETACHED one whose oneshot
          receiver was dropped when [self.pending_task = Some(...)]
          (engine/lib.rs:229) overwrote it. The detached task keeps running and
          still commits its blocks, but engine/lib.rs:268 never sees its header.
          Unreachable unless the [self.pending_task.is_none() &&] conjunct at
          engine/lib.rs:227 is deleted. *)

(** Total order on {!slot}: every constructor pair spelled, no wildcard arm. *)
let slot_compare a b =
  match (a, b) with
  | Idle, Idle -> 0
  | Idle, (Awaiting _ | Awaiting_with_detached _) -> -1
  | (Awaiting _ | Awaiting_with_detached _), Idle -> 1
  | Awaiting t1, Awaiting t2 -> task_compare t1 t2
  | Awaiting _, Awaiting_with_detached _ -> -1
  | Awaiting_with_detached _, Awaiting _ -> 1
  | Awaiting_with_detached (a1, d1), Awaiting_with_detached (a2, d2) ->
      let c = task_compare a1 a2 in
      if Bool.not (Int.equal c 0) then c else task_compare d1 d2

(** A peer validator's engine backlog, abstracted to the only thing the family's
    ignorance claims need: whether it is at its own [MAX_QUEUED_OUTPUTS] bound. *)
type peer =
  | Peer_below  (** the peer's engine is draining normally *)
  | Peer_at_bound
      (** the peer's engine is saturated, so ITS forwarder is blocked too *)

(** Total order index for {!peer}. *)
let peer_index = function Peer_below -> 0 | Peer_at_bound -> 1

(** Total order on {!peer}. *)
let peer_compare a b = Int.compare (peer_index a) (peer_index b)

(** The joint global state: V0's whole engine pipeline plus the peer's occupancy. *)
type state = {
  upstream : out list;
      (** outputs still undelivered in the [to_engine] mpsc (node.rs:838) *)
  queued : out list;  (** the engine's backlog, head first (engine/lib.rs:51) *)
  slot : slot;  (** [pending_task] (engine/lib.rs:54) *)
  tip : int;  (** height of [parent_header] (engine/lib.rs:69) *)
  head : int;
      (** height of the highest block committed to the database by any task
          (tn-reth/lib.rs:941-944) *)
  a_grants : int;  (** how many times {!Oa} has been granted the slot *)
  b_done : bool;  (** {!Ob}'s execution resolved and its engine update was sent *)
  stopped : bool;
      (** the awaited task errored, [?] at engine/lib.rs:264 ended [run] and the
          critical task did not restart it (node/src/engine/inner.rs:75-87) *)
  peer : peer;  (** the peer node's backlog occupancy *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = out_list_compare s1.upstream s2.upstream in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = out_list_compare s1.queued s2.queued in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = slot_compare s1.slot s2.slot in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Int.compare s1.tip s2.tip in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Int.compare s1.head s2.head in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Int.compare s1.a_grants s2.a_grants in
            if Bool.not (Int.equal c5 0) then c5
            else
              let c6 = Bool.compare s1.b_done s2.b_done in
              if Bool.not (Int.equal c6 0) then c6
              else
                let c7 = Bool.compare s1.stopped s2.stopped in
                if Bool.not (Int.equal c7 0) then c7
                else peer_compare s1.peer s2.peer

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. *)
type view =
  | View_engine of state
      (** V0: its ENTIRE local engine - upstream channel, backlog, slot,
          [parent_header], committed head and its own execution counters. The
          peer field is normalised to {!Peer_below} here, which is exactly the
          claim that V0 sees nothing of the peer's occupancy: queue depth is only
          ever the local gauge at engine/lib.rs:251 and is in no wire message. *)
  | View_peer of peer * int
      (** V1: its own backlog occupancy, plus V0's last PUBLISHED execution tip -
          the engine update at tn-reth/lib.rs:962-973 feeding
          [recent_blocks.push_latest] (node.rs:1305-1322). It does NOT carry V0's
          queue, V0's slot, or whether a task is in flight; none of those is
          serialized anywhere. *)
  | View_idle  (** the constant blank view of the non-agents V2..V9 *)

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_engine _ | View_peer _) -> -1
  | (View_engine _ | View_peer _), View_idle -> 1
  | View_engine s1, View_engine s2 -> state_compare s1 s2
  | View_engine _, View_peer _ -> -1
  | View_peer _, View_engine _ -> 1
  | View_peer (p1, t1), View_peer (p2, t2) ->
      let c = peer_compare p1 p2 in
      if Bool.not (Int.equal c 0) then c else Int.compare t1 t2

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 (the engine's own node) and V1 (a peer) are the knowledge
    agents; every other committee member is an idle non-agent with the constant
    blank view and never appears under [K]. *)
let view v s =
  match v with
  | Validator.V0 -> View_engine { s with peer = Peer_below }
  | Validator.V1 -> View_peer (s.peer, s.tip)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** [MAX_QUEUED_OUTPUTS] at model scale. The real constant is 8
    (engine/lib.rs:38); 2 is the smallest value at which "backlog at the bound
    while the upstream channel still holds an output" is reachable inside a
    three-output window. *)
let bound = 2

(** Model cap on how many times one output may be handed the slot. Pristine and
    two of the three mutants never reach it (each output is removed when granted,
    engine/lib.rs:124); it exists only to keep {!Reexecute_head}'s unbounded
    re-grant loop finite, and it can only bind in states that already violate the
    one-shot conjunct, so it cannot manufacture a proof. *)
let grant_cap = 2

(** The header height an in-flight task returns. An output with batches chains a
    block onto its captured parent (payload_builder.rs:167-175); the empty
    non-epoch-closing output returns [canonical_header] unchanged
    (payload_builder.rs:84-97). *)
let tip_after t = match t.on with Ob -> t.parent | Oa | Oc -> t.parent + 1

(** Is this the empty output whose engine update carries no block? *)
let is_empty_output o = match o with Ob -> true | Oa | Oc -> false

(** Is this {!Oa}, the output whose grant count the one-shot conjunct watches? *)
let is_oa o = match o with Oa -> true | Ob | Oc -> false

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_slot_exclusion
      (** delete the [self.pending_task.is_none() &&] conjunct at
          engine/lib.rs:227, keeping [!self.queued.is_empty()]. The loop then
          re-enters and spawns again while a task is still running, so this ADDS
          transitions [Awaiting t -> Awaiting_with_detached (t', t)]: two blocking
          tasks in flight, both cloning the SAME [self.parent_header]
          (engine/lib.rs:126), and the assignment at :229 drops the first
          receiver so engine/lib.rs:268 never installs its header even though its
          blocks are committed. No sibling path repairs it. (a)
          [build_block_from_batch_payload] only does
          [state_by_block_hash(parent_header.hash())] (tn-reth/lib.rs:736-739), so
          a duplicate parent is still a valid state root and nothing errors. (b)
          [finish_executing_output] is [save_blocks(blocks, Full)?; commit()?]
          with no contiguity and no duplicate-height check
          (tn-reth/lib.rs:941-944). (c) [push_latest] appends unconditionally -
          no dedup, no monotonic round check (recent_blocks.rs:40-60), and it
          overwrites [last_consensus_round] with whatever it is handed. (d) the
          only other writer of [pending_task] is the release arm at
          engine/lib.rs:266. (e) [replay_missed_consensus] is the one guard keyed
          on output identity and it is startup-only, with its doc conceding the
          consequence: "replaying output the engine already applied causes double
          execution" (node/start_epoch.rs:60-64, :71-93). *)
  | No_queue_bound
      (** delete the [self.queued.len() < MAX_QUEUED_OUTPUTS] conjunct from the
          consensus-stream select arm at engine/lib.rs:245. This ADDS transitions
          in which the engine keeps draining the [to_engine] channel while a task
          is in flight, so [queued] grows past the bound AND the upstream channel
          empties - the forwarder's blocking [send().await]
          (run_epoch.rs:547-551) never blocks again. No sibling path repairs it:
          [TO_ENGINE_CAPACITY = 64] (node.rs:60-68, :838) bounds the hop upstream,
          not the engine's [VecDeque] - with the gate gone that depth is a supply,
          not a bound, exactly as its own doc warns ("A deep channel here would
          defeat the engine's bound by buffering the backlog one hop upstream").
          [spawn_execution_task] pops exactly one (engine/lib.rs:124), there is no
          eviction, no [truncate] and no other capacity check in the file - the
          only writers of [queued] are the [push_back] at :249, the [pop_front] at
          :124 and the [cfg(test)] helper at :179-182. *)
  | Reexecute_head
      (** delete the REMOVAL from [self.queued.pop_front()] at engine/lib.rs:124,
          i.e. read the head without consuming it. This REMOVES the transition
          that shortens the backlog on a grant: the same head is re-granted on
          every loop iteration, so it executes repeatedly and everything queued
          behind it starves. No sibling path repairs it: [execute_consensus_output]
          has no already-executed check keyed on the consensus digest
          (payload_builder.rs:22-36 computes the digest only for the tracing span
          and the mix hash), [finish_executing_output] rejects no duplicate
          (tn-reth/lib.rs:941-944), [push_latest] appends the repeat with no dedup
          and no monotonic round check (recent_blocks.rs:40-60), and the only
          identity-keyed guard, [replay_missed_consensus]
          (node/start_epoch.rs:71-93), runs once at epoch start and cannot help a
          running engine. *)

(** The ingest transition: the consensus-output arm of the [select!]
    (engine/lib.rs:245-252), gated on the queue bound in every model except
    {!No_queue_bound}. *)
let ingest_steps mut s =
  let gate_open =
    match mut with
    | Pristine | No_slot_exclusion | Reexecute_head ->
        List.length s.queued < bound
    | No_queue_bound -> true
  in
  match s.upstream with
  | [] -> []
  | o :: rest ->
      if gate_open then
        [ { s with upstream = rest; queued = s.queued @ [ o ] } ]
      else []

(** The grant transition: engine/lib.rs:227-230 selecting a head and
    [spawn_execution_task] (engine/lib.rs:120-133) removing it and capturing
    [parent_header]. *)
let spawn_steps mut s =
  match s.queued with
  | [] -> []
  | h :: rest ->
      let granted = { on = h; parent = s.tip } in
      let grants = if is_oa h then s.a_grants + 1 else s.a_grants in
      if grants > grant_cap then []
      else
        let base = { s with a_grants = grants } in
        (match mut with
        | Pristine | No_queue_bound -> (
            match s.slot with
            | Idle -> [ { base with queued = rest; slot = Awaiting granted } ]
            | Awaiting _ | Awaiting_with_detached _ -> [])
        | No_slot_exclusion -> (
            match s.slot with
            | Idle -> [ { base with queued = rest; slot = Awaiting granted } ]
            | Awaiting old ->
                [
                  {
                    base with
                    queued = rest;
                    slot = Awaiting_with_detached (granted, old);
                  };
                ]
            | Awaiting_with_detached _ -> [])
        | Reexecute_head -> (
            match s.slot with
            | Idle -> [ { base with slot = Awaiting granted } ]
            | Awaiting _ | Awaiting_with_detached _ -> []))

(** The release transition: the execution-result arm at engine/lib.rs:262-268.
    Only the AWAITED task's header reaches [self.parent_header = finalized_header]
    (:268); a detached task still runs to completion, still commits its blocks
    (tn-reth/lib.rs:941-944) and still emits its engine update
    (tn-reth/lib.rs:962-973), but its oneshot receiver was dropped at :229 so the
    engine never installs its header. Resolving the detached task first is a
    determinism choice inside a shape only {!No_slot_exclusion} can reach; it
    does not gate anything, since the two-task state itself is already the
    violation.

    The awaited task has TWO successors, because the arm opens with
    [res.map_err(Into::into).and_then(|res| res)?] (engine/lib.rs:264): the result
    either installs a header or ends the engine for good, since [run] is a
    critical task whose body is [Ok(res?)] (node/src/engine/inner.rs:75-87). The
    failure successor keeps [upstream] and [queued] exactly as they were - nothing
    drains them once the loop is gone - and it is what stops this family's [AF]
    conjuncts from being manufactured. The detached task has NO failure successor:
    its [tx.send] failure is only logged (engine/lib.rs:143-145), because the
    engine dropped its receiver at :229 and never awaits it. *)
let complete_steps s =
  match s.slot with
  | Idle -> []
  | Awaiting t ->
      let h = tip_after t in
      [
        {
          s with
          slot = Idle;
          tip = h;
          head = Int.max s.head h;
          b_done = s.b_done || is_empty_output t.on;
        };
        { s with slot = Idle; stopped = true };
      ]
  | Awaiting_with_detached (a, d) ->
      [
        {
          s with
          slot = Awaiting a;
          head = Int.max s.head (tip_after d);
          b_done = s.b_done || is_empty_output d.on;
        };
      ]

(** The engine's own steps under a mutation, before the peer is resampled. A
    stopped engine has none: the loop returned and the critical task took the
    node with it (node/src/engine/inner.rs:75-87), so {!stopped} is absorbing. *)
let engine_steps mut s =
  if s.stopped then []
  else ingest_steps mut s @ spawn_steps mut s @ complete_steps s

(** The transition relation. Every step advances V0's engine AND resamples the
    peer's occupancy, because the peer's engine runs concurrently and its depth is
    unconstrained by anything V0 does. Resampling on the engine step rather than
    as a step of its own is deliberate: a standalone peer step would be an
    infinite path on which V0's engine never progresses, which would defeat every
    [AF] claim in the family for a reason that has nothing to do with the code. *)
let next_with mut s =
  List.concat_map
    (fun s' -> [ { s' with peer = Peer_below }; { s' with peer = Peer_at_bound } ])
    (engine_steps mut s)

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: three outputs committed and handed to the forwarder,
    nothing ingested, the slot free, the chain at genesis height 0. *)
let initial =
  {
    upstream = [ Oa; Ob; Oc ];
    queued = [];
    slot = Idle;
    tip = 0;
    head = 0;
    a_grants = 0;
    b_done = false;
    stopped = false;
    peer = Peer_below;
  }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Two_tasks_in_flight
      (** the engine holds two execution tasks at once - the shape
          [pending_task : Option<_>] plus the guard at engine/lib.rs:227 forbids *)
  | Executing  (** [pending_task.is_some()]: a task is in flight *)
  | Parent_is_committed_head
      (** every in-flight task captured a parent equal to the highest block
          already committed, i.e. execution is chaining onto the real head rather
          than onto a stale header *)
  | Queue_over_bound  (** [queued.len() > MAX_QUEUED_OUTPUTS] *)
  | Queue_gate_closed
      (** [queued.len() >= MAX_QUEUED_OUTPUTS]: the select arm at
          engine/lib.rs:245 is disabled and the stream is not polled *)
  | Upstream_undelivered
      (** the [to_engine] channel still holds an output the engine has not taken *)
  | Ob_queued  (** the second leader's output is sitting in the backlog *)
  | Ob_resolved
      (** {!Ob}'s execution resolved and its engine update was emitted
          (payload_builder.rs:92-95) *)
  | Oa_granted_twice  (** {!Oa} occupied the execution slot more than once *)
  | Engine_stopped
      (** an execution error propagated out of [run] at engine/lib.rs:264 and the
          critical task did not restart it (node/src/engine/inner.rs:75-87), so
          nothing will drain the backlog again *)
  | Peer_saturated  (** the peer node's engine backlog is at its own bound *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Two_tasks_in_flight -> (
      match s.slot with
      | Idle | Awaiting _ -> false
      | Awaiting_with_detached _ -> true)
  | Executing -> (
      match s.slot with
      | Idle -> false
      | Awaiting _ | Awaiting_with_detached _ -> true)
  | Parent_is_committed_head -> (
      match s.slot with
      | Idle -> true
      | Awaiting t -> Int.equal t.parent s.head
      | Awaiting_with_detached (a1, d1) ->
          Int.equal a1.parent s.head && Int.equal d1.parent s.head)
  | Queue_over_bound -> List.length s.queued > bound
  | Queue_gate_closed -> List.length s.queued >= bound
  | Upstream_undelivered -> (
      match s.upstream with [] -> false | _ :: _ -> true)
  | Ob_queued -> List.exists is_empty_output s.queued
  | Ob_resolved -> s.b_done
  | Oa_granted_twice -> s.a_grants > 1
  | Engine_stopped -> s.stopped
  | Peer_saturated -> (
      match s.peer with Peer_below -> false | Peer_at_bound -> true)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Two_tasks_in_flight -> "two_in_flight"
  | Executing -> "executing"
  | Parent_is_committed_head -> "parent = committed_head"
  | Queue_over_bound -> "|queued| > MAX"
  | Queue_gate_closed -> "|queued| >= MAX"
  | Upstream_undelivered -> "to_engine_nonempty"
  | Ob_queued -> "queued(o_B)"
  | Ob_resolved -> "executed(o_B)"
  | Oa_granted_twice -> "grants(o_A) > 1"
  | Engine_stopped -> "engine_stopped"
  | Peer_saturated -> "peer_at_bound"

(** The CTLK checker over this family's ordered state and view: the presheaf
    topos denotation, pinned to agree with {!System} at every reachable world by
    test/t_engine_queue_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the single initial state,
    mutation-parameterized transitions, the two-agent view projection, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
