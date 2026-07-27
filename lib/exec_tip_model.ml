(** Finite interpreted system for the EXEC_TIP family: the pre-vote execution
    gate that binds a proposed primary header's [latest_execution_block] to the
    VOTER's own executed chain, and the epistemic boundary that gate does NOT
    cross - it authenticates the claimed VALUE against the voter's own blocks
    and never the claimant's possession of them. File citations refer to
    Telcoin-Association/telcoin-network (this checkout, git HEAD [0c59c15b]).

    The modeled mechanism, one proposal round r >= 1 by author V0 over the
    four-validator committee (f = 1):

    - PROPOSE: the proposer stamps whatever its own consensus bus reports as the
      latest executed block into the header it signs
      ([Header::new (.., consensus_bus.app().latest_execution_block_num_hash())],
      proposer.rs:208-215). The field is a plain copied [BlockNumHash] read back
      by [Header::latest_execution_block] (header.rs:158-161), and
      [Header::validate] checks epoch, parent count, digest, committee
      membership and worker ids and NEVER constrains that field against the
      author (header.rs:97-132). So a Byzantine author may stamp a genuine tip
      it never executed (replay) or a value nobody will ever produce (forgery).

    - EXECUTE (per peer): the engine event loop spawns the execution task only
      when it is idle and the queue is non-empty
      ([if self.pending_task.is_none() && !self.queued.is_empty() { ..
      spawn_execution_task() }], engine/lib.rs:227-230). The completion arm
      installs the new parent header (engine/lib.rs:262-271); the SAME arm
      propagates an execution error out of [run] with [?] (engine/lib.rs:264),
      killing the engine. Those two outcomes of the single spawned task are the
      only successors of a queued output. Completion is what eventually pushes
      the sealed header into [RecentBlocks] (payload_builder.rs:186-198 ->
      tn-reth/lib.rs:946-973 -> node.rs:1298-1322).

    - VOTE (per peer): [vote_inner] rejects the header unless
      [wait_for_execution(header.latest_execution_block())] succeeds
      (handler.rs:639-650, returning [HeaderError::UnknownExecutionResult]).
      [wait_for_execution] parks on the [RecentBlocks] watch while
      [current_number < target_number] and only then applies
      [contains_execution_hash] (consensus_bus.rs:620-648), which scans the
      voter's OWN executed headers (recent_blocks.rs:81-89). So a vote is
      possible only after the voter's own engine drained the output, and a
      forged hash at the same number terminates the wait with [Err].

    - CERTIFY: the author self-signs its own header into the vote aggregator
      BEFORE soliciting anyone (certifier.rs:277-280), and
      [quorum_threshold(4) = (2*4)/3 + 1 = 3] (committee.rs:684-688) is enforced
      as [weight >= threshold] by [validate_and_verify]
      (certificate.rs:225-251). A certificate over this header is therefore the
      author's self-vote plus exactly TWO peer votes - and certificate
      validation covers epoch, genesis, [Header::validate], quorum weight and
      the aggregate signature, never [latest_execution_block].

    Components: (1) the author kind, a hidden constant branch fixed at init;
    (2) a per-peer engine phase for the consensus output n whose execution
    yields the block with hash h; (3) a per-peer vote-request decision; (4) the
    certificate flag. Every transition strictly advances a monotone component,
    so the graph is acyclic, every path is finite, and terminals are
    stutter-closed by the kernel (which is what makes the [Af] of S3 honest).

    Role mapping (a knowledge agent must have a real, non-constant view; a
    blank-view party may never appear under K):
    - V0 is the header AUTHOR. It is a modeled actor - the constant [author]
      component IS its choice of what to stamp - but it is deliberately NOT a
      knowledge agent: it carries the constant [View_blank] and never appears
      under K.
    - V1 is a knowledge agent (statements S1 and S3): it sees its own engine
      phase, its own vote-request outcome and the broadcast certificate flag. It
      does NOT see the author kind, the author's execution state, whether the
      claimed tip is genuine (it learns that only by executing -
      [contains_execution_hash] scans its OWN blocks, recent_blocks.rs:81-89),
      or the other peer's engine and decision.
    - V2 is the second honest peer voter, with the symmetric real view. It is a
      modeled actor and never appears under K.
    - V3 is a knowledge agent (statement S2): the committee member whose vote
      the quorum did not need, so its ENTIRE view is the broadcast certificate
      flag - no engine of its own, no individual vote observed, no author kind.
      This is deliberately the coarsest honest projection available: a coarser
      view enlarges the indistinguishability class and makes a positive K
      strictly HARDER, so the abstraction cannot rig S2's knowledge claim.

    A genuine sibling route to a vote exists in the real code and is recorded
    here for R4 honesty: handler.rs:494-505 recasts [Vote::new] WITHOUT entering
    [vote_inner] when [read_vote_info] already holds a vote for this exact
    header digest, and handler.rs:513-565 caches the derived response the same
    way. Both are idempotent replays of a vote the gated path already produced -
    they never create a FIRST vote for an unexecuted tip - so the model's
    monotone single vote step subsumes them and neither repairs the deletion of
    the gate. The other [wait_for_execution] call sites (consensus/state.rs and
    state-sync/lib.rs) run after the vote and the certificate and check only the
    local chain, so they are not pre-vote gates either.

    Modeling admissions (R5): the scope is fixed at claimed height = own height
    + 1, the ahead-proposer case, which is the branch that actually parks; the
    forged claim carries block NUMBER n with a bogus hash, which is the
    terminating branch of [wait_for_execution] (a number far in the future parks
    indefinitely, which is the same shape as {!No_engine_spawn}'s terminal, not
    a separate mechanism); the single f = 1 fault budget is spent entirely on
    the AUTHOR, the adversarially strongest allocation for these statements
    since only the author chooses what tip to stamp; and genesis is out of scope
    (round-0 headers are rejected before any of this, handler.rs:614-617, and
    genesis certificates skip validation entirely, certificate.rs:235-238). *)

(** Which of the three author worlds the run is in. Constant: fixed at init and
    never written by a transition - it is the hidden Byzantine branch, and it is
    what makes every cross-world view class of this family non-singleton. *)
type author_kind =
  | Honest_executed
      (** V0's own engine ran consensus output n and it stamped its genuine
          bus tip (proposer.rs:208-215) *)
  | Byz_replayed
      (** V0 never executed output n; it copied a genuine [BlockNumHash] out of
          a header or certificate it saw. Nothing rejects this:
          [latest_execution_block] is a plain copied field
          (header.rs:158-161) and [Header::validate] never binds it to the
          author (header.rs:97-132) *)
  | Byz_forged
      (** V0 stamped a hash at number n that no honest node will ever produce,
          so every honest voter's [contains_execution_hash] misses
          (recent_blocks.rs:81-89) and [wait_for_execution] returns [Err]
          (consensus_bus.rs:640-647) *)

(** Total order index for {!author_kind}. *)
let author_index = function
  | Honest_executed -> 0
  | Byz_replayed -> 1
  | Byz_forged -> 2

(** Total order on {!author_kind}. *)
let author_compare a b = Int.compare (author_index a) (author_index b)

(** [true] iff the header author's OWN engine produced the block with hash h.
    This is the hidden fact no voter can decide from the header bytes. *)
let author_has_executed = function
  | Honest_executed -> true
  | Byz_replayed -> false
  | Byz_forged -> false

(** [true] iff [header.latest_execution_block] is the genuine tip that executing
    consensus output n actually produces - i.e. iff an honest peer's
    [contains_execution_hash] will hit once its own engine has drained the
    output (recent_blocks.rs:81-89). A replayed tip is genuine; only a forgery
    is not. *)
let author_claim_genuine = function
  | Honest_executed -> true
  | Byz_replayed -> true
  | Byz_forged -> false

(** A peer's engine phase for the consensus output n whose execution yields the
    block with hash h. *)
type engine =
  | Queued
      (** output n sits in [queued] with no pending task; local height is n - 1,
          so a vote request for a tip at n is parked inside
          [wait_for_execution] (consensus_bus.rs:635-639) *)
  | Executed
      (** the idle-and-non-empty spawn (engine/lib.rs:227-230) plus the
          completion arm (engine/lib.rs:262-271) ran, and the sealed header
          reached [RecentBlocks] (payload_builder.rs:186-198 ->
          tn-reth/lib.rs:946-973 -> node.rs:1298-1322) *)
  | Halted
      (** the pending task resolved to [Err] and the [?] at engine/lib.rs:264
          propagated it out of [run]: the engine is gone and the local height
          never advances again *)

(** Total order index for {!engine}. *)
let engine_index = function Queued -> 0 | Executed -> 1 | Halted -> 2

(** Total order on {!engine}. *)
let engine_compare a b = Int.compare (engine_index a) (engine_index b)

(** [true] iff the peer's engine drained output n, so its [RecentBlocks] holds
    the block with hash h. *)
let engine_is_executed = function
  | Queued -> false
  | Executed -> true
  | Halted -> false

(** [true] iff the output is still queued and unexecuted. *)
let engine_is_queued = function
  | Queued -> true
  | Executed -> false
  | Halted -> false

(** [true] iff the engine died on the [?] at engine/lib.rs:264. *)
let engine_is_halted = function
  | Queued -> false
  | Executed -> false
  | Halted -> true

(** A peer's outcome for the author's vote request. *)
type decision =
  | Undecided  (** the request has not resolved: still inside [vote_inner] *)
  | Voted
      (** the gate at handler.rs:639-650 passed and [Vote::new] was reached
          (handler.rs:860-872) *)
  | Rejected
      (** [wait_for_execution] returned [Err], so [vote_inner] answered
          [HeaderError::UnknownExecutionResult] (handler.rs:649) *)

(** Total order index for {!decision}. *)
let decision_index = function Undecided -> 0 | Voted -> 1 | Rejected -> 2

(** Total order on {!decision}. *)
let decision_compare a b = Int.compare (decision_index a) (decision_index b)

(** [true] iff the peer answered the vote request with a [Vote]. *)
let decision_is_voted = function
  | Undecided -> false
  | Voted -> true
  | Rejected -> false

(** [true] iff the vote request has not resolved yet. *)
let decision_is_undecided = function
  | Undecided -> true
  | Voted -> false
  | Rejected -> false

(** [true] iff the peer answered [UnknownExecutionResult]. *)
let decision_is_rejected = function
  | Undecided -> false
  | Voted -> false
  | Rejected -> true

(** The certificate over the proposed header. *)
type cert_state =
  | No_cert  (** the vote aggregator has not reached [quorum_threshold] *)
  | Cert
      (** author self-vote (certifier.rs:277-280) plus both peer votes reaches
          weight 3 >= [quorum_threshold(4)] (committee.rs:684-688,
          certificate.rs:243-246) and the certificate is broadcast *)

(** Total order index for {!cert_state}. *)
let cert_index = function No_cert -> 0 | Cert -> 1

(** Total order on {!cert_state}. *)
let cert_compare a b = Int.compare (cert_index a) (cert_index b)

(** [true] iff the certificate over the header exists. *)
let cert_is_formed = function No_cert -> false | Cert -> true

(** The joint global state: the hidden author branch, both honest peers' engine
    phase and vote decision, and the certificate flag. There is no clock and no
    author-side component beyond [author]: nothing a voter can see distinguishes
    an author that executed from one that merely copied a value. *)
type state = {
  author : author_kind;
  e1 : engine;
  d1 : decision;
  e2 : engine;
  d2 : decision;
  cert : cert_state;
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = author_compare s1.author s2.author in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = engine_compare s1.e1 s2.e1 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = decision_compare s1.d1 s2.d1 in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = engine_compare s1.e2 s2.e2 in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = decision_compare s1.d2 s2.d2 in
          if Bool.not (Int.equal c4 0) then c4 else cert_compare s1.cert s2.cert

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_voter] is the projection of a peer voter
    (V1, V2): its OWN engine phase, its OWN vote-request outcome, and the
    broadcast certificate flag - and nothing else, in particular no component of
    the author and no component of the other peer. [View_observer] is V3's
    projection: the certificate flag alone, the coarsest honest view in the
    family. [View_blank] is the constant view of the author V0, which is an
    actor but not a knowledge agent and never appears under K. *)
type view =
  | View_voter of engine * decision * cert_state
  | View_observer of cert_state
  | View_blank

(** Total deterministic order over ALL fields of a peer voter's view. *)
let view_voter_compare (ea, da, ca) (eb, db, cb) =
  let c = engine_compare ea eb in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = decision_compare da db in
    if Bool.not (Int.equal c1 0) then c1 else cert_compare ca cb

(** Total order on views: [View_blank] < [View_voter] < [View_observer], with
    the field-wise order within each constructor. Every constructor pair is
    spelled: no wildcard arm on the finite view sum. *)
let view_compare a b =
  match (a, b) with
  | View_blank, View_blank -> 0
  | View_blank, (View_voter _ | View_observer _) -> -1
  | (View_voter _ | View_observer _), View_blank -> 1
  | View_voter (ea, da, ca), View_voter (eb, db, cb) ->
      view_voter_compare (ea, da, ca) (eb, db, cb)
  | View_voter _, View_observer _ -> -1
  | View_observer _, View_voter _ -> 1
  | View_observer ca, View_observer cb -> cert_compare ca cb

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V1 and V3 are the knowledge agents; V2 is the symmetric
    second honest voter and V0 is the author - both are modeled actors that
    never appear under K, and V0's view is the constant blank one. *)
let view v s =
  match v with
  | Validator.V1 -> View_voter (s.e1, s.d1, s.cert)
  | Validator.V2 -> View_voter (s.e2, s.d2, s.cert)
  | Validator.V3 -> View_observer s.cert
  | Validator.V0 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 -> View_blank

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_execution_gate
      (** delete the pre-vote execution check
          [if self.consensus_bus.wait_for_execution(header.latest_execution_block())
          .await.is_err() { .. return Err(HeaderError::UnknownExecutionResult(..)) }]
          (handler.rs:639-650), the ONLY pre-vote check of
          [header.latest_execution_block()]. With it gone [vote_inner] falls
          through to [Vote::new] (handler.rs:860-872) for whatever tip the
          header carries, so the decide step becomes [Undecided -> Voted] from
          ANY engine phase and for ANY author kind - adding e.g.
          {author = Honest_executed; e1 = Queued; d1 = Voted; ..} and,
          transitively, [Cert] states whose signers never executed anything.
          NO SIBLING REPAIRS IT: handler.rs:494-505 (recast of a stored vote for
          the same digest) and handler.rs:513-565 (the [auth_last_vote] response
          cache) only replay a vote [vote_inner] already produced, so with the
          gate deleted they replay the UNGATED vote; the equivocation checks at
          handler.rs:787-855 consult epoch, round, digest and certificate
          existence and never execution; [Header::validate] (header.rs:97-132)
          and [Certificate::validate_and_verify] (certificate.rs:225-251) never
          touch [latest_execution_block]; and the other [wait_for_execution]
          call sites (consensus/state.rs:421-434, state-sync/lib.rs:359-377) run
          on already-committed sub-dags and on the consensus-follow path - both
          after the vote and the certificate, both against the LOCAL chain, and
          state.rs:427-433 responds by going [CvvInactive] and shutting the node
          down rather than un-casting a vote. *)
  | No_engine_spawn
      (** delete the idle-and-non-empty spawn step
          [if self.pending_task.is_none() && !self.queued.is_empty() {
          self.pending_task = Some(self.spawn_execution_task()); }]
          (engine/lib.rs:227-230). This removes BOTH successors of
          [engine = Queued]: the drain edge to [Executed] and the fault edge to
          [Halted] are the two outcomes of the single task spawned at
          engine/lib.rs:229 (completion arm :262-271, error propagated by the
          [?] at :264), so with no task neither outcome can fire. Every parked
          state becomes terminal and is stutter-closed, so the [Af] of S3 fails.
          NO SIBLING REPAIRS IT: [spawn_execution_task] (engine/lib.rs:116-154)
          has exactly ONE call site, engine/lib.rs:229 (the identically named
          method in batch-builder/src/lib.rs is a different type); the shutdown
          branch :203-215 and the closed-stream branch :217-221 only RETURN once
          [pending_task] is [None] and [queued] is empty and never execute
          anything; the test-only [push_back_queued_for_test] (:176-182) only
          enqueues; the consensus-stream arm :245-259 only pushes into [queued]
          and is itself gated on [queued.len() < MAX_QUEUED_OUTPUTS] so
          backpressure replaces dropping; the only LIVE writer of
          [RecentBlocks] is the engine-update task node.rs:1298-1322, fed
          exclusively by [finish_executing_output]
          (payload_builder.rs:186-198 -> tn-reth/lib.rs:946-973), the other
          [push_latest] at node.rs:1290-1292 being the one-shot startup seed in
          [try_restore_state]; and the state-sync follow path forwards its
          verified output to the SAME engine (state-sync/lib.rs:378-380). *)

(** A peer's enabled engine moves under a mutation. Pristine (and under
    {!No_execution_gate}, which touches only the vote path) a queued output has
    exactly the two outcomes of the spawned task - drain to [Executed] or die at
    the [?] on its error (engine/lib.rs:262-271) - and both [Executed] and
    [Halted] are terminal for this component. Under {!No_engine_spawn} the task
    is never created, so a queued output has no successor at all. *)
let engine_next mut e =
  match e with
  | Queued -> (
      match mut with
      | Pristine -> [ Executed; Halted ]
      | No_execution_gate -> [ Executed; Halted ]
      | No_engine_spawn -> [])
  | Executed -> []
  | Halted -> []

(** The pristine resolution of a vote request: [wait_for_execution] parks until
    the peer's own height reaches the claimed number and then applies
    [contains_execution_hash] to the peer's OWN executed blocks
    (consensus_bus.rs:635-647, recent_blocks.rs:81-89). So the request resolves
    only once this peer has EXECUTED the output, and it resolves to a vote iff
    the claimed value is one this peer's engine actually produced. *)
let pristine_decide author e =
  match e with
  | Queued -> []
  | Halted -> []
  | Executed -> if author_claim_genuine author then [ Voted ] else [ Rejected ]

(** A peer's enabled vote-request moves under a mutation. A decision is
    monotone: once [Voted] or [Rejected] it never changes, matching the single
    stored vote per authority per epoch/round (the don't-vote-twice check
    handler.rs:807-855 over the vote written at handler.rs:869-870). Under
    {!No_execution_gate} the deleted check lets [vote_inner] fall through to
    [Vote::new] for any tip in any engine phase. *)
let decide_next mut author e d =
  match d with
  | Voted -> []
  | Rejected -> []
  | Undecided -> (
      match mut with
      | Pristine -> pristine_decide author e
      | No_engine_spawn -> pristine_decide author e
      | No_execution_gate -> [ Voted ])

(** The certification step: the author self-signed its header into the
    aggregator up front (certifier.rs:277-280), so the author's self-vote plus
    both peer votes is weight 3 >= [quorum_threshold(4)] = 3
    (committee.rs:684-688, certificate.rs:243-246) and the certificate forms.
    Neither mutation touches this step - certificate validation never inspects
    [latest_execution_block] (certificate.rs:225-251). *)
let certify_next s =
  match s.cert with
  | Cert -> []
  | No_cert ->
      if decision_is_voted s.d1 && decision_is_voted s.d2 then
        [ { s with cert = Cert } ]
      else []

(** The transition relation: the two peers' engines and vote requests advance
    independently, one component per step, plus the certification step. The
    [author] component is never written - it is the hidden branch resolved at
    init. Every move strictly advances a monotone component, so the graph is
    acyclic and terminal states (which the kernel stutter-closes) are exactly
    the saturated ones. *)
let next_with mut s =
  List.concat
    [
      List.map (fun e -> { s with e1 = e }) (engine_next mut s.e1);
      List.map (fun e -> { s with e2 = e }) (engine_next mut s.e2);
      List.map (fun d -> { s with d1 = d }) (decide_next mut s.author s.e1 s.d1);
      List.map (fun d -> { s with d2 = d }) (decide_next mut s.author s.e2 s.d2);
      certify_next s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The three initial states, one per hidden author branch, all with both peers
    parked on the queued output and no certificate. The branch is resolved here
    and never written afterwards, so an [Ag] evaluated at one init explores only
    that world's cone while [K] and the [prove_nonvacuous] reachability check
    range over the union of all three - which is exactly the semantics these
    statements need. *)
let initial =
  let parked =
    { author = Honest_executed; e1 = Queued; d1 = Undecided; e2 = Queued;
      d2 = Undecided; cert = No_cert }
  in
  [
    parked;
    { parked with author = Byz_replayed };
    { parked with author = Byz_forged };
  ]

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Author_executed
      (** the header author's own engine produced the block with hash h
          ([author = Honest_executed]); the hidden K operand of S1 and S2 *)
  | Claim_genuine
      (** [header.latest_execution_block] is the genuine tip of consensus
          output n ([author <> Byz_forged]); the hidden K operand of S3 *)
  | Executed_1
      (** V1's engine drained output n, so its [RecentBlocks] contains h *)
  | Executed_2  (** V2's engine drained output n *)
  | Parked_1
      (** V1's vote request is parked inside [wait_for_execution]: output n
          queued, local height n - 1, no decision yet *)
  | Halted_1
      (** V1's engine died on the [?] at engine/lib.rs:264 *)
  | Voted_1  (** V1 answered the vote request with a [Vote] *)
  | Voted_2  (** V2 answered the vote request with a [Vote] *)
  | Rejected_1
      (** V1 answered [HeaderError::UnknownExecutionResult] (handler.rs:649) *)
  | Cert_formed
      (** the certificate over the header reached quorum and was broadcast *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Author_executed -> author_has_executed s.author
  | Claim_genuine -> author_claim_genuine s.author
  | Executed_1 -> engine_is_executed s.e1
  | Executed_2 -> engine_is_executed s.e2
  | Parked_1 -> engine_is_queued s.e1 && decision_is_undecided s.d1
  | Halted_1 -> engine_is_halted s.e1
  | Voted_1 -> decision_is_voted s.d1
  | Voted_2 -> decision_is_voted s.d2
  | Rejected_1 -> decision_is_rejected s.d1
  | Cert_formed -> cert_is_formed s.cert

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Author_executed -> "author_executed"
  | Claim_genuine -> "claim_genuine"
  | Executed_1 -> "executed_1"
  | Executed_2 -> "executed_2"
  | Parked_1 -> "parked_1"
  | Halted_1 -> "halted_1"
  | Voted_1 -> "voted_1"
  | Voted_2 -> "voted_2"
  | Rejected_1 -> "rejected_1"
  | Cert_formed -> "cert_formed"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the three hidden-branch initial states,
    mutation-parameterized transitions, the two-agent view, the atom
    valuation. *)
let spec_of mut = { Checker.init = initial; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
