(** Finite interpreted system for the PREFETCH family (DESIGN family
    CONSENSUS-EXT #6, batch-digest-gossip-prefetch-knowledge-via-verified-
    fetch): a non-holding validator that receives a gossiped worker-batch
    digest learns that some peer holds the payload ONLY after a
    content-address-verified fetch actually lands the payload - the received
    digest alone (a bare hash) never grants that knowledge, because a
    Byzantine committee author can gossip a digest for a payload that
    exists nowhere.

    Mechanisms modeled, keyed to Telcoin-Association/telcoin-network:
    - an honest worker seals a batch only after it reaches an attestation
      quorum (so quorum-many workers hold the payload), then publishes the
      digest on the authorized-publishers-restricted worker-batch topic
      (crates/consensus/worker/src/worker.rs:293-320, the [publish_batch]
      wrapper crates/consensus/worker/src/network/handle.rs:147-154);
    - a listening validator that lacks the payload fans out a fetch on
      receiving the gossiped digest
      (crates/consensus/worker/src/network/handler.rs:142-228, the
      gossip-triggered [request_batches] at handler.rs:188-223);
    - the fetch pipeline is CONTENT-ADDRESSED end to end: the receiver
      recomputes each returned batch's digest and keys the tuple by it
      ([let batch_digest = batch.digest()] then
      [batches.push((batch_digest, batch))] in [read_sync_batches],
      crates/consensus/worker/src/network/handle.rs:509,523), the caller
      admits only requested keys ([requested_digests.remove(&digest)],
      handle.rs:241-244), and the store insert is keyed by that same
      recomputed digest while the cache probe uses the gossiped hash
      (handler.rs:194-208 keyed insert, handler.rs:167-169 probe) - so a
      mismatched (bogus) payload can only ever occupy its OWN key b',
      never the gossiped key b; the digest-binding stream abort
      (handle.rs:512-516) is a redundant defense in front of this;
    - the prefetch admission cap (handler.rs:181-187) is modeled as
      never-binding (a single outstanding digest), so the gossip-triggered
      leads-to holds unconditionally on the modeled runs;
    - epoch/seal context: crates/node/src/manager/node/start_epoch.rs:697-705,
      crates/types/src/worker/sealed_batch.rs:119-124.

    The hidden Byzantine sub-choice [Choice_unchosen] labels only the
    initial state and resolves into BOTH honest committee-author branches at
    the first (gossip) transition - after V1's local view is already fixed -
    so the two branches view-collide for V1:
    - [Cooperate]: V3's worker really sealed the batch b (payload held by the
      quorum {V0, V2, V3}) and gossiped its digest, publisher V3;
    - [Forge_digest]: V3 gossiped the SAME digest b with no payload held
      anywhere, publisher V3.
    The publisher is PINNED to V3 in both branches (the worker-batch topic is
    publisher-restricted, so V1's view records who published): a distinct
    honest author would not view-collide and the ~K witness would evaporate.

    The single digest b is shared across the two branches on purpose. To a
    non-holder V1 the received digest is an opaque token - a 32-byte hash
    tells V1 nothing about whether a preimage payload exists - so the
    Cooperate "b is really held" pre-fetch state and the Forge "b is held by
    nobody" pre-fetch state are indistinguishable in V1's view. That
    collision is the entire epistemic content: receiving a digest is not
    knowledge that a holder exists. Once V1 has STORED a batch under key b,
    its view records "I hold b"; in the pristine model that storage happened
    only through content-addressed keying - the stored key is the payload's
    recomputed digest, so occupying key b requires the genuine preimage,
    i.e. a responder that really held the payload - and
    [K (V1, Held_by_other)] is then sound. Keying storage by the GOSSIPED
    digest instead (the mutation) lets V1 store a bogus payload from a
    NON-holder under key b: the "V1 holds b" view then also covers a run
    with no real holder, collapsing that knowledge - which is exactly the
    confirm-by-mutation refutation.

    Role mapping of the four kernel validator slots for this family:
    - V1: the honest listening validator whose prefetch knowledge is at issue
      - the ONLY knowledge agent; its view is (received-a-digest-from-V3,
      holds-a-batch-under-key-b, a-cert-references-b-in-its-dag).
    - V3: the committee batch author/publisher; a State-fields party only
      (its hidden Cooperate/Forge choice and the real holder set), constant
      blank view, never under K.
    - V0, V2: the rest of the honest committee, abstracted into the sealing
      attestation quorum behind the Cooperate branch; constant blank views,
      never under K.

    Payloads are unforgeable-by-construction holdings: [real_holders] is
    populated only where the Cooperate branch sealed the genuine batch. *)

(** The phase machine: V3 gossips the digest and the hidden author-branch
    resolves ([Gossip]); V1 fetches, and content-addressed keying decides
    whether the response occupies key b ([Deliver]); then the terminal
    stutter ([Done], stutter-closed by the kernel). *)
type phase = Gossip | Deliver | Done

(** Total order index for {!phase}. *)
let phase_index = function Gossip -> 0 | Deliver -> 1 | Done -> 2

(** Total order on {!phase} via {!phase_index}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The hidden committee-author sub-choice, [Choice_unchosen] in the initial
    state and resolved into BOTH branches by the gossip transition - after
    V1's view is fixed, so the branches collide. [Cooperate]: V3's worker
    sealed the real batch b (payload held by the quorum) and gossiped its
    digest. [Forge_digest]: V3 gossiped the same digest b for a payload held
    nowhere. Publisher is V3 in both. *)
type choice = Choice_unchosen | Cooperate | Forge_digest

(** Total order index for {!choice}. *)
let choice_index = function
  | Choice_unchosen -> 0
  | Cooperate -> 1
  | Forge_digest -> 2

(** Total order on {!choice} via {!choice_index}. *)
let choice_compare a b = Int.compare (choice_index a) (choice_index b)

(** Sets of validators: the real holders of batch b's payload - the
    attestation quorum behind a sealed batch (worker.rs:293-320). Empty
    under [Forge_digest]; never contains V1 (V1's own storage is the
    separate [v1_stored] flag). *)
module Vset = Set.Make (Validator)

(** The global state. [choice] and [real_holders] are hidden from V1;
    [recv] is V1's record that it received the gossiped digest from V3;
    [v1_stored] is whether V1 has a batch stored under key b (set only where
    a fetch response was accepted); [dag_ref] is whether a certificate whose
    header references b sits in V1's dag. *)
type state = {
  phase : phase;
  choice : choice;
  recv : bool;
  real_holders : Vset.t;
  v1_stored : bool;
  dag_ref : bool;
}

(** Total deterministic order over ALL state fields. *)
let state_compare a b =
  let c = phase_compare a.phase b.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = choice_compare a.choice b.choice in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Bool.compare a.recv b.recv in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Vset.compare a.real_holders b.real_holders in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare a.v1_stored b.v1_stored in
          if Bool.not (Int.equal c4 0) then c4
          else Bool.compare a.dag_ref b.dag_ref

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** V1's local view - the knowledge ground for [K (V1, _)]: whether it
    received a digest gossip from V3 (publisher visible, digest value opaque
    to a non-holder), whether it holds a batch under key b, and whether a
    cert referencing b sits in its dag. The hidden author-branch and the
    real holder set are absent: V1 knows only what it locally holds. *)
type view_local = {
  w_recv : bool;
  w_stored : bool;
  w_dag_ref : bool;
}

(** Total deterministic order over ALL view fields. *)
let view_compare a b =
  let c = Bool.compare a.w_recv b.w_recv in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Bool.compare a.w_stored b.w_stored in
    if Bool.not (Int.equal c1 0) then c1
    else Bool.compare a.w_dag_ref b.w_dag_ref

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view_local

  let compare = view_compare
end

(** V1's view projection: received-from-V3, own storage, own dag reference. *)
let view_v1 s =
  { w_recv = s.recv; w_stored = s.v1_stored; w_dag_ref = s.dag_ref }

(** The constant blank view of the non-agent validators (V0, V2, V3): they
    are State-fields parties in this family and never appear under K, so
    their projection carries no information. *)
let view_blank = { w_recv = false; w_stored = false; w_dag_ref = false }

(** The total view function: V1 is the sole knowledge agent; V0, V2, V3
    project to the constant blank view. *)
let view v s =
  match v with
  | Validator.V1 -> view_v1 s
  | Validator.V0 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      view_blank

(** The initial state: gossip pending, author-branch unresolved, nothing
    received, no holders, nothing stored, no dag reference. *)
let initial =
  {
    phase = Gossip;
    choice = Choice_unchosen;
    recv = false;
    real_holders = Vset.empty;
    v1_stored = false;
    dag_ref = false;
  }

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_content_addressing
      (** key fetched batches by the GOSSIPED digest instead of the
          recomputed one - replace [let batch_digest = batch.digest()] /
          [batches.push((batch_digest, batch))]
          (crates/consensus/worker/src/network/handle.rs:509,523) with the
          requested digest b: a bogus payload is then keyed b, sails
          through the requested-digests filter (handle.rs:241-244) and the
          keyed store insert (handler.rs:201-202), so in the [Forge_digest]
          branch V1 comes to hold b with NO real holder - a state
          view-identical to the Cooperate faithful hold, which collapses
          [K (V1, Held_by_other)] and refutes the verified-fetch knowledge
          conjunct. Deleting only the digest-binding stream abort
          (handle.rs:512-516) would NOT reach this state: content-addressed
          keying plus the caller filter silently repair that deletion, so
          the pin is anchored on the keying itself, which no sibling path
          recomputes downstream *)

(** The sealing attestation quorum behind the Cooperate branch: the
    validators that hold b's payload once V3's worker sealed it
    (worker.rs:293-320). V1 is excluded - it is the non-holding listener
    that must fetch. *)
let coop_holders = Vset.of_list [ Validator.V0; Validator.V2; Validator.V3 ]

(** Gossip step: V3 publishes b's digest and the hidden author-branch
    resolves into BOTH successors (handler.rs:142-228 receiving the gossip;
    handle.rs:147-154 the publish wrapper). [Cooperate] additionally records
    that the quorum really holds b's payload; [Forge_digest] leaves the
    holder set empty. V1's view - received-a-digest-from-V3, not stored -
    is identical across the two, the load-bearing collision. *)
let gossip_step s =
  [
    {
      s with
      phase = Deliver;
      choice = Cooperate;
      recv = true;
      real_holders = coop_holders;
    };
    { s with phase = Deliver; choice = Forge_digest; recv = true };
  ]

(** Whether a fetch response whose payload does NOT recompute to the
    requested digest b ends up stored UNDER KEY b. Pristine: never - the
    pipeline is content-addressed (recomputed-digest keying at
    handle.rs:509,523, requested-key filter at handle.rs:241-244, keyed
    insert at handler.rs:201-202), so the bogus payload can only occupy its
    own key b'. Under [No_content_addressing] the gossiped digest b is the
    storage key, so it occupies b. *)
let stored_under_gossip_key = function
  | Pristine -> false
  | No_content_addressing -> true

(** Deliver step: V1 (holding the digest, lacking the payload) fetches.
    - [Cooperate]: an honest holder serves the genuine batch, its recomputed
      digest IS b, so content-addressed keying stores it under b
      (handle.rs:497-523 accept path, handler.rs:201-202 keyed insert) - V1
      now holds b. Modeled as the single faithful outcome (any Byzantine
      bogus response lands under its own key, never b, and the fetch retries
      until an honest holder answers under bounded-delay fairness), so
      [holds_i(b)] is inevitable here.
    - [Forge_digest]: no honest holder exists. Two fetch outcomes - a
      not-found (nothing stored) and a Byzantine bogus payload whose digest
      mismatches b. Pristine: content-addressed keying files the bogus
      payload under its own digest b' and the requested-key filter drops it
      (handle.rs:241-244), so key b stays empty and both outcomes coincide.
      Under [No_content_addressing] it is keyed by the gossiped b, so V1
      holds b with no real holder.
    - [Choice_unchosen]: never reached at [Deliver] (resolved at [Gossip]);
      no successors. *)
let deliver_step mut s =
  match s.choice with
  | Cooperate -> [ { s with phase = Done; v1_stored = true } ]
  | Forge_digest ->
      [
        { s with phase = Done };
        {
          s with
          phase = Done;
          v1_stored = s.v1_stored || stored_under_gossip_key mut;
        };
      ]
  | Choice_unchosen -> []

(** The transition relation, parameterized by the mutation; [Done] is
    terminal and stutter-closed by the kernel. *)
let next_with mut s =
  match s.phase with
  | Gossip -> gossip_step s
  | Deliver -> deliver_step mut s
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The atom vocabulary: exactly what the statement quantifies over, plus
    the terminal probe for the sanity suite. *)
type atom =
  | Recv_digest
      (** V1 received b's digest gossip from V3 (publisher V3, worker-batch
          topic, handler.rs:142-228) *)
  | Byz_cooperate
      (** the hidden author-branch is [Cooperate]: V3's worker really sealed
          and gossiped b (worker.rs:293-320) *)
  | Holds
      (** V1 holds a batch stored under key b (handle.rs:497-523 accept
          path) *)
  | Held_by_other
      (** some validator other than V1 really holds b's payload - the K
          operand [exists j != i: held_j(b)] *)
  | Referenced_in_dag
      (** a certificate whose header references b sits in V1's dag; false
          throughout this minimal abstraction (no DAG-reference path is
          modeled) - the guard is retained for faithfulness to the full
          formula, where vote-implies-availability would otherwise let V1
          infer a holder without holding b *)
  | At_done  (** terminal phase reached *)

(** Atom valuation over global states. *)
let label a s =
  match a with
  | Recv_digest -> s.recv
  | Byz_cooperate -> (
      match s.choice with
      | Cooperate -> true
      | Choice_unchosen | Forge_digest -> false)
  | Holds -> s.v1_stored
  | Held_by_other -> Bool.not (Vset.is_empty s.real_holders)
  | Referenced_in_dag -> s.dag_ref
  | At_done -> (
      match s.phase with
      | Done -> true
      | Gossip | Deliver -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Recv_digest -> "recv-digest(v1,b,pub=v3)"
  | Byz_cooperate -> "byz=cooperate"
  | Holds -> "holds(v1,b)"
  | Held_by_other -> "exists j!=v1: held(j,b)"
  | Referenced_in_dag -> "referenced-in-dag(v1,b)"
  | At_done -> "done"

(** The exact CTLK checker over this family's ordered state and view. *)
module Checker = System.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, the V1-only view, the atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
