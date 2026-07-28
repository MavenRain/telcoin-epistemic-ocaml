(** The round-[r] parent handoff from the certificate-manager task to the
    proposer task of ONE telcoin-network primary, abstracted as a finite
    interpreted system.

    {1 Mechanism}

    A primary runs the certificate manager and the proposer as two separate
    tokio tasks that share no memory; the only link between them is the
    bounded [parents] channel of the consensus bus
    (crates/consensus/primary/src/consensus_bus.rs:789 [parents :
    QueChannel<(Vec<Certificate>, Round)>], :899-900 sender, :979-980
    subscriber).

    - Aggregation. [CertificatesAggregator::append]
      (crates/consensus/primary/src/aggregators/certificates.rs:75-102)
      first refuses an origin it has already counted -
      [if !self.authorities_seen.insert(origin.clone()) { return None; }]
      (:83-85) - then pushes the certificate and adds the origin's voting
      power (:88-89). On [self.weight >= committee.quorum_threshold()] (:92)
      it returns [Some(self.certificates.drain(..).collect())] (:98) with the
      deliberate [// NOTE: do not reset the weight here // this method could
      be called again if the proposer doesn't advance the round] (:94-97):
      [weight] and [authorities_seen] survive, [certificates] does not.
    - Forwarding. [CertificatesAggregatorManager::append_certificate]
      (certificates.rs:24-44) forwards only a non-empty quorum batch:
      [if let Some(parents) = quorum { self.consensus_bus.parents().send((parents,
      round)).await?; }] (:39-41). It is called once per accepted certificate
      from [accept_verified_certificates]
      (crates/consensus/primary/src/state_sync/cert_manager.rs:205-211). It is
      ROUND-GENERIC: [let round = certificate.round();] (:29) selects the
      per-round aggregator (:32-36), so the very same [:39-41] send also
      carries a quorum batch for a FUTURE round [r' > r] on the SAME channel.
    - Consumption. The proposer receives on the same channel
      (crates/consensus/primary/src/proposer.rs:702-705) and dispatches on
      [round.cmp(&self.round)] (:393): [Ordering::Greater] ASSIGNS
      [self.last_parents = parents] and jumps [self.round = round] (:404-407);
      [Ordering::Less] IGNORES the batch (:427-436); [Ordering::Equal]
      EXTENDS, [self.last_parents.extend(parents);] (:447).
    - Proposal. [enough_parents = !self.last_parents.is_empty()] (:751) is a
      hard conjunct of [should_create_header] (:755-757); proposing does
      [self.round += 1] (:548) and [let parents = std::mem::take(&mut
      self.last_parents);] (:592), and the header keeps the parents as a SET,
      [parents.iter().map(|x| x.header().digest()).collect()] (:213) into
      [Header::new(.., parents: BTreeSet<HeaderDigest>, ..)]
      (crates/types/src/primary/header.rs:69-90, field at :74).
    - The second producer on the same channel.
      [CertValidator::forward_verified_certs]
      (crates/consensus/primary/src/state_sync/cert_validator.rs:133-158)
      sends [(vec![], minimal_round_for_parents)] with
      [minimal_round_for_parents = highest_received_round.saturating_sub(1)]
      (:157-158). It carries an EMPTY vector, so through the [Greater] arm it
      advances [self.round] and CLEARS [last_parents], and can never satisfy
      [enough_parents].
    - The THIRD writer of [last_parents], and the one this model was corrected
      to carry. Because the forward of :39-41 is round-generic, a quorum batch
      for a future round [r' > r] reaches a proposer still at [<= r] and takes
      the [Ordering::Greater] arm, which does [self.round = round;] (:404) and
      [self.last_parents = parents;] (:407) - a REPLACEMENT that drops every
      round-[r] certificate held so far, with NO header proposed and NO
      cert-validator notice involved. It is not gated on anything the proposer
      or the aggregator controls; it is a network condition. Modelled as
      {!step_future_batch}, and it is what makes the strong "the late
      certificate stays in [last_parents] until it is in the header" reading
      FALSE - see {!Parent_batch_forward_statements.s3} conjunct (2).

      The one thing that IS implied when such a batch fires is that the
      round-[r] aggregator has already counted 2f+1 distinct origins:
      [get_missing_parents] (cert_manager.rs:139-180) holds a certificate
      pending until every parent digest is in the certificate store (:157-166),
      the only write to that store on this path is [write_all] at
      cert_manager.rs:196, and every certificate it writes is handed to
      [append_certificate] in the same loop (:198-211). So a round-[r+1]
      certificate cannot be accepted before its 2f+1 round-[r] parents have
      each passed through the round-[r] aggregator. (The one bypass,
      [node_storage().write] at network/handler.rs:267, is on the
      [is_cvv_inactive] catch-up branch, i.e. a node that is not the active
      proposer this model is about.) {!step_future_batch} is therefore
      enabled only from {!Ea3}, and that is a consequence of the DAG parent
      rule, not a convenience.

    {1 Components}

    - [early]: how many of the three early origins (2f+1 = 3 of a 4-member
      committee, [Committee::calculate_quorum_threshold],
      crates/types/src/committee.rs:247) the aggregator has accepted for
      round [r]. The three are interchangeable for every statement here, so
      only their count is carried.
    - [latched]: [weight >= quorum_threshold] has been crossed and, per the
      NOTE at certificates.rs:94-97, is never un-crossed.
    - [straggler]: the fourth, late origin's round-[r] certificate has been
      accepted. It is the "slow but not silent" validator of the fairness
      statement.
    - [first] / [second]: the two batches the aggregator can emit for round
      [r] - one at the quorum crossing, one on the later distinct origin -
      each [Msg_unsent], [Msg_inflight] (queued on the [parents] channel) or
      [Msg_delivered]. Delivery is FIFO because the channel is.
    - [holds_early] / [holds_straggler] / [holds_dup]: the proposer's
      [last_parents] for round [r], as "the early certificates are in it",
      "the straggler's certificate is in it", and "some certificate is in it
      twice". A vector, not a set: proposer.rs:447 [extend]s.
    - [holds_future]: [last_parents] holds a FUTURE round's certificates,
      assigned by the [Greater] arm at proposer.rs:407 from a round-[r']
      quorum batch. It is disjoint from the three round-[r] flags because
      :407 assigns rather than extends. It matters because
      [enough_parents = !self.last_parents.is_empty()] (:751) does not look
      at rounds: a future round's parents satisfy it just as well, so
      [Proposer_holds_parents] must be true in these states or the model
      would be claiming an emptiness the code does not have.
    - [phase]: the proposer's [self.round] relative to [r] plus what put it
      there - [P_behind] ([self.round = r-1], so a round-[r] batch takes the
      [Greater] arm), [P_at_r] ([self.round = r], the [Equal] arm),
      [P_proposed] ([self.round = r+1] after proposer.rs:548 with a header
      out), [P_jumped] ([self.round > r] after the [Greater] arm took a
      future-round message - either the cert-validator's empty notice or a
      real future-round quorum batch - with no header).
    - [hdr]: the parent set of the header this node proposed for [r+1]. It is
      a SET (header.rs:74), which is the modelled repair path that hides a
      duplicated [last_parents] from the header itself.
    - [notice]: whether a future-round empty-parents notice from
      cert_validator.rs:158 is still due on this run.

    {1 Role mapping}

    CTLK knowledge is indistinguishability of a local state, and the two
    tasks of this primary have genuinely disjoint local state, so they are
    the two knowledge agents:

    - [Validator.V0] is the PROPOSER task. Its view is exactly its own
      [last_parents] (as the four booleans), its [self.round]/[proposed]
      status and its emitted header's parent set. It cannot see [early],
      [latched], [straggler], the channel, or the pending notice: nothing in
      proposer.rs reads the aggregator.
    - [Validator.V1] is the CERTIFICATE-MANAGER task. Its view is exactly the
      aggregator state it owns - [early], [latched], [straggler] - plus which
      of its two batches it has already handed to [parents().send]. It cannot
      see [last_parents], the proposer's round, or whether a sent batch was
      taken: [send] returns as soon as the queue accepts it.
    - [Validator.V2] .. [Validator.V9] are idle non-agents with the constant
      blank view and never appear under [K].

    Like the other isolated family models (validator.mli:8-11) this one keeps
    a module-local four-member roster - three early origins plus one late one,
    quorum 2f+1 = 3 - rather than the ten-member committee of {!Tn_model};
    [Validator.t] is used only to name the two knowledge agents.

    {1 Scope and disclosed omissions}

    - The run is one round [r] on one primary. Garbage collection
      (certificates.rs:47-49) and the [recover_state] startup replay
      (cert_manager.rs:244-257) are outside the window.
    - The first round-[r] batch is modelled as arriving while the proposer is
      still at [r-1], i.e. through the [Greater] ASSIGN arm (proposer.rs:407).
      A cert-validator notice for round [r] itself would instead put the
      proposer at [r] with an empty [last_parents] and route the first batch
      through the [Equal] EXTEND arm; the resulting [last_parents] is the
      same on the pristine model, so no statement here changes, while under
      {!No_equal_arm_extend} that variant would additionally starve the FIRST
      batch. Omitting it is therefore conservative: it can only weaken a
      mutation, never make a statement true that would otherwise be false.
    - The repropose path's [self.last_parents.clear()] (proposer.rs:576)
      fires only when the proposer store already holds a header for the round
      being proposed, i.e. across a restart, which is outside this one-round
      window. It is the FOURTH writer of [last_parents]; the other three -
      the [Greater] assign (:407), the [Equal] extend (:447) and the
      [std::mem::take] at proposal (:592) - are all inside the window and all
      modelled.
    - After {!step_future_batch} the proposer is at some round [r' > r] with
      that round's parents in hand and would go on to propose a header for
      [r'+1]. That proposal is outside this one-round window, so {!P_jumped}
      admits no {!step_propose}; {!hdr} means only "the header this node
      proposed for [r+1]". The omission removes continuations, so it can only
      weaken a claim, never manufacture one.
    - Under {!No_equivocation_guard} the model does not re-emit on the
      genuine origins that arrive after the Byzantine flood. That omission
      only removes refuting states, so it cannot rescue a statement.

    The CTLK checker over this family is the presheaf-topos denotation
    {!Denote.Make}, pinned to agree with {!System} at every reachable world by
    test/t_parent_batch_forward_topos.ml. *)

(** How many of the three early (quorum-forming) origins the round-[r]
    aggregator has accepted; [Ea3] is the 2f+1 crossing of
    certificates.rs:92. *)
type early = Ea0 | Ea1 | Ea2 | Ea3

(** Total order index for {!early}. *)
let early_index = function Ea0 -> 0 | Ea1 -> 1 | Ea2 -> 2 | Ea3 -> 3

(** Total order on {!early}. *)
let early_compare a b = Int.compare (early_index a) (early_index b)

(** The next acceptance step; [Ea3] is absorbing because
    [authorities_seen.insert] (certificates.rs:83-85) refuses a repeat
    origin, so a fourth EARLY append is not a transition at all. *)
let early_next = function Ea0 -> Ea1 | Ea1 -> Ea2 | Ea2 -> Ea3 | Ea3 -> Ea3

(** Whether 2f+1 DISTINCT early origins have been accepted. *)
let early_is_full = function Ea0 | Ea1 | Ea2 -> false | Ea3 -> true

(** The state of one emitted parent batch on the bounded [parents] channel
    (consensus_bus.rs:789): never handed to [send], queued, or consumed by
    the proposer's [rx_parents.recv()] (proposer.rs:702). *)
type msg = Msg_unsent | Msg_inflight | Msg_delivered

(** Total order index for {!msg}. *)
let msg_index = function Msg_unsent -> 0 | Msg_inflight -> 1 | Msg_delivered -> 2

(** Total order on {!msg}. *)
let msg_compare a b = Int.compare (msg_index a) (msg_index b)

(** Whether the certificate manager has already called [parents().send] for
    this batch - the only part of a batch's fate that the manager can see. *)
let msg_sent = function Msg_unsent -> false | Msg_inflight | Msg_delivered -> true

(** Whether the batch is queued on the channel and not yet processed. *)
let msg_is_inflight = function
  | Msg_inflight -> true
  | Msg_unsent | Msg_delivered -> false

(** The proposer's [self.round] relative to the parents' round [r], together
    with what put it there (proposer.rs:393-457, :548). *)
type phase =
  | P_behind  (** [self.round = r-1]: a round-[r] batch takes [Greater]. *)
  | P_at_r  (** [self.round = r]: a round-[r] batch takes [Equal]. *)
  | P_proposed  (** [self.round = r+1] after proposing a header for [r+1]. *)
  | P_jumped
      (** [self.round > r] after the [Greater] arm took a future-round
          message; no header was proposed. Two sources reach it: the
          cert-validator's empty notice (cert_validator.rs:157-158), which
          assigns an EMPTY [last_parents], and a real future-round quorum
          batch off certificates.rs:39-41, which assigns that round's
          parents. *)

(** Total order index for {!phase}. *)
let phase_index = function
  | P_behind -> 0
  | P_at_r -> 1
  | P_proposed -> 2
  | P_jumped -> 3

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** Whether the proposer can still take round-[r] parents, i.e. it is on the
    [Greater] or [Equal] side of proposer.rs:393. *)
let phase_collects = function
  | P_behind | P_at_r -> true
  | P_proposed | P_jumped -> false

(** The parent set of the header this node proposed for round [r+1]
    (proposer.rs:592 then :213 into the [BTreeSet] of header.rs:74). *)
type hdr =
  | Hdr_none  (** no header proposed yet in this window *)
  | Hdr_without_straggler  (** proposed with the early origins only *)
  | Hdr_with_straggler  (** proposed with the late origin included *)

(** Total order index for {!hdr}. *)
let hdr_index = function
  | Hdr_none -> 0
  | Hdr_without_straggler -> 1
  | Hdr_with_straggler -> 2

(** Total order on {!hdr}. *)
let hdr_compare a b = Int.compare (hdr_index a) (hdr_index b)

(** Whether a future-round empty-parents notice from cert_validator.rs:158 is
    still due on this run. [Notice_absent] is the in-sync run: no peer
    certificate two rounds ahead shows up inside this window. *)
type notice = Notice_absent | Notice_pending | Notice_consumed

(** Total order index for {!notice}. *)
let notice_index = function
  | Notice_absent -> 0
  | Notice_pending -> 1
  | Notice_consumed -> 2

(** Total order on {!notice}. *)
let notice_compare a b = Int.compare (notice_index a) (notice_index b)

(** The joint global state: aggregator, channel, proposer, environment. *)
type state = {
  early : early;  (** distinct early origins accepted for round [r] *)
  latched : bool;  (** [weight >= quorum_threshold] was crossed *)
  straggler : bool;  (** the late fourth origin was accepted *)
  first : msg;  (** the batch emitted at the quorum crossing *)
  second : msg;  (** the batch emitted on the later distinct origin *)
  holds_early : bool;  (** early certificates are in [last_parents] *)
  holds_straggler : bool;  (** the late certificate is in [last_parents] *)
  holds_dup : bool;  (** some certificate is in [last_parents] twice *)
  holds_future : bool;
      (** [last_parents] holds a FUTURE round's certificates, assigned by
          proposer.rs:407 *)
  phase : phase;  (** the proposer's round relative to [r] *)
  hdr : hdr;  (** the proposed header's parent set *)
  notice : notice;  (** the cert-validator's empty-parents notice *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = early_compare s1.early s2.early in
  if Bool.not (Int.equal c 0) then c
  else
    let c = Bool.compare s1.latched s2.latched in
    if Bool.not (Int.equal c 0) then c
    else
      let c = Bool.compare s1.straggler s2.straggler in
      if Bool.not (Int.equal c 0) then c
      else
        let c = msg_compare s1.first s2.first in
        if Bool.not (Int.equal c 0) then c
        else
          let c = msg_compare s1.second s2.second in
          if Bool.not (Int.equal c 0) then c
          else
            let c = Bool.compare s1.holds_early s2.holds_early in
            if Bool.not (Int.equal c 0) then c
            else
              let c = Bool.compare s1.holds_straggler s2.holds_straggler in
              if Bool.not (Int.equal c 0) then c
              else
                let c = Bool.compare s1.holds_dup s2.holds_dup in
                if Bool.not (Int.equal c 0) then c
                else
                  let c = Bool.compare s1.holds_future s2.holds_future in
                  if Bool.not (Int.equal c 0) then c
                  else
                    let c = phase_compare s1.phase s2.phase in
                    if Bool.not (Int.equal c 0) then c
                    else
                      let c = hdr_compare s1.hdr s2.hdr in
                      if Bool.not (Int.equal c 0) then c
                      else notice_compare s1.notice s2.notice

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A task's local view.

    [View_proposer] is exactly what proposer.rs keeps in [self]:
    [last_parents] as (early present, straggler present, a duplicate present,
    a future round's parents present), [self.round]/proposal status, and the
    parent set of the header it emitted. [View_manager] is exactly what the certificate manager keeps:
    the round-[r] aggregator's distinct origins, its latched weight, whether
    the late origin was accepted, and which of its two batches it has already
    pushed into [parents().send]. Neither projection mentions a field the
    other task owns, which is the whole epistemic content of this family. *)
type view =
  | View_proposer of bool * bool * bool * bool * phase * hdr
  | View_manager of early * bool * bool * bool * bool
  | View_idle  (** the constant blank view of the non-agents V2, V3 *)

(** Total order on the proposer view's payload. *)
let proposer_view_compare (he, hs, hd, hf, ph, hr) (he', hs', hd', hf', ph', hr')
    =
  let c = Bool.compare he he' in
  if Bool.not (Int.equal c 0) then c
  else
    let c = Bool.compare hs hs' in
    if Bool.not (Int.equal c 0) then c
    else
      let c = Bool.compare hd hd' in
      if Bool.not (Int.equal c 0) then c
      else
        let c = Bool.compare hf hf' in
        if Bool.not (Int.equal c 0) then c
        else
          let c = phase_compare ph ph' in
          if Bool.not (Int.equal c 0) then c else hdr_compare hr hr'

(** Total order on the certificate-manager view's payload. *)
let manager_view_compare (e, la, st, f, sd) (e', la', st', f', sd') =
  let c = early_compare e e' in
  if Bool.not (Int.equal c 0) then c
  else
    let c = Bool.compare la la' in
    if Bool.not (Int.equal c 0) then c
    else
      let c = Bool.compare st st' in
      if Bool.not (Int.equal c 0) then c
      else
        let c = Bool.compare f f' in
        if Bool.not (Int.equal c 0) then c else Bool.compare sd sd'

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, (View_manager _ | View_proposer _) -> -1
  | (View_manager _ | View_proposer _), View_idle -> 1
  | View_manager (e, la, st, f, sd), View_manager (e', la', st', f', sd') ->
      manager_view_compare (e, la, st, f, sd) (e', la', st', f', sd')
  | View_manager _, View_proposer _ -> -1
  | View_proposer _, View_manager _ -> 1
  | ( View_proposer (he, hs, hd, hf, ph, hr),
      View_proposer (he', hs', hd', hf', ph', hr') ) ->
      proposer_view_compare
        (he, hs, hd, hf, ph, hr)
        (he', hs', hd', hf', ph', hr')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 is the proposer task and V1 the certificate-manager
    task of the SAME primary; V2 .. V9 are idle non-agents with the constant
    blank view and never appear under [K]. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_proposer
        ( s.holds_early,
          s.holds_straggler,
          s.holds_dup,
          s.holds_future,
          s.phase,
          s.hdr )
  | Validator.V1 ->
      View_manager
        (s.early, s.latched, s.straggler, msg_sent s.first, msg_sent s.second)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletions for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_drain
      (** delete the [.drain(..)] at
          crates/consensus/primary/src/aggregators/certificates.rs:98, i.e.
          return [Some(self.certificates.clone())]. The buffer then survives
          its own emission, so the SECOND emission for round [r] - the one the
          latched weight of :92-97 makes normal, not exceptional - re-carries
          the early certificates the proposer already holds, and the [Equal]
          arm's [extend] (proposer.rs:447) puts them into [last_parents] a
          second time: this adds the [holds_dup] transition.

          Sibling hunt: the header is repaired and this model SAYS SO -
          [Header::new] takes [parents: BTreeSet<HeaderDigest>]
          (crates/types/src/primary/header.rs:69-90, field :74) filled by
          [parents.iter().map(..).collect()] (proposer.rs:213), so {!hdr}
          here is a set and a duplicated hold is invisible in the header. The
          claim is therefore anchored on [last_parents] itself, which is NOT
          repaired: [enough_votes] iterates [for certificate in
          &self.last_parents] and adds [voting_power_by_id(certificate.origin())]
          with no de-duplication (proposer.rs:351-358) before testing
          [votes_for_leader >= validity_threshold() || no_votes >=
          quorum_threshold()] (:363-364), so one origin's stake can be counted
          twice into the f+1 leader test that sets [self.advance_round]
          (:463). [std::mem::take] (:592) empties the vector only at proposal
          time and cannot undo a double count that already happened. *)
  | No_parents_forward
      (** delete the forward at
          crates/consensus/primary/src/aggregators/certificates.rs:39-41
          ([if let Some(parents) = quorum { self.consensus_bus.parents().send((parents,
          round)).await?; }]). No batch is ever queued, so [last_parents] is
          never made non-empty and [enough_parents] (proposer.rs:751) never
          admits a proposal.

          Because :39-41 is round-generic (:29, :32-36), this deletion also
          removes {!step_future_batch}: the future-round quorum batch that
          otherwise replaces [last_parents] rides the very same send.

          Sibling hunt: [parents().send] has exactly two non-test call sites
          in the crate - this one and
          crates/consensus/primary/src/state_sync/cert_validator.rs:158,
          which sends [(vec![], minimal_round_for_parents)]. That producer
          SURVIVES this deletion and is modelled here as {!Notice_pending}:
          it still advances the proposer's round through the [Greater] arm
          (proposer.rs:404-407), so the node is not frozen, but the arm
          ASSIGNS the empty vector into [last_parents], so it can never
          repair the conclusion. [recover_state] (cert_manager.rs:244-257)
          reaches the proposer only through this same deleted forward, and
          [new_certificates()] (cert_manager.rs:214) feeds the Bullshark DAG,
          not the proposer. *)
  | No_equal_arm_extend
      (** delete [self.last_parents.extend(parents);] at
          crates/consensus/primary/src/proposer.rs:447, leaving the [Equal]
          arm to reset only the min-delay interval (:452-455). The batch the
          latched aggregator emits for the late fourth origin then reaches a
          proposer already at round [r] and is discarded, so the late origin
          is excluded from the header the node goes on to propose.

          Sibling hunt: the [Greater] arm (proposer.rs:394-426) ASSIGNS
          rather than extends (:407) and has already fired for the first
          batch, so it cannot re-admit a same-round batch; [Ordering::Less]
          (:427-436) ignores; the proposer hands [Header::new] only
          [std::mem::take(&mut self.last_parents)] (:592) with no store
          re-scan at proposal time, and [Header::new] reads only its
          [parents] argument (header.rs:69-90); [recover_state]
          (cert_manager.rs:244-257) runs at startup only. Nothing re-derives
          a parent that never entered [last_parents]. *)
  | No_equivocation_guard
      (** delete the equivocation guard
          [if !self.authorities_seen.insert(origin.clone()) { return None; }]
          at crates/consensus/primary/src/aggregators/certificates.rs:83-85.
          A single Byzantine origin's repeated round-[r] certificates are then
          each pushed and each add [voting_power_by_id(&origin)] (:88-89), so
          [self.weight >= committee.quorum_threshold()] (:92) is crossed by
          ONE origin and a sub-quorum batch is forwarded to the proposer. The
          model adds exactly one transition for this, from one accepted early
          origin straight to [latched] with the first batch queued.

          Sibling hunt: nothing upstream stops it.
          [process_verified_certificates] (cert_manager.rs:88-125) checks
          signature verification, pending status and missing parents, none of
          which is per-origin-per-round; [accept_verified_certificates]
          (cert_manager.rs:196-217) writes to storage by digest and calls
          [append_certificate] (:205-211) BEFORE forwarding to consensus
          (:214). The one real detector,
          [ConsensusError::CertificateEquivocation]
          (crates/consensus/primary/src/consensus/state.rs:145-157), lives on
          the [new_certificates] consumer and therefore fires strictly after
          the aggregator has already counted the certificate and possibly
          already emitted; it cannot retract a batch from the [parents]
          channel or from [last_parents]. *)

(** Whether this mutation still performs the [parents().send] of
    certificates.rs:39-41. *)
let forwards = function
  | Pristine | No_drain | No_equal_arm_extend | No_equivocation_guard -> true
  | No_parents_forward -> false

(** Accept one more distinct EARLY origin (certificates.rs:83-89). Crossing
    2f+1 latches the weight for good (:92-97) and emits the first batch. *)
let step_accept_early mut s =
  if early_is_full s.early then []
  else
    let e = early_next s.early in
    let crosses = early_is_full e in
    let newly_latched = Bool.not s.latched && crosses in
    [
      {
        s with
        early = e;
        latched = s.latched || crosses;
        first = (if newly_latched && forwards mut then Msg_inflight else s.first);
      };
    ]

(** The Byzantine flood that only {!No_equivocation_guard} makes possible: one
    origin's repeated certificates carry the weight to quorum on their own,
    so a batch is forwarded with a single distinct origin behind it. *)
let step_byzantine_flood mut s =
  match mut with
  | No_equivocation_guard ->
      let at_one =
        match s.early with Ea1 -> true | Ea0 | Ea2 | Ea3 -> false
      in
      if at_one && Bool.not s.latched then
        [ { s with latched = true; first = Msg_inflight } ]
      else []
  | Pristine | No_drain | No_parents_forward | No_equal_arm_extend -> []

(** Accept the late fourth origin. The weight is still latched
    (certificates.rs:94-97), so :92 fires again immediately and a second
    batch is emitted for the same round. *)
let step_accept_straggler mut s =
  if s.latched && Bool.not s.straggler && early_is_full s.early then
    [
      {
        s with
        straggler = true;
        second = (if forwards mut then Msg_inflight else s.second);
      };
    ]
  else []

(** Apply a delivered round-[r] batch to the proposer, dispatching on
    [round.cmp(&self.round)] exactly as proposer.rs:393-457 does. *)
let apply_batch mut ~carries_early ~carries_straggler s =
  match s.phase with
  | P_behind ->
      (* Ordering::Greater, proposer.rs:404-407: jump the round and ASSIGN.
         The assign at :407 replaces whatever was there, so any future-round
         parents would go too. *)
      {
        s with
        phase = P_at_r;
        holds_early = carries_early;
        holds_straggler = carries_straggler;
        holds_dup = false;
        holds_future = false;
      }
  | P_at_r -> (
      (* Ordering::Equal, proposer.rs:437-456: EXTEND at :447. *)
      match mut with
      | No_equal_arm_extend -> s
      | Pristine | No_drain | No_parents_forward | No_equivocation_guard ->
          {
            s with
            holds_dup =
              s.holds_dup
              || (carries_early && s.holds_early)
              || (carries_straggler && s.holds_straggler);
            holds_early = s.holds_early || carries_early;
            holds_straggler = s.holds_straggler || carries_straggler;
          })
  | P_proposed | P_jumped ->
      (* Ordering::Less, proposer.rs:427-436: older parents are ignored. *)
      s

(** Deliver the quorum-crossing batch. It carries the aggregator's buffered
    early certificates. *)
let step_deliver_first mut s =
  match s.first with
  | Msg_inflight ->
      [
        {
          (apply_batch mut ~carries_early:true ~carries_straggler:false s) with
          first = Msg_delivered;
        };
      ]
  | Msg_unsent | Msg_delivered -> []

(** Deliver the late origin's batch, behind the first one because the
    [parents] channel is FIFO. Under {!No_drain} it still carries the early
    certificates too, because the buffer was cloned rather than drained. *)
let step_deliver_second mut s =
  match s.second with
  | Msg_inflight -> (
      match s.first with
      | Msg_inflight -> []
      | Msg_unsent | Msg_delivered ->
          let carries_early =
            match mut with
            | No_drain -> true
            | Pristine | No_parents_forward | No_equal_arm_extend
            | No_equivocation_guard ->
                false
          in
          [
            {
              (apply_batch mut ~carries_early ~carries_straggler:true s) with
              second = Msg_delivered;
            };
          ])
  | Msg_unsent | Msg_delivered -> []

(** Propose the next header. [enough_parents] (proposer.rs:751) is the hard
    conjunct of :755-757 and the max-delay disjunct eventually admits the
    proposal; :548 advances the round and :592 takes the parents, which
    proposer.rs:213 collapses into the header's [BTreeSet]. *)
let step_propose s =
  match s.phase with
  | P_at_r ->
      if s.holds_early || s.holds_straggler then
        [
          {
            s with
            phase = P_proposed;
            hdr =
              (if s.holds_straggler then Hdr_with_straggler
               else Hdr_without_straggler);
            holds_early = false;
            holds_straggler = false;
            holds_dup = false;
            holds_future = false;
          };
        ]
      else []
  | P_behind | P_proposed | P_jumped -> []

(** Consume the cert-validator's empty-parents notice for a future round
    (cert_validator.rs:157-158). The [Greater] arm jumps [self.round] and
    ASSIGNS the empty vector (proposer.rs:404-407), so any round-[r] parents
    held so far are lost and every later round-[r] batch takes [Less]. *)
let step_catchup_jump s =
  match s.notice with
  | Notice_pending -> (
      match s.phase with
      | P_behind | P_at_r ->
          [
            {
              s with
              notice = Notice_consumed;
              phase = P_jumped;
              holds_early = false;
              holds_straggler = false;
              holds_dup = false;
              holds_future = false;
            };
          ]
      | P_proposed | P_jumped -> [])
  | Notice_absent | Notice_consumed -> []

(** Consume a NON-EMPTY quorum batch for a future round [r' > r], forwarded by
    the same round-generic send at
    crates/consensus/primary/src/aggregators/certificates.rs:39-41 that
    forwards the round-[r] batch ([round] there is [certificate.round()], :29,
    and the aggregator is looked up per round, :32-36). The proposer's
    [Ordering::Greater] arm then does [self.round = round;] (proposer.rs:404)
    and [self.last_parents = parents;] (:407), REPLACING [last_parents]: every
    round-[r] certificate held so far, straggler included, is dropped, no
    header is proposed, and no cert-validator notice is involved.

    This is the path {!step_catchup_jump} does NOT cover.
    {!step_catchup_jump} is hard-gated on {!Notice_pending} because
    cert_validator.rs:157-158 sends [(vec![], highest_received_round - 1)];
    this one has no such gate, because nothing in either task controls when a
    peer quorum for a later round shows up. Modelling only the notice path is
    what made the strong persistence reading of
    {!Parent_batch_forward_statements.s3} look true.

    Enabling conditions, each of them a fact about the Rust and not a
    convenience for a statement:

    - [forwards mut]. The batch rides the SAME [:39-41] send as the round-[r]
      batch, so {!No_parents_forward} deletes this path too. Only
      cert_validator.rs:158 survives that deletion, and it carries [vec![]].
    - [phase_collects s.phase]. [Ordering::Greater] fires only while
      [self.round <= r] (proposer.rs:393); past that the batch is either
      [Equal] or [Less].
    - [early_is_full s.early]. A round-[r+1] certificate is held pending
      until every parent digest is in the certificate store
      ([get_missing_parents], cert_manager.rs:139-180, storage test at
      :157-166), the only write to that store on the active-CVV path is
      [write_all] at cert_manager.rs:196, and the same loop hands every
      written certificate to [append_certificate] (:198-211). So the 2f+1
      distinct round-[r] parents have already been counted by the round-[r]
      aggregator before any round-[r+1] quorum can form here.

    The proposer is left holding the FUTURE round's parents, so
    [enough_parents = !self.last_parents.is_empty()] (proposer.rs:751) is
    still satisfied - the node is not starved, it has simply stopped
    collecting for [r]. *)
let step_future_batch mut s =
  if forwards mut && phase_collects s.phase && early_is_full s.early then
    [
      {
        s with
        phase = P_jumped;
        holds_early = false;
        holds_straggler = false;
        holds_dup = false;
        holds_future = true;
      };
    ]
  else []

(** The transition relation: one task event per step. *)
let next_with mut s =
  List.concat
    [
      step_accept_early mut s;
      step_byzantine_flood mut s;
      step_accept_straggler mut s;
      step_deliver_first mut s;
      step_deliver_second mut s;
      step_propose s;
      step_catchup_jump s;
      step_future_batch mut s;
    ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The in-sync run: nothing has been accepted for round [r] yet, the
    proposer is still at [r-1], and no future-round certificate shows up
    inside the window, so cert_validator.rs:158 never preempts it. *)
let initial =
  {
    early = Ea0;
    latched = false;
    straggler = false;
    first = Msg_unsent;
    second = Msg_unsent;
    holds_early = false;
    holds_straggler = false;
    holds_dup = false;
    holds_future = false;
    phase = P_behind;
    hdr = Hdr_none;
    notice = Notice_absent;
  }

(** The lagging run: identical, except that a peer certificate two rounds
    ahead is going to make cert_validator.rs:157-158 send an empty batch for
    round [r+1], which the [Greater] arm will use to jump the proposer past
    [r] and clear its parents. *)
let initial_catchup = { initial with notice = Notice_pending }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Quorum_of_distinct_origins
      (** the round-[r] aggregator has accepted 2f+1 DISTINCT origins *)
  | Aggregator_latched  (** [weight >= quorum_threshold] was crossed *)
  | Straggler_accepted  (** the late fourth origin's certificate was accepted *)
  | Batch_in_flight  (** a batch is queued on the [parents] channel *)
  | Proposer_holds_parents  (** [!self.last_parents.is_empty()] *)
  | Proposer_holds_straggler  (** the late certificate is in [last_parents] *)
  | Proposer_holds_future_round_parents
      (** [last_parents] was REPLACED by a future round's quorum batch
          through the [Greater] assign of proposer.rs:407 *)
  | Duplicate_in_last_parents  (** some certificate is in [last_parents] twice *)
  | Proposer_can_still_collect
      (** the proposer's round is [<= r], so a round-[r] batch is not ignored *)
  | Proposer_at_round_r  (** the proposer's round is exactly [r] *)
  | Header_proposed  (** a header for round [r+1] was proposed *)
  | Header_carries_straggler
      (** that header's parent set contains the late origin's certificate *)
  | Catchup_notice_pending
      (** a future-round empty-parents notice is still due on this run *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Quorum_of_distinct_origins -> early_is_full s.early
  | Aggregator_latched -> s.latched
  | Straggler_accepted -> s.straggler
  | Batch_in_flight -> msg_is_inflight s.first || msg_is_inflight s.second
  | Proposer_holds_parents ->
      s.holds_early || s.holds_straggler || s.holds_future
  | Proposer_holds_straggler -> s.holds_straggler
  | Proposer_holds_future_round_parents -> s.holds_future
  | Duplicate_in_last_parents -> s.holds_dup
  | Proposer_can_still_collect -> phase_collects s.phase
  | Proposer_at_round_r -> (
      match s.phase with
      | P_at_r -> true
      | P_behind | P_proposed | P_jumped -> false)
  | Header_proposed -> (
      match s.phase with
      | P_proposed -> true
      | P_behind | P_at_r | P_jumped -> false)
  | Header_carries_straggler -> (
      match s.hdr with
      | Hdr_with_straggler -> true
      | Hdr_none | Hdr_without_straggler -> false)
  | Catchup_notice_pending -> (
      match s.notice with
      | Notice_pending -> true
      | Notice_absent | Notice_consumed -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Quorum_of_distinct_origins -> "quorum_of_distinct_origins(r)"
  | Aggregator_latched -> "aggregator_latched(r)"
  | Straggler_accepted -> "straggler_accepted(r)"
  | Batch_in_flight -> "batch_in_flight"
  | Proposer_holds_parents -> "proposer_holds_parents(r)"
  | Proposer_holds_straggler -> "proposer_holds_straggler(r)"
  | Proposer_holds_future_round_parents -> "proposer_holds_future_round_parents"
  | Duplicate_in_last_parents -> "duplicate_in_last_parents"
  | Proposer_can_still_collect -> "proposer_can_still_collect(r)"
  | Proposer_at_round_r -> "proposer_at_round(r)"
  | Header_proposed -> "header_proposed(r+1)"
  | Header_carries_straggler -> "header_carries_straggler(r+1)"
  | Catchup_notice_pending -> "catchup_notice_pending"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation, pinned to agree with {!System} by
    test/t_parent_batch_forward_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation; both initial states are the same
    aggregator/proposer configuration and differ only in whether the
    cert-validator's future-round notice lands inside the window. *)
let spec_of mut =
  {
    Checker.init = [ initial; initial_catchup ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
