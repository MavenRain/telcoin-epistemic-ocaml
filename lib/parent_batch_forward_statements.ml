(** The parent-batch-forward statement family over the
    {!Parent_batch_forward_model} interpreted system: the aggregator-to-proposer
    handoff of round-[r] parent certificates inside one telcoin-network
    primary. Mined from telcoin-network, re-verified against the working tree
    at git HEAD 0c59c15b, and stated in the form that survived the grounding
    and encodability skeptics. File citations refer to
    Telcoin-Association/telcoin-network.

    {1 Reading guide for the K operands}

    The two knowledge agents are the two tokio tasks of ONE primary, which
    share no memory and communicate only over the bounded [parents] channel
    (consensus_bus.rs:789). So each [K] operand below is a fact owned by the
    OTHER task, never a projection of the knower's own view:

    - [K (V0, quorum_of_distinct_origins(r))] in S2. V0 is the proposer task;
      its view is [last_parents], its round and its emitted header
      (proposer.rs:751, :548, :592). The operand is [authorities_seen.len() >=
      2f+1] inside [CertificatesAggregator] (certificates.rs:62, :83-85, :92),
      a field of the certificate-manager task that the proposer never reads.
      It is not rigid either: it is false at both initial states and at every
      state before the quorum crossing. What makes the knowledge SOUND is
      that a non-empty round-[r] batch can only come from certificates.rs:39-41,
      which fires only under :92 after the per-origin dedup at :83-85 - the
      only other producer on the channel, cert_validator.rs:157-158, sends an
      EMPTY vector. The proposer's [enough_parents] test (proposer.rs:751) is
      a quorum proxy purely because of that.
    - [~K (V1, proposer_holds_parents(r))] and [~K (V1,
      ~proposer_holds_parents(r))] in S1. V1 is the certificate-manager task.
      [parents().send] returns when the queue accepts the batch, so the
      manager never learns whether the proposer took it, ignored it through
      [Ordering::Less] (proposer.rs:427-436), or had it wiped by a
      future-round jump (:404-407). That two-sided ignorance is the literal
      justification of the NOTE at certificates.rs:94-97 - "this method could
      be called again if the proposer doesn't advance the round" - which is
      why the weight is never reset.
    - [~K (V0, straggler_accepted(r))] and [~K (V0, ~straggler_accepted(r))]
      in S3. At the moment the proposer holds the quorum trio it cannot tell
      a slow fourth validator from a silent one: [straggler] lives in the
      aggregator. The mechanism deliberately does not force it to decide -
      it accepts the late origin instead of freezing round-[r] membership at
      the quorum instant.

    No [K] mentions V2 .. V9: they are idle non-agents with the constant
    blank view. *)

open Parent_batch_forward_model

(** A statement over this family's atom vocabulary; [bucket] reuses the
    shared vocabulary of the frozen {!Statements} module, and [antecedent] is
    the reachability witness [prove_nonvacuous] demands, so no statement is
    certified on the strength of an antecedent that holds nowhere. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - parent-batch-drain-keeps-last-parents-duplicate-free [safety]. Two
    conjuncts about the emission side of the handoff.

    (1) Drain-once: [AG(~duplicate_in_last_parents)]. Reaching quorum hands
    the buffered certificates to the proposer by DRAINING them -
    [return Some(self.certificates.drain(..).collect());]
    (crates/consensus/primary/src/aggregators/certificates.rs:98) - so no
    certificate is delivered into the proposer's [last_parents] twice for one
    round, even though the aggregator deliberately does NOT reset its weight
    (the NOTE at :94-97) and therefore emits AGAIN on every later distinct
    origin, and even though the proposer accumulates same-round batches with
    [self.last_parents.extend(parents);] (proposer.rs:447) rather than
    replacing them. Repeated emission for one round is the normal case here,
    which is exactly what makes drain-once load-bearing.

    (2) Send-side ignorance: [AG(batch_in_flight -> ~K_V1(proposer_holds_parents)
    /\ ~K_V1(~proposer_holds_parents))]. While a batch is queued the
    certificate-manager task cannot tell whether the proposer will hold it:
    [self.consensus_bus.parents().send((parents, round)).await?]
    (certificates.rs:40) completes on acceptance by the queue
    (consensus_bus.rs:899-900), and the proposer may take it ([Equal],
    proposer.rs:447), ignore it ([Less], :427-436) or have it overwritten by
    a future-round jump ([Greater] assign, :404-407). The witness pair is
    concrete: after the first emission, the state where the proposer has
    already extended and the state where it has not are view-identical to
    V1, whose projection stops at (early origins, latched, straggler, which
    batches were sent).

    Mutation pin: {!Parent_batch_forward_model.No_drain} replaces the
    [.drain(..)] of certificates.rs:98 with a clone, so the buffer survives
    its own emission and the second round-[r] batch re-carries the early
    certificates; the [Equal] arm's [extend] then puts them into
    [last_parents] a second time and conjunct (1) fails. No sibling repairs
    it where the claim is anchored: the HEADER is repaired - [Header::new]
    takes [parents: BTreeSet<HeaderDigest>] (types/src/primary/header.rs:74)
    filled by [parents.iter().map(..).collect()] (proposer.rs:213), and this
    model carries that set as {!Parent_batch_forward_model.hdr} - but
    [enough_votes] reads the VECTOR, adding
    [voting_power_by_id(certificate.origin())] once per element
    (proposer.rs:351-358) into the f+1 leader test at :363-364 that sets
    [self.advance_round] (:463), with no de-duplication anywhere. *)
let s1 =
  let holds = atom Proposer_holds_parents in
  let drain_once = Formula.Ag (Formula.Not (atom Duplicate_in_last_parents)) in
  let send_side_ignorance =
    Formula.Ag
      (Formula.Implies
         ( atom Batch_in_flight,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, holds)),
               Formula.Not (Formula.K (Validator.V1, Formula.Not holds)) ) ))
  in
  {
    name = "parent-batch-drain-keeps-last-parents-duplicate-free";
    bucket = Statements.Safety;
    formula = Formula.And (drain_once, send_side_ignorance);
    antecedent = Formula.And (holds, atom Straggler_accepted);
  }

(** S2 - quorum-forward-gives-proposer-trustworthy-parents [liveness]. Two
    conjuncts about the delivery side of the handoff.

    (1) Inevitable non-empty parents (leads-to): once the round-[r]
    aggregator has latched 2f+1 (certificates.rs:92-97), the proposer is
    still on the [<= r] side of [round.cmp(&self.round)] (proposer.rs:393)
    and no future-round notice is due, the certificates INEVITABLY land as a
    NON-EMPTY [last_parents] - the only thing that can satisfy
    [let enough_parents = !self.last_parents.is_empty();] (proposer.rs:751)
    inside [should_create_header] (:755-757). Non-emptiness is the whole
    point: the other producer on the very same channel,
    [self.consensus_bus.parents().send((vec![], minimal_round_for_parents)).await?]
    (state_sync/cert_validator.rs:157-158), advances the round through the
    [Greater] arm but ASSIGNS an empty vector (:407) and can never unblock a
    proposal. The guard [~catchup_notice_pending] is honest rather than
    cosmetic: that empty-vector producer is modelled, and when it IS due it
    can jump the proposer past [r] and wipe the round-[r] parents, so the
    unguarded claim would be false.

    Read this conjunct as what it says - [enough_parents] becomes true, the
    node is not starved - and NOT as "the round-[r] certificates specifically
    land". The two are no longer the same, because
    {!Parent_batch_forward_model.step_future_batch} gives a second way for
    [!self.last_parents.is_empty()] to become true: a quorum batch for a round
    [r' > r] taken through the [Greater] ASSIGN (proposer.rs:404-407) leaves
    the proposer holding THAT round's parents instead. The round-specific
    reading [leads_to(operative, holds_early \/ holds_straggler)] is FALSE for
    exactly that reason and is not claimed here. The conjunct as stated is
    still pinned, because the future-round batch rides the same
    certificates.rs:39-41 send and dies with it under
    {!Parent_batch_forward_model.No_parents_forward}.

    (2) Quorum knowledge (invariant): [AG(proposer_holds_parents ->
    K_V0(quorum_of_distinct_origins))]. Whenever [last_parents] is non-empty
    for round [r], the proposer KNOWS that 2f+1 distinct origins were
    accepted by the certificate-manager task - a fact of the other task's
    local state it never reads. It is sound because
    [if !self.authorities_seen.insert(origin.clone()) { return None; }]
    (certificates.rs:83-85) makes the counted origins distinct, the batch is
    emitted only under [self.weight >= committee.quorum_threshold()] (:92),
    and only such a batch is forwarded (:39-41). It is non-degenerate: the
    operand is false at both initial states and at every pre-quorum state,
    and V0's view class at the operative state contains at least the state
    where the straggler has already been accepted with a second batch in
    flight and the state where it has not - V0 sees neither.

    Mutation pins. {!Parent_batch_forward_model.No_parents_forward} deletes
    certificates.rs:39-41, the only route by which a certificate becomes a
    parent, so conjunct (1) fails: the node still latches, still drains, and
    - through the surviving cert_validator.rs:158 producer - still advances
    its round, but [last_parents] stays empty forever. This is a gate
    deletion and not the removal of the model's only transition, which is why
    it is not manufactured liveness.
    {!Parent_batch_forward_model.No_equivocation_guard} deletes the
    per-origin guard at certificates.rs:83-85, so one Byzantine origin's
    repeated certificates carry [self.weight] to quorum by themselves (:88-89
    adds the stake each time) and a batch backed by ONE origin is forwarded;
    the proposer then holds parents in a state where
    [quorum_of_distinct_origins] is false, and conjunct (2) fails at that
    very state. The only equivocation detector in the crate,
    [ConsensusError::CertificateEquivocation] (consensus/state.rs:145-157),
    is downstream on the [new_certificates] consumer, which
    [accept_verified_certificates] feeds only AFTER [append_certificate]
    (cert_manager.rs:205-216), so it cannot retract the forwarded batch. *)
let s2 =
  let operative =
    Formula.conj
      [
        atom Aggregator_latched;
        atom Proposer_can_still_collect;
        Formula.Not (atom Catchup_notice_pending);
      ]
  in
  let inevitable_parents =
    Formula.leads_to operative (atom Proposer_holds_parents)
  in
  let quorum_knowledge =
    Formula.Ag
      (Formula.Implies
         ( atom Proposer_holds_parents,
           Formula.K (Validator.V0, atom Quorum_of_distinct_origins) ))
  in
  {
    name = "quorum-forward-gives-proposer-trustworthy-parents";
    bucket = Statements.Liveness;
    formula = Formula.And (inevitable_parents, quorum_knowledge);
    antecedent = operative;
  }

(** S3 - late-origin-admissible-and-evicted-only-by-a-future-round-jump
    [fairness]. Three conjuncts about the late fourth origin. The bucket stays
    [fairness]: conjunct (1), the admissibility claim that there is no
    first-come-only quorum window at the parent layer, is the fairness content
    and it survives untouched. Conjunct (2) is the one that was corrected;
    what it lost is an over-strong persistence reading, not the fairness
    subject matter.

    (1) Admissibility: [AG((straggler_accepted /\ proposer_can_still_collect
    /\ ~catchup_notice_pending) -> EF(header_proposed /\
    header_carries_straggler))]. A certificate that arrives AFTER round [r]'s
    quorum has already fired is neither dropped nor held back. Because the
    aggregator keeps its weight latched (certificates.rs:94-97), the very
    next distinct origin re-satisfies :92 and triggers another emission, and
    the proposer merges it with [self.last_parents.extend(parents);]
    (proposer.rs:447) rather than replacing. So a validator that is merely
    slow still has a continuation in which its round-[r] certificate reaches
    the next header's parent set - there is no first-come-only quorum window
    at the parent layer. The claim is existential on purpose: [should_create_header]
    (proposer.rs:755-757) can fire on [max_delay_timed_out] before the second
    batch is delivered, so an inevitability claim here would be false, and
    order confers no advantage once the certificate is in, since the header's
    parents are a digest-ordered [BTreeSet] (header.rs:74) bounded only by
    [committee.size()] (:109-112). The [~catchup_notice_pending] guard is
    redundant for THIS conjunct on the present model - an [EF] survives a
    postponable jump, and the same is true of the future-round batch of
    {!Parent_batch_forward_model.step_future_batch} - and is kept anyway,
    because under the fair reading in which a notice already queued on the
    [parents] channel must eventually be received (proposer.rs:702), those
    runs end past round [r] and the claim should not lean on postponing them.
    Conjunct (2) below no longer needs the guard at all; see its exit
    disjunct.

    (2) Bounded persistence (weak until). The strong reading -
    [A[proposer_holds_straggler W (header_proposed /\ header_carries_straggler)]],
    "once it is in [last_parents] it stays there until it is in the header" -
    is FALSE, and this family used to assert it on the strength of a model
    that omitted a path the code has. The omitted path: the forward at
    aggregators/certificates.rs:39-41 is round-generic ([round] is
    [certificate.round()], :29; the aggregator is per round, :32-36) and
    [accept_verified_certificates] calls it for every accepted certificate
    (state_sync/cert_manager.rs:205-211), so a quorum batch for a FUTURE round
    [r' > r] arrives on the same [parents] channel, takes
    [Ordering::Greater], and executes [self.round = round;] (proposer.rs:404)
    and [self.last_parents = parents;] (:407). That assignment is a THIRD
    writer of [last_parents] and it REPLACES the vector, dropping the late
    certificate with no header proposed and no cert-validator notice
    involved. It is ungated: nothing in either task decides when a peer
    quorum for a later round shows up. {!Parent_batch_forward_model.step_future_batch}
    now carries it, and test/t_parent_batch_forward.ml asserts the strong
    reading is refuted on the pristine model, so the weakening cannot rot back
    into an unearned claim.

    The claim that does hold is the same weak until with the exits named
    honestly:
    [A[proposer_holds_straggler W ((header_proposed /\ header_carries_straggler)
    \/ (~proposer_can_still_collect /\ ~header_proposed))]],
    encoded with the kernel identity as [~E[~q U (~p /\ ~q)]]. In words: once
    the late certificate is in [last_parents], the ONLY two ways it leaves are
    into the header of the round-[r+1] proposal, or by the proposer being
    carried past round [r] with no proposal at all. It is not weakened into
    triviality - it still rules out the eviction that would be the actual
    unfairness, namely the proposer emitting a header for [r+1] that omits a
    certificate it was holding. [std::mem::take] at proposal time
    (proposer.rs:592) hands the whole vector to [Header::new], so a held
    straggler is in that header by construction; the [Equal] arm only
    [extend]s (:447); and the restart-only [clear()] on the repropose path
    (:576) is outside this one-round window. The guard on
    [~catchup_notice_pending] the old conjunct needed is now GONE: the exit
    disjunct covers the notice jump and the future-round batch alike, so the
    claim no longer leans on the notice being absent.

    (3) Straggler ignorance: [AG((proposer_holds_parents /\
    ~proposer_holds_straggler /\ proposer_at_round_r) -> ~K_V0(straggler_accepted)
    /\ ~K_V0(~straggler_accepted))]. Holding the quorum trio, the proposer
    can distinguish neither "the fourth validator is slow" from "the fourth
    validator is silent": [straggler] is a field of the aggregator. The
    witness pair is the state where the aggregator has already accepted the
    late origin with its second batch still queued and the state where it has
    not - view-identical to V0.

    Mutation pin: {!Parent_batch_forward_model.No_equal_arm_extend} deletes
    [self.last_parents.extend(parents);] at proposer.rs:447. The node keeps
    the trio it took through the [Greater] ASSIGN (:407), proposes a
    perfectly valid quorum header, and permanently excludes the late origin -
    starvation with no visible failure - so conjunct (1) fails while its
    antecedent stays reachable (the aggregator still accepts the straggler
    and still emits). This is a genuine refutation, not an antecedent that
    evaporated. No sibling repairs it: [Greater] ASSIGNS rather than extends
    and has already fired, [Less] ignores (:427-436), [Header::new] reads
    only its [parents] argument (header.rs:69-90) and the proposer passes it
    only [std::mem::take(&mut self.last_parents)] (:592) with no store
    re-scan, and [recover_state] (cert_manager.rs:244-257) runs at startup
    only. A second unrepaired consequence: [update_leader] searches
    [self.last_parents] for the round leader's certificate
    (proposer.rs:319-327), so a LATE leader certificate can then never set
    [self.last_leader]. *)
let s3 =
  let in_header =
    Formula.And (atom Header_proposed, atom Header_carries_straggler)
  in
  let admissible =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [
               atom Straggler_accepted;
               atom Proposer_can_still_collect;
               Formula.Not (atom Catchup_notice_pending);
             ],
           Formula.Ef in_header ))
  in
  let persists =
    (* The two honest exits: into the header, or past round [r] with no
       header at all (the cert-validator notice and the future-round quorum
       batch of proposer.rs:404-407 both land here). *)
    let exits =
      Formula.Or
        ( in_header,
          Formula.And
            ( Formula.Not (atom Proposer_can_still_collect),
              Formula.Not (atom Header_proposed) ) )
    in
    Formula.Ag
      (Formula.Implies
         ( atom Proposer_holds_straggler,
           (* A[p W q] = ~E[~q U (~p /\ ~q)] *)
           Formula.Not
             (Formula.Eu
                ( Formula.Not exits,
                  Formula.And
                    ( Formula.Not (atom Proposer_holds_straggler),
                      Formula.Not exits ) )) ))
  in
  let straggler_ignorance =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [
               atom Proposer_holds_parents;
               Formula.Not (atom Proposer_holds_straggler);
               atom Proposer_at_round_r;
             ],
           Formula.And
             ( Formula.Not
                 (Formula.K (Validator.V0, atom Straggler_accepted)),
               Formula.Not
                 (Formula.K
                    (Validator.V0, Formula.Not (atom Straggler_accepted))) ) ))
  in
  {
    name = "late-origin-admissible-and-evicted-only-by-a-future-round-jump";
    bucket = Statements.Fairness;
    formula = Formula.conj [ admissible; persists; straggler_ignorance ];
    antecedent =
      Formula.conj
        [
          atom Straggler_accepted;
          atom Proposer_can_still_collect;
          Formula.Not (atom Catchup_notice_pending);
        ];
  }

(** The family's statements. *)
let all = [ s1; s2; s3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st = Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure
    degrades every row to [proved = false] rather than raising. *)
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
