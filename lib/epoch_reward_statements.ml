(** The EPOCH_REWARD statement family, encoded over the {!Epoch_reward_model}
    interpreted system. Three statements about telcoin-network's per-epoch
    leader-reward counter: the credit that survives the engine's empty-output
    skip, the crash-rebuild partition that keeps every committed round credited
    exactly once, and the boundary output that inevitably seals the epoch even
    with no batches to execute. File citations refer to
    Telcoin-Association/telcoin-network (HEAD 0c59c15b).

    Reading guide for the K operands. [V1] is the reference node and the ONLY
    knowledge agent: its view is its own consumption phase, its own three reward
    counters, its own sealed flag - process-local state (gas_accumulator.rs:20-21,
    :90-96) - plus the single inbound wire fact that says anything about a peer's
    execution, a MATCHED peer epoch-record vote (epoch_votes.rs:88-111). Every
    [K (Validator.V1, _)] operand below therefore targets a fact about the PEER:
    whether the peer sealed, what the peer's counters hold, whether the peer
    crashed.

    The knowledge about the peer's COUNTERS is always CONDITIONAL - "if the peer
    has sealed, then its counts agree with mine" - because the counter is
    process-local and in-memory and is never gossiped in any form; asserting the
    unconditional form would have been an R1/R5 defect. What makes the
    conditional form real is that a count mismatch is chain-visible: the closing
    block stamps [generate_withdrawals()] and its root into the header
    (block.rs:969-978), and re-execution feeds [apply_consensus_block_rewards]
    from the LOCAL [ctx.rewards_counter] (block.rs:824), so a divergent count is
    a state-root rejection.

    The knowledge about the peer's SEAL is different, and S3 states both halves.
    Sealing is a local execution act, but it is acknowledged exactly once, at the
    boundary: [close_epoch] awaits [wait_for_consensus_execution]
    (run_epoch.rs:653) and [write_epoch_record] then commits
    [latest_execution_block_num_hash()] into [EpochRecord.final_state]
    (close_epoch.rs:236-245, recent_blocks.rs:67-74); committee members sign that
    record and gossip the vote (epoch_votes.rs:59-73) and a receiver counts it
    only on a digest and committee-membership match (epoch_votes.rs:88-111). So a
    matched peer vote DOES tell V1 the peer executed the identical closing block.
    S3 conjunct C is therefore scoped to the window before that vote arrives, and
    conjunct D asserts the positive knowledge the vote confers.

    One K the mining pass proposed was DROPPED rather than weakened: that a
    closing block's randomness entails a quorum-signed leader certificate.
    output.rs:378-382 reads
    [leader.aggregated_signature().unwrap_or_else(|| { error!(...);
    BlsSignature::default() })] - a DEFAULT fallback with only an error log - so
    the randomness does not by itself entail a quorum signature, and asserting it
    would have been true only by omitting the default. *)

open Epoch_reward_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - blockless-round-credits-its-leader-with-no-block [fairness]. A
    committed output that carries no batches and is not the epoch close is
    skipped by the engine entirely - no execution block is produced and the
    executed-block watermark does not move - yet its leader is still credited
    exactly once, and once a node's own counter for that round's leader stands at
    one it KNOWS every peer that has executed the epoch-closing block holds the
    same count, whatever that peer's hidden crash-and-rebuild history was.

    (A) The credit precedes the skip:
    AG( (consumed_blockless /\\ watermark_zero) -> credited_blockless ).
    payload_builder.rs:22-30 puts
    [gas_accumulator.rewards_counter().inc_leader_count(output.leader().author())]
    at :30, the FIRST statement of [execute_consensus_output]; the batch-less
    non-closing early return is at :84-97 and returns the unchanged canonical
    header after only [engine_update_tx.try_send((leader_round,
    consensus_num_hash, None))]. [watermark_zero] is true exactly at phases
    P0/P1, grounded in recent_blocks.rs:36-60 ([push_latest] with [None] pushes
    NO executed block) plus consensus_bus.rs:669-688
    ([last_executed_consensus_block] reads [latest_execution_block()]'s
    parent_beacon_block_root): the skipped round leaves the watermark at 0.

    (B) The blockless credit is fleet-wide, and known at the counter:
    AG( credited_blockless -> K_V1( sealed_2 -> credit_blockless_agrees ) ). The
    only other production writer of the counter is consensus_pack.rs:1267-1294
    [count_leaders], which walks CONSENSUS headers (not executed blocks) and so
    credits the blockless round on a restarted peer too; gas_accumulator.rs:98-107
    shows the increment is a bare [+= 1] with no per-round key; block.rs:969-978
    seals [rewards_counter.generate_withdrawals()] and its root into the closing
    block, which is what makes a mismatch chain-visible.

    R1/R2: the K operand mentions two fields of the PEER's local state (its
    sealed flag and its [l1] counter) that appear in no component of V1's view,
    so it is not knower-local; it is not rigid either, being FALSE at the
    reachable state (v1 = P0, ledger (0,0,0)) paired with a sealed peer holding
    (1,1,1), so [Not (K (V1, ...))] is satisfiable and the knowledge is earned by
    V1 having itself credited the blockless round. The operative view class is
    non-singleton: at v1 = (P1, (One,Zero,Zero), unsealed, no peer vote) it
    contains both (v2 = (P0, (Zero,Zero,Zero), unsealed), v2_restarted = false)
    and (v2 = (P3, (One,One,One), sealed), v2_restarted = true) - V1 has not
    sealed there, so no epoch record of its own exists to match a peer vote
    against (close_epoch.rs:231-248) and the vote component cannot separate them.

    Mutation pin: {!Epoch_reward_model.Credit_after_skip} moves
    [inc_leader_count] below the batch-less non-closing early return, so the
    P0 -> P1 step no longer sets [l1 := One] and conjunct A is false at the
    (still reachable) antecedent state - a genuine [Refuted], never a
    [Vacuous_antecedent]. {!Epoch_reward_model.No_catchup_watermark} and
    {!Epoch_reward_model.Skip_batchless_close} both leave this statement proving,
    so the refutation is cleanly attributable. *)
let s1 =
  let credit_precedes_skip =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom V1_consumed_blockless, atom V1_watermark_zero),
           atom V1_credited_blockless ))
  in
  let credit_is_fleet_wide =
    Formula.Ag
      (Formula.Implies
         ( atom V1_credited_blockless,
           Formula.K
             ( Validator.V1,
               Formula.Implies (atom V2_sealed, atom Credit_blockless_agrees) )
         ))
  in
  {
    name = "blockless-round-credits-its-leader-with-no-block";
    bucket = Statements.Fairness;
    formula = Formula.And (credit_precedes_skip, credit_is_fleet_wide);
    antecedent =
      Formula.And (atom V1_consumed_blockless, atom V1_watermark_zero);
  }

(** S2 - restart-rebuild-credits-each-committed-round-exactly-once [safety]. The
    two halves of the restart rebuild PARTITION the epoch's committed rounds:
    [count_leaders] credits only rounds at or below the executed-block watermark,
    and [replay_missed_consensus] re-executes only the outputs strictly above it.
    So a node that crashed mid-epoch never credits a round twice, at the epoch
    close its per-leader ledger is identical to that of a node that ran the epoch
    straight through, and a node that has sealed KNOWS this of every peer that
    has sealed - while still being unable to tell whether that peer crashed at
    all.

    (A) No double credit: AG( ~double_credit_2 ). consensus_pack.rs:1284-1291 -
    [if leader_round > last_executed_round { continue; }] guards the only
    catchup-side increment; state-sync/lib.rs:148-182 - [get_missing_consensus]
    collects only consensus numbers [last_executed_block.number + 1 ..=
    last_db_block.number]; start_epoch.rs:71-107 forwards exactly those through
    the normal engine path. gas_accumulator.rs:98-107 has no dedup, so the
    partition is the ONLY thing preventing a second credit.

    (B) Fleet agreement at the seal:
    AG( (sealed_1 /\\ sealed_2) -> ledgers_equal ). node.rs:231-232 derives
    [last_executed_round] from the pinned finalized header's nonce and
    node.rs:262-268 bounds [count_leaders] by it for the current epoch only;
    node.rs:1272-1293 ([try_restore_state]) reseeds recent_blocks from EXECUTED
    blocks only, which is why a blockless round falls on the replay side of the
    partition rather than the catchup side; block.rs:969-978 seals the resulting
    counts into the closing block's withdrawals root.

    (C) Agreement known, crash invisible:
    AG( sealed_1 -> ( K_V1( sealed_2 -> ledgers_equal ) /\\ ~K_V1(restarted_2)
    /\\ ~K_V1(~restarted_2) ) ). The in-memory counter is discarded on restart
    (gas_accumulator.rs:18-36 module doc: the three cooperating codepaths,
    "ensuring no rounds are skipped or double-counted"; gas_accumulator.rs:109-113
    [clear] plus run_epoch.rs:636-660, which calls it only at the boundary);
    nothing in the protocol reports a peer's restart, so the crash is invisible
    precisely because the partition is exact.

    R1/R2/R3: the K operand is a joint fact over the peer's sealed flag and the
    peer's three counters, none of which appear in V1's view; it is not rigid,
    being FALSE at the reachable state (v1 = P1, ledger (One,Zero,Zero)) paired
    with a sealed peer holding (One,One,One) - V1 only comes to know it by
    sealing itself. The operative view class at v1 = (P3, (One,One,One), sealed,
    no peer vote) contains the never-crashed peer (v2 = (P3, (One,One,One),
    sealed), v2_restarted = false) and the crashed-and-rebuilt peer
    (byte-identical ledger, v2_restarted = true): distinct worlds with the same
    V1 view, which is simultaneously the colliding pair witnessing both ignorance
    conjuncts. The peer's epoch vote does not close this gap either - it commits
    to [final_state] and [final_consensus] (close_epoch.rs:238-245), never to how
    the signer's in-memory accumulator was assembled - so the same pair survives
    at (that v1 with the peer vote matched).

    Mutation pin: {!Epoch_reward_model.No_catchup_watermark} deletes
    [if leader_round > last_executed_round { continue; }], so the crash-at-P2
    restart rebuilds (One,One,One) from the whole pack and then replays [O3] on
    top, producing [l3 = Two]: conjunct A gains a reachable double-credit state,
    conjunct B a sealed pair with unequal ledgers, and conjunct C's positive K a
    class member with a sealed, unequal peer. ({!Epoch_reward_model.Credit_after_skip}
    also refutes B and C; the pin is the watermark guard, its own gate. Under
    {!Epoch_reward_model.Skip_batchless_close} this statement's antecedent is
    UNREACHABLE, so that pair would be a [Vacuous_antecedent] artifact and is not
    pinned.) *)
let s2 =
  let no_double_credit = Formula.Ag (Formula.Not (atom V2_double_credit)) in
  let agree_at_seal =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom V1_sealed, atom V2_sealed),
           atom Ledgers_equal ))
  in
  let agreement_known_crash_invisible =
    Formula.Ag
      (Formula.Implies
         ( atom V1_sealed,
           Formula.And
             ( Formula.K
                 ( Validator.V1,
                   Formula.Implies (atom V2_sealed, atom Ledgers_equal) ),
               Formula.And
                 ( Formula.Not (Formula.K (Validator.V1, atom V2_restarted)),
                   Formula.Not
                     (Formula.K
                        (Validator.V1, Formula.Not (atom V2_restarted))) ) ) ))
  in
  {
    name = "restart-rebuild-credits-each-committed-round-exactly-once";
    bucket = Statements.Safety;
    formula =
      Formula.And
        ( no_double_credit,
          Formula.And (agree_at_seal, agreement_known_crash_invisible) );
    antecedent = Formula.And (atom V2_restarted, atom V2_sealed);
  }

(** S3 - batchless-boundary-output-inevitably-seals-the-epoch [liveness]. The
    empty-output fast path is conditional on the epoch NOT closing, so a boundary
    output that carries no batches does not get skipped: the engine builds one
    synthetic empty block from the parent's fee and gas limit, and that block
    runs applyIncentives/concludeEpoch and carries the reward withdrawals. Hence
    from the state where the batch-less boundary output is next, the epoch
    inevitably seals, and it cannot seal any earlier than that output. Sealing is
    a purely local execution act, so a node that has sealed does not know whether
    any peer has - until the peer's epoch-record vote arrives and matches, which
    is exactly the acknowledgement, and then it does.

    (A) Inevitable seal: AG( at_boundary -> AF sealed_1 ), via
    {!Formula.leads_to}. payload_builder.rs:84-97 - the skip is gated on
    [if !output.close_epoch()]; payload_builder.rs:99-136 - the batch-less
    closing output instead builds ONE [TNPayload] from
    [canonical_header.base_fee_per_gas] / [gas_limit] with the leader's execution
    address as beneficiary and executes it; output.rs:240-244
    [close_epoch_for_last_batch] answers [Some(true)] for an empty batch_digests;
    payload.rs:87-91 turns that into [close_epoch = Some(output.keccak_leader_sigs())];
    block.rs:794-835 fires [apply_consensus_block_rewards] +
    [apply_closing_epoch_contract_call] under [ctx.close_epoch = Some].

    (B) No early seal, the weak-until A[ ~sealed W at_boundary ] encoded by the
    kernel identity A[p W q] = ~E[ ~q U (~p /\\ ~q) ] with p = ~sealed_1 and
    q = at_boundary: AG( ~sealed_1 -> ~E[ ~at_boundary U (sealed_1 /\\
    ~at_boundary) ] ). run_epoch.rs:530-539 / :595-616 - [set_epoch_close] is
    applied only from [committed_at() >= self.epoch_boundary], and only the first
    such output is forwarded before [wait_for_epoch_boundary] returns;
    block.rs:969-978 - a non-closing block carries empty extra_data and the
    EMPTY_WITHDRAWALS root, so no earlier block can be the seal.

    (C) The seal is unacknowledged UNTIL the peer's epoch vote:
    AG( (sealed_1 /\\ ~saw_peer_vote) -> ~K_V1( sealed_2 ) ). Before that vote
    there is nothing to go on. The closing block is produced by each node's own
    execution of the committed output (payload_builder.rs:99-136) and the engine's
    only outward signal is the local [engine_update_tx] into that node's own
    consensus bus (payload_builder.rs:92 for skips, node.rs:1305-1322 for the
    consumer); the one gossiped progress record, [PrimaryGossip::Consensus] of a
    [ConsensusResult], is published by the CONSENSUS subscriber and carries the
    consensus header's epoch/round/number/hash only, never an execution result
    (subscriber.rs:288-316, block.rs:116-133). So a node that has sealed but has
    not matched a peer vote cannot rule out that peer still sitting at the
    epoch's first output.

    (D) The epoch vote IS the acknowledgement:
    AG( saw_peer_vote -> K_V1( sealed_2 ) ). This is the conjunct the earlier
    draft got wrong by asserting C unconditionally.
    [close_epoch] awaits [wait_for_consensus_execution(target_hash)]
    (run_epoch.rs:653) and only then does [write_epoch_record] build
    [EpochRecord { .., final_state: latest_execution_block_num_hash(),
    final_consensus: (last_consensus_header.number, target_hash) }]
    (close_epoch.rs:231-245); [latest_execution_block_num_hash] returns the last
    EXECUTED block's num/hash (recent_blocks.rs:67-74), so past that await the
    record's digest is a commitment to having executed the epoch-closing block.
    The record is published on [epoch_record_watch] (close_epoch.rs:247-248),
    [spawn_epoch_vote_collector] picks it up (epoch_votes.rs:302-342),
    [manage_epoch_votes] signs it and gossips the vote (epoch_votes.rs:59-73),
    and a receiver counts an inbound vote only when
    [vote.epoch_hash == epoch_hash && committee_keys.contains(&vote.public_key)]
    against its OWN record's digest (epoch_votes.rs:88-111). A matched vote
    therefore certifies that the signing peer computed the identical closing
    execution state, i.e. that it sealed.

    R1/R2/R3. Conjunct C is an IGNORANCE claim, conjunct D a positive one; both
    operands are the peer's local execution fact [V2_sealed], which is not rigid
    (false at every reachable state with the peer below P3, true at the peer's
    P3). Colliding pair for C: (v1 = (P3, (One,One,One), sealed, no peer vote),
    v2 = (P3, (One,One,One), sealed), v2_restarted = false) and the same v1 with
    (v2 = (P0, (Zero,Zero,Zero), unsealed), v2_restarted = false) - identical V1
    view, opposite truth value of [V2_sealed]. For D, [V2_sealed] is NOT a
    function of V1's view in the R1 sense - it is the peer's act, learned through
    a message - and its operative view class is non-singleton: at
    v1 = (P3, (One,One,One), sealed, peer vote matched) the class holds both
    (v2 = (P3,(One,One,One),sealed), v2_restarted = false) and the
    crashed-and-rebuilt (v2 = (P3,(One,One,One),sealed), v2_restarted = true),
    since the vote commits to [final_state], never to how the signer's
    accumulator was assembled.

    Mutation pin: {!Epoch_reward_model.Skip_batchless_close} deletes the
    [if !output.close_epoch()] condition, so the P2 -> P3 step takes the early
    return and [sealed] is never set; the model's terminal state has v1 at P3
    with [V1_sealed] false and [AF sealed_1] fails at the (still reachable)
    antecedent state. Conjuncts B, C and D degrade to vacuously true under that
    mutation - with no closing block, no epoch record commits to a closing state,
    so there is no seal to acknowledge - and the refutation is attributable to A
    alone. {!Epoch_reward_model.Credit_after_skip} and
    {!Epoch_reward_model.No_catchup_watermark} leave this statement proving. *)
let s3 =
  let inevitable_seal =
    Formula.leads_to (atom V1_at_boundary) (atom V1_sealed)
  in
  let no_early_seal =
    (* A[ ~sealed W at_boundary ] = ~E[ ~at_boundary U (sealed /\ ~at_boundary) ] *)
    Formula.Ag
      (Formula.Implies
         ( Formula.Not (atom V1_sealed),
           Formula.Not
             (Formula.Eu
                ( Formula.Not (atom V1_at_boundary),
                  Formula.And
                    (atom V1_sealed, Formula.Not (atom V1_at_boundary)) )) ))
  in
  let seal_unacknowledged_before_the_vote =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom V1_sealed, Formula.Not (atom V1_saw_peer_vote)),
           Formula.Not (Formula.K (Validator.V1, atom V2_sealed)) ))
  in
  let vote_is_the_acknowledgement =
    Formula.Ag
      (Formula.Implies
         (atom V1_saw_peer_vote, Formula.K (Validator.V1, atom V2_sealed)))
  in
  {
    name = "batchless-boundary-output-inevitably-seals-the-epoch";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( inevitable_seal,
          Formula.And
            ( no_early_seal,
              Formula.And
                (seal_unacknowledged_before_the_vote, vote_is_the_acknowledgement)
            ) );
    antecedent = atom V1_at_boundary;
  }

(** The family's statements: the blockless credit (fairness), the crash-rebuild
    partition (safety) and the batch-less boundary seal (liveness), pinned
    respectively by {!Epoch_reward_model.Credit_after_skip},
    {!Epoch_reward_model.No_catchup_watermark} and
    {!Epoch_reward_model.Skip_batchless_close}. *)
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
