(** The FEE_ROUTING_SINK statements over {!Fee_routing_sink_model}: where a
    telcoin-network block's charge lands (S1), who the payee is (S2), and what a
    node can learn about a peer's fee-sink configuration (S3).

    {1 Reading guide for the K operands}

    The single knowledge agent is {!Fee_routing_sink_model.observer} = V0, the
    observing node. Its view is (own [BASEFEE_ADDRESS] slot, pipeline stage,
    locally computed settlement summary, own execution-tip comparison). The
    peer's parameter is in NO view, because it is a field of the peer's own
    parameters file (crates/config/src/node.rs:277-278) and appears in no
    genesis alloc, no committee file, no [Batch]
    (crates/types/src/worker/sealed_batch.rs:63-89) and no [CertifiedBatch]
    (crates/types/src/primary/output.rs:33-40).

    - [Sinks_agree] is neither a projection of V0's own view nor rigid. It
      reads the PEER's slot, which no view carries, and it is false at reachable
      states (every state where the peer resolved [Alt1] or [Alt2]) and true at
      others. The two positive knowledge claims about it are earned by a
      specific protocol observable and by nothing else: a primary header carries
      the proposer's execution tip
      (crates/types/src/primary/header.rs:31,159-160) and
      crates/consensus/primary/src/network/handler.rs:639-650 refuses to vote on
      a header whose tip the local node has not itself executed, resolving
      through [wait_for_execution]
      (crates/consensus/primary/src/consensus_bus.rs:620-648). Delete that
      comparison and the knowledge is gone; that is why S3 states the opacity as
      holding UNTIL the comparison rather than forever.
    - The two positive [K] operands sit on view classes proved non-singleton in
      test/t_fee_routing_sink.ml. At a [Tip_match] state the class holds both
      [Peer_defaulted] and [Peer_explicit Gov], because
      crates/tn-reth/src/lib.rs:201 and :209 both funnel through
      [unwrap_or(GOVERNANCE_SAFE_ADDRESS)] and so make an unset parameter and an
      explicit governance parameter observationally identical. At a
      [Tip_mismatch] state the class holds both [Peer_explicit Alt1] and
      [Peer_explicit Alt2], because the comparison reveals only that the peer's
      executed block differs, never which address it credited.
    - Every ignorance conjunct has a reachable witness pair sharing V0's whole
      view and disagreeing on the operand; those pairs are asserted in the
      contingency group of test/t_fee_routing_sink.ml.

    S1 and S2 carry no [K]: they are value-routing and authority-binding
    invariants, and their epistemic content would be empty. *)

open Fee_routing_sink_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** unique across every family *)
  bucket : Statements.bucket;  (** Safety | Liveness | Fairness | Security *)
  formula : atom Formula.t;  (** the claim *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - block-producer-take-is-tip-only-basefee-and-penalty-go-to-governance
    [security].

    AG( settled(b) -> ~basefee_in_credit(beneficiary) /\
        basefee_in_credit(fee_sink) /\
        (penalty_gas(tx)>0 -> penalty_in_credit(fee_sink)) /\
        credits = charge )

    The address credited for producing a block receives the priority tip and
    nothing else; the base-fee component of the charge and the whole
    over-estimation penalty are routed instead to the node's governance fee sink
    for off-chain processing; and the two credit legs sum to exactly what the
    caller was charged.

    - Conjunct A, ~basefee_in_credit(beneficiary): the gate is
      [let coinbase_gas_price = effective_gas_price.saturating_sub(basefee);]
      at crates/tn-reth/src/evm/handler.rs:156, whose product is what
      handler.rs:157-160 credits to [context.block().beneficiary()]. So a batch
      producer gains nothing by proposing a higher base fee - and it could not
      propose one anyway, since every voter rejects a batch whose base fee
      differs from the worker/epoch expectation
      (crates/batch-validator/src/validator.rs:188-195).
    - Conjunct B, basefee_in_credit(fee_sink): handler.rs:165-168 credits
      [self.basefee_address] with [basefee * gas_used], under the comment "send
      the base fee portion to a basefee account for later processing
      (offchain)". This is exactly where TN departs from stock revm, which burns
      the base fee.
    - Conjunct C, penalty_gas(tx)>0 -> penalty_in_credit(fee_sink): the
      over-estimation penalty [calculate_gas_penalty(gas_limit, gas_spent)]
      (handler.rs:109) is withheld from the caller's refund (handler.rs:112-113)
      and transferred to the SAME sink at handler.rs:125-131, a separate
      [incr_balance] site. So a producer gains nothing by packing transactions
      with bloated gas limits either.
    - Conjunct D, credits = charge: the two legs are the only credits in the
      handler besides the caller's own refund - the complete [incr_balance] set
      is handler.rs:121, :127-130, :157-160 and :165-168, and system calls are
      skipped outright (handler.rs:85-87, :145-147). Nothing is created and
      nothing is lost.

    Mutation pin. [Basefee_to_producer] deletes the [saturating_sub] at
    handler.rs:156, so the settle transition produces [Producer_tip_and_basefee]
    instead of [Producer_tip]: conjunct A fails outright and conjunct D fails
    too, because handler.rs:165-168 still pays the sink its base-fee leg and the
    credits now exceed the charge. [Basefee_burned] deletes the sink credit at
    handler.rs:165-168, so conjunct B fails and conjunct D fails in the other
    direction. Neither is silently repaired: the penalty transfer at
    handler.rs:125-131 is a distinct [incr_balance] carrying only
    [effective_gas_price * penalty_gas] and never the base fee (which is why the
    model keeps the two sink legs separately observable), the producer cannot
    redirect the sink because it is a node-local startup parameter no batch or
    certificate field reaches (crates/config/src/node.rs:277-278,
    crates/node/src/manager/node.rs:1253-1258,
    crates/tn-reth/src/lib.rs:196-210), and there is no second beneficiary
    credit anywhere in the handler. *)
let s_1 =
  let no_basefee_to_producer = Formula.Not (atom Producer_took_basefee) in
  let basefee_reaches_the_sink = atom Basefee_at_sink in
  let penalty_reaches_the_sink =
    Formula.Implies (atom Penalty_assessed, atom Penalty_at_sink)
  in
  let charge_is_conserved = atom Fees_conserved in
  {
    name =
      "block-producer-take-is-tip-only-basefee-and-penalty-go-to-governance";
    bucket = Statements.Security;
    formula =
      Formula.Ag
        (Formula.Implies
           ( atom Settled_block,
             Formula.conj
               [
                 no_basefee_to_producer;
                 basefee_reaches_the_sink;
                 penalty_reaches_the_sink;
                 charge_is_conserved;
               ] ));
    antecedent = Formula.And (atom Settled_block, atom Penalty_assessed);
  }

(** S2 - block-beneficiary-is-the-certified-author-not-the-batch-self-declared-field
    [security].

    AG( settled(b) -> beneficiary(b) = committee_addr(author(cert(b))) /\
        beneficiary(b) <> batch(b).beneficiary )
    /\ AG( unknown_author(b) -> AG ~settled(b) )

    Priority fees for a block are paid to the execution address the committee
    has on record for the authority that authored the certificate carrying the
    batch. The batch struct still carries its own [beneficiary] field, nothing
    ever validates it, and nothing ever reads it at execution - so a Byzantine
    proposer cannot redirect the tips of the blocks it produces.

    - Conjunct A: crates/consensus/executor/src/subscriber.rs:522-526 builds
      [CertifiedBatch { address:
      self.authority_execution_address(header.author())?, ... }], a committee
      lookup keyed by the certificate author (subscriber.rs:422-434). That field
      is documented as the block beneficiary at
      crates/types/src/primary/output.rs:33-40, is passed as the payload
      beneficiary at crates/engine/src/payload_builder.rs:153-164, lands in the
      block env at crates/tn-reth/src/evm/config.rs:133 and is what
      crates/tn-reth/src/evm/handler.rs:148,157-160 credits. The proposer's own
      [Batch.beneficiary] (crates/types/src/worker/sealed_batch.rs:68-70, set
      from the worker's own arguments at
      crates/batch-builder/src/batch.rs:49,123) is never consulted on that path.
    - Conjunct B: the committee lookup is fallible - subscriber.rs:422-434
      returns [SubscriberError::UnexpectedAuthority] when the author is missing
      from the committee, and subscriber.rs:439-440 records that such an error
      "is BAD and will most likely cause node shutdown". There is no fallback
      payee: the failure aborts the output rather than falling through to the
      batch's own field, which is why [Aborted] is terminal in the model.

    Mutation pin. [Beneficiary_from_batch_field] replaces the lookup at
    subscriber.rs:524 with [address: batch.beneficiary], so the certify
    transition binds [Payee_declared] and conjunct A fails: a Byzantine
    authority's batch pays its tips to any address it names. No sibling path
    repairs it. The entire voter-side check list at
    crates/batch-validator/src/validator.rs:39-82 - digest, worker id, epoch,
    size in bytes, decode/recover, no-4844, total gas, base fee - contains no
    beneficiary check, so admission never constrains the field.
    crates/tn-reth/src/evm/block.rs:983 copies
    [evm_env.block_env.beneficiary()] into the assembled header rather than
    re-deriving it, so the assembler is not a repair. The empty-output path does
    its own committee lookup (crates/engine/src/payload_builder.rs:104-107,
    crates/types/src/gas_accumulator.rs:161-165) but executes zero transactions
    and therefore routes no fees, so it is a disjoint branch and not a repair
    either. *)
let s_2 =
  let payee_is_the_certified_author =
    Formula.And (atom Payee_is_author, Formula.Not (atom Payee_is_declared))
  in
  let no_fallback_to_the_declared_field =
    Formula.Ag
      (Formula.Implies
         (atom Lookup_failed, Formula.Ag (Formula.Not (atom Settled_block))))
  in
  {
    name =
      "block-beneficiary-is-the-certified-author-not-the-batch-self-declared-field";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( Formula.Ag
            (Formula.Implies
               (atom Settled_block, payee_is_the_certified_author)),
          no_fallback_to_the_declared_field );
    antecedent = atom Settled_block;
  }

(** S3 - fee-sink-is-node-local-immutable-and-peer-opaque-until-tip-comparison
    [safety].

    AG( sink(V0)=governance_safe -> AG sink(V0)=governance_safe )
    /\ AG( settled(b) /\ no_peer_tip_compared ->
           ~K_V0(sink(V0)=sink(peer)) /\ ~K_V0(sink(V0)<>sink(peer)) )
    /\ AG( peer_exec_tip=own_exec_tip -> K_V0(sink(V0)=sink(peer)) )
    /\ AG( peer_exec_tip=own_exec_tip /\ sink(V0)=governance_safe ->
           ~K_V0(peer_param=Some(addr)) /\ ~K_V0(peer_param<>Some(addr)) )
    /\ AG( peer_exec_tip<>own_exec_tip ->
           K_V0(sink(V0)<>sink(peer)) /\ ~K_V0(sink(peer)=alt1)
           /\ ~K_V0(sink(peer)<>alt1) )

    A node resolves its fee sink exactly once, from a purely local configuration
    file, and the value cannot change for the life of the process. Nothing in
    the protocol carries that value, so until a node has compared a peer's
    execution tip it cannot know whether the peer resolved the same address; a
    matching tip proves the peer did, but never reveals whether the peer set the
    parameter explicitly or inherited the default; and a mismatching tip proves
    the peer did not, but never reveals which address the peer used instead.

    - Conjunct A, immutability: crates/tn-reth/src/lib.rs:196-210 -
      [static BASEFEE_ADDRESS: OnceLock<Address>] read through
      [*BASEFEE_ADDRESS.get().unwrap_or(&GOVERNANCE_SAFE_ADDRESS)] (lib.rs:201)
      and written through [let _ = BASEFEE_ADDRESS.set(...)] (lib.rs:209), whose
      doc says verbatim "This will only work on the first call ... Calling more
      than once will do nothing, not calling early can lead to an unset basefee
      address and a chain fork." The write happens inside [RethEnv::new]
      (lib.rs:650-662), which crates/node/src/manager/node.rs:1247-1264
      constructs before [ExecutionNode::new] - so on the node path no block ever
      executes against an unwritten slot, and that ordering is why the model's
      pipeline cannot leave [Booting] until both slots are locked.
    - Conjunct B, opacity before the comparison: the sink comes from
      [self.builder.tn_config.parameters.basefee_address]
      (node.rs:1253), declared at crates/config/src/node.rs:277-278 and written
      per node by crates/telcoin-network-cli/src/genesis/mod.rs:305 into the
      node's own parameters file, NOT into the shared genesis or committee files
      written alongside it at genesis/mod.rs:308-319.
    - Conjuncts C and E, what a tip comparison does prove: a primary header
      carries [latest_execution_block]
      (crates/types/src/primary/header.rs:31,159-160) and
      crates/consensus/primary/src/network/handler.rs:639-650 refuses to vote on
      a header whose tip is not among the local node's executed blocks
      ([wait_for_execution], crates/consensus/primary/src/consensus_bus.rs:
      620-648). Because everything else about the execution is shared and fixed,
      that comparison is exactly a test of sink agreement.
    - Conjunct D, what it still does not prove: lib.rs:201 and lib.rs:209 both
      funnel through [unwrap_or(GOVERNANCE_SAFE_ADDRESS)], so a peer that left
      [basefee_address] unset (its default, config/src/node.rs:366) and a peer
      that set it explicitly to the governance safe resolve the same address and
      are indistinguishable in every observable, forever.
    - Conjunct E's ignorance half: a mismatch says only that the peer's executed
      block differs. Nothing in the header, the certificate or the batch carries
      the address, so the observer cannot narrow the peer's sink beyond "not
      mine".

    Mutation pin. [Mutable_fee_sink] replaces the [OnceLock::set] once-semantics
    at lib.rs:207-210 with an unconditional store, adding the transition
    [Own_locked Gov -> Own_locked Alt1] at any stage: conjunct A fails
    immediately, and conjunct C fails as well, because a node that re-resolves
    its sink after having matched a peer's tip now holds a matching observation
    while the sinks in fact differ. No sibling path repairs it: [basefee_address]
    occurs only in crates/config/src/node.rs:277-278/366,
    crates/node/src/manager/node.rs:1253-1258,
    crates/telcoin-network-cli/src/genesis/mod.rs:47-53/305/333,
    crates/tn-reth/src/lib.rs:196-210/654-662 and
    crates/tn-reth/src/evm/handler.rs:5/42, so no protocol message can re-agree
    the sink; and the execution-tip comparison this family DOES model detects the
    divergence but never restores the previous address. *)
let s_3 =
  let sink_never_changes_once_locked =
    Formula.Ag
      (Formula.Implies (atom Sink_locked_gov, Formula.Ag (atom Sink_locked_gov)))
  in
  let opaque_before_the_comparison =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Settled_block, atom Tip_unchecked),
           Formula.And
             ( Formula.Not (Formula.K (observer, atom Sinks_agree)),
               Formula.Not
                 (Formula.K (observer, Formula.Not (atom Sinks_agree))) ) ))
  in
  let a_match_proves_agreement =
    Formula.Ag
      (Formula.Implies
         (atom Tip_match, Formula.K (observer, atom Sinks_agree)))
  in
  let a_match_hides_the_provenance =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Tip_match, atom Sink_locked_gov),
           Formula.And
             ( Formula.Not (Formula.K (observer, atom Peer_sink_explicit)),
               Formula.Not
                 (Formula.K (observer, Formula.Not (atom Peer_sink_explicit)))
             ) ))
  in
  let a_mismatch_proves_divergence_only =
    Formula.Ag
      (Formula.Implies
         ( atom Tip_mismatch,
           Formula.conj
             [
               Formula.K (observer, Formula.Not (atom Sinks_agree));
               Formula.Not (Formula.K (observer, atom Peer_sink_is_alt1));
               Formula.Not
                 (Formula.K (observer, Formula.Not (atom Peer_sink_is_alt1)));
             ] ))
  in
  {
    name =
      "fee-sink-is-node-local-immutable-and-peer-opaque-until-tip-comparison";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          sink_never_changes_once_locked;
          opaque_before_the_comparison;
          a_match_proves_agreement;
          a_match_hides_the_provenance;
          a_mismatch_proves_divergence_only;
        ];
    antecedent = atom Tip_match;
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st = Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

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
