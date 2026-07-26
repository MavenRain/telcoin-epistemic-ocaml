(** The EXEC_TIP statement family, encoded over the {!Exec_tip_model}
    interpreted system. All three statements were mined from telcoin-network,
    re-grounded line by line against this checkout (git HEAD [0c59c15b]) and
    stated here in the form that survived that pass. File citations refer to
    Telcoin-Association/telcoin-network.

    What the family is about: [header.latest_execution_block] is the only place
    a primary header claims anything about execution, and the ONE check that
    ever inspects it before a vote is
    [wait_for_execution(header.latest_execution_block())] in [vote_inner]
    (handler.rs:639-650). That check parks on the voter's own [RecentBlocks]
    watch and then applies [contains_execution_hash] to the voter's OWN executed
    headers (consensus_bus.rs:620-648, recent_blocks.rs:81-89). So it
    authenticates the claimed VALUE against the voter's own chain - and never
    the claimant's possession of it.

    Reading guide for the K operands:
    - [K (V1, _)] is the knowledge of an honest peer VOTER whose entire local
      state here is (own engine phase, own vote decision, certificate flag).
    - [K (V3, _)] is the knowledge of the committee member whose vote the quorum
      did not need: its entire local state is the certificate flag. That is the
      coarsest honest projection in the family, so its one POSITIVE knowledge
      claim (S2 conjunct A) is the hardest to make true, not the easiest.
    - [Author_executed] and [Claim_genuine] are both hidden global facts about
      the author's world, invisible in every agent's view. They are the operands
      of every ignorance conjunct here, and each is contingent: [Author_executed]
      is true only in the [Honest_executed] world and [Claim_genuine] false only
      in the [Byz_forged] world, all three worlds being reachable. *)

open Exec_tip_model

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

(** S1 - vote-implies-own-execution-yet-author-possession-unknown [security]. A
    peer vote for a proposed header is impossible unless the voter's OWN engine
    has produced an execution block whose hash equals
    [header.latest_execution_block]; and yet, having voted, the voter still
    cannot tell whether the header's AUTHOR ever executed that block.

    (A) own execution, node 1: AG( voted_1 -> executed_1 ). [vote_inner] returns
    [HeaderError::UnknownExecutionResult] unless
    [wait_for_execution(header.latest_execution_block())] succeeds
    (handler.rs:639-650); that call parks while [current_number < target_number]
    and only then requires [contains_execution_hash]
    (consensus_bus.rs:635-647), which scans the voter's OWN executed headers
    (recent_blocks.rs:81-89). Only after that does control reach [Vote::new]
    (handler.rs:860-872).

    (A') own execution, node 2: AG( voted_2 -> executed_2 ) - the same gate at
    the model's second honest peer voter. Stating it for both is what makes S2's
    quorum-knowledge conjunct a counting argument rather than a claim about one
    distinguished node.

    (B) author opacity: AG( voted_1 -> (~K_V1(author_executed) /\\
    ~K_V1(~author_executed)) ). [latest_execution_block] is a plain copied
    [BlockNumHash] field (header.rs:158-161) that [Header::validate] never
    constrains against the author (header.rs:97-132), and the proposer merely
    stamps back whatever its own bus reports (proposer.rs:208-215); a node's
    executed tip is written purely locally by its own engine
    (engine/lib.rs:262-271 -> payload_builder.rs:186-198 ->
    tn-reth/lib.rs:946-973 -> node.rs:1298-1322). So a Byzantine author can
    replay a genuine value it never executed, and the voter - which passed the
    gate on its OWN chain - has no predicate that separates the two worlds.

    R3 ignorance witness for (B), both members reachable: w_A =
    {author = Honest_executed; e1 = Executed; d1 = Voted; e2 = Queued;
    d2 = Undecided; cert = No_cert} and w_B the same state with
    author = Byz_replayed. [view V1] is [View_voter (Executed, Voted, No_cert)]
    at both, and [author_executed] is true at w_A and false at w_B, so both
    knowledge claims fail.

    Mutation pin: {!Exec_tip_model.No_execution_gate} deletes handler.rs:639-650,
    so the decide step becomes [Undecided -> Voted] from ANY engine phase,
    making {author = Honest_executed; e1 = Queued; d1 = Voted; ..} reachable and
    refuting conjunct (A). No sibling repairs it - the recast paths
    handler.rs:494-505 and :513-565 only replay a vote [vote_inner] already
    produced, so with the gate gone they replay the ungated vote. NOT pinned to
    {!Exec_tip_model.No_engine_spawn}: that mutation makes [voted_1]
    unreachable, degrading this statement to [Vacuous_antecedent] rather than a
    meaningful refutation. *)
let s1 =
  let own_execution_1 =
    Formula.Ag (Formula.Implies (atom Voted_1, atom Executed_1))
  in
  let own_execution_2 =
    Formula.Ag (Formula.Implies (atom Voted_2, atom Executed_2))
  in
  let author_opacity =
    Formula.Ag
      (Formula.Implies
         ( atom Voted_1,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Author_executed)),
               Formula.Not
                 (Formula.K
                    (Validator.V1, Formula.Not (atom Author_executed))) ) ))
  in
  {
    name = "vote-implies-own-execution-yet-author-possession-unknown";
    bucket = Statements.Security;
    formula =
      Formula.And (own_execution_1, Formula.And (own_execution_2, author_opacity));
    antecedent = atom Voted_1;
  }

(** S2 - certificate-implies-known-honest-execution-quorum [security]. A node
    that holds nothing but the certificate over a header - it has executed
    nothing itself and has seen no individual vote - thereby KNOWS that
    f + 1 = 2 honest committee members each ran that consensus output through
    their own engine and hold a canonical block with the claimed hash. The same
    certificate tells it nothing whatsoever about the AUTHOR.

    (A) quorum knowledge: AG( cert_formed -> K_V3(executed_1 /\\ executed_2) ).
    The author self-signs its own header into the vote aggregator before
    soliciting any peer (certifier.rs:277-280), and
    [quorum_threshold(4) = (2*4)/3 + 1 = 3] (committee.rs:684-688) is enforced
    as [weight >= threshold] by [validate_and_verify] (certificate.rs:243-246).
    So a certificate here is the author's self-vote plus exactly TWO peer votes,
    and each peer vote required that peer's own execution (handler.rs:639-650 +
    consensus_bus.rs:620-648 + recent_blocks.rs:81-89). Note the correction this
    encodes: the quorum is NOT three peer signers, and the author is a signer
    that never passes the gate - which is exactly why the single f = 1 fault
    budget is spent on the author, the strongest allocation against this claim.

    (B) author boundary: AG( cert_formed -> (~K_V3(author_executed) /\\
    ~K_V3(~author_executed)) ). Certificate validation covers epoch, genesis,
    [Header::validate], quorum weight and the aggregate signature and never
    touches the execution field (certificate.rs:225-251, header.rs:97-132), so
    the certificate carries no evidence about the author's own execution.

    R2 non-singleton discharge for (A): conjunct (B) IS the two-worlds proof.
    V3's view class at a certificate state has exactly two reachable members -
    w_A = {author = Honest_executed; e1 = Executed; d1 = Voted; e2 = Executed;
    d2 = Voted; cert = Cert} and w_B the same with author = Byz_replayed. They
    agree on the operand of (A) and disagree on [author_executed], which is
    precisely what (B) asserts. The operand of (A) is not rigid either: it is
    false at 48 of the 50 reachable states, e.g. at every initial state.

    Mutation pin: {!Exec_tip_model.No_execution_gate} lets both peers vote from
    [e_i = Queued], so a [Cert] state with [e1 = Queued] becomes reachable, the
    operand of (A) is false at a member of V3's certificate-view class, and the
    positive K fails. NOT pinned to {!Exec_tip_model.No_engine_spawn}, under
    which [cert_formed] is unreachable and the verdict degrades to
    [Vacuous_antecedent]. *)
let s2 =
  let quorum_knowledge =
    Formula.Ag
      (Formula.Implies
         ( atom Cert_formed,
           Formula.K
             (Validator.V3, Formula.And (atom Executed_1, atom Executed_2)) ))
  in
  let author_boundary =
    Formula.Ag
      (Formula.Implies
         ( atom Cert_formed,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V3, atom Author_executed)),
               Formula.Not
                 (Formula.K
                    (Validator.V3, Formula.Not (atom Author_executed))) ) ))
  in
  {
    name = "certificate-implies-known-honest-execution-quorum";
    bucket = Statements.Security;
    formula = Formula.And (quorum_knowledge, author_boundary);
    antecedent = atom Cert_formed;
  }

(** S3 - parked-vote-request-resolves-and-ahead-claim-stays-opaque [liveness].
    When a proposer one output ahead stamps a tip the voter has not executed,
    the voter's vote request PARKS inside [wait_for_execution] rather than being
    rejected - and it always resolves: the engine's idle-and-non-empty spawn
    step is the sole unblocking event, so the voter inevitably votes, rejects,
    or its own engine dies. Throughout the park the voter can neither confirm
    nor rule out that the ahead claim is genuine.

    (A) resolution: parked_1 ~> (voted_1 \\/ rejected_1 \\/ halted_1), i.e.
    AG( parked_1 -> AF(voted_1 \\/ rejected_1 \\/ halted_1) ).
    [wait_for_execution] parks on the [RecentBlocks] watch while
    [current_number < target_number] (consensus_bus.rs:635-639) and only then
    applies [contains_execution_hash] (:640-647); the queued output is unblocked
    exclusively by the engine loop's
    [pending_task.is_none() && !queued.is_empty()] spawn (engine/lib.rs:227-230),
    whose completion installs the new parent header (engine/lib.rs:262-271) and
    whose sealed header reaches the bus (payload_builder.rs:186-198 ->
    tn-reth/lib.rs:946-973 -> node.rs:1298-1322). The [halted_1] disjunct is the
    faithful admission that the SAME completion arm propagates an execution
    error with [?] (engine/lib.rs:264), killing the engine and leaving the
    waiter parked forever; without that disjunct the [Af] would be manufactured
    liveness (R8), because the code does not in fact guarantee a vote.

    (B) park opacity: AG( parked_1 -> (~K_V1(claim_genuine) /\\
    ~K_V1(~claim_genuine)) ). The claimed value is checked only against the
    voter's OWN executed set (recent_blocks.rs:81-89), which by definition does
    not yet contain the block, and nothing else in [Header::validate] constrains
    it (header.rs:97-132). So during the park the voter has no predicate at all
    that separates a genuine ahead tip from a fabricated one.

    R3 ignorance witness for (B), both members reachable (they are initial
    states): u_A = {author = Honest_executed; e1 = Queued; d1 = Undecided;
    e2 = Queued; d2 = Undecided; cert = No_cert} and u_F the same with
    author = Byz_forged. [view V1] is [View_voter (Queued, Undecided, No_cert)]
    at both, and [claim_genuine] is true at u_A and false at u_F.

    Mutation pin: {!Exec_tip_model.No_engine_spawn} deletes engine/lib.rs:227-230
    and thereby removes BOTH successors of [e_i = Queued] - the drain edge to
    [Executed] and the fault edge to [Halted] are the two outcomes of the single
    task spawned at engine/lib.rs:229 - so every parked state becomes terminal,
    the kernel stutter-closes it, and the [Af] of (A) fails at all three initial
    states. That is a real gate, not a sibling: [spawn_execution_task] has
    exactly one call site, no other route drains [queued], and the only live
    writer of [RecentBlocks] is fed exclusively by the completion of that task.
    {!Exec_tip_model.No_execution_gate} deliberately LEAVES this statement
    proved - decide stays enabled and the parked view class still spans all
    three author worlds - which keeps the two pins cleanly attributable. *)
let s3 =
  let resolution =
    Formula.leads_to (atom Parked_1)
      (Formula.Or (Formula.Or (atom Voted_1, atom Rejected_1), atom Halted_1))
  in
  let park_opacity =
    Formula.Ag
      (Formula.Implies
         ( atom Parked_1,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Claim_genuine)),
               Formula.Not
                 (Formula.K (Validator.V1, Formula.Not (atom Claim_genuine)))
             ) ))
  in
  {
    name = "parked-vote-request-resolves-and-ahead-claim-stays-opaque";
    bucket = Statements.Liveness;
    formula = Formula.And (resolution, park_opacity);
    antecedent = atom Parked_1;
  }

(** The family's statements: two security statements pinned by the pre-vote
    execution gate and one liveness statement pinned by the engine spawn step. *)
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
