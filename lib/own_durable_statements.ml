(** The OWN_DURABLE statement family, encoded over the {!Own_durable_model}
    interpreted system. Three statements about the durability of a validator's
    OWN certificate record: that the queued write does reach the physical disk
    on a crash-free tail, that the durable record is what actually forbids
    signature equivocation, and that a peer's guarantee rests on an author-local
    write it can never observe. File citations refer to
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b].

    Reading guide for the K operands. The family has exactly ONE positive
    knowledge conjunct, [K_V2(own_cert_stored)] in {!s3}: a peer that has seen
    V1's certificate on gossip knows V1 first executed the
    [ProposedCertificates] insert, because certifier.rs:443-446 puts that write
    - and its [return Err] on failure - strictly upstream of every release
    route. Everything else in the family is IGNORANCE, and it is all of one
    shape: physical-media residency is invisible. [disk] appears in no view. V1
    cannot see it because no API on the write path reports it (layered_db.rs
    :118-124, :247-249, :463-495); V2 cannot see it because
    [publish_certificate] carries certificate bytes and nothing about V1's
    storage. The sharpest fact in the family is that the AUTHOR is as blind to
    its own durability as the peer is.

    What V2 CAN see. V2's view is [(pub_c1, pub_c2, revote_requested)]. The
    third component is a correction: an earlier draft gave V2 only the two
    gossip releases and justified that with the guard's byte-identical
    re-publish (certifier.rs:426). That justification covers only ONE of the two
    post-restart routes. The other - the one taken when the
    [ProposedCertificates] lookup MISSES - falls through to [propose_header]
    (certifier.rs:431-440), which spawns a fresh [request_vote] to every other
    primary (:286-312); the peer's handler recognises the repeat for a header it
    has already voted on (handler.rs:494-506). So a re-run of vote collection is
    an OBSERVABLE event at V2, and the model now carries it. {!s3} conjunct B is
    scoped accordingly.

    What was mined and what survived. The mining pass proposed three cards; two
    were retargeted and one was dropped.
    - Card 1 asserted an UNCONDITIONAL [leads_to] from a queued
      [CertificateStore::write] to disk, plus peer-ignorance. Both halves moved.
      The unconditional form is FALSE - a restart before the background thread's
      physical write loses the queued insert - so {!s1} scopes the [Af] to the
      post-restart (crash-free) tail, and [t_own_durable.ml] carries an explicit
      HONESTY witness that the unscoped form is refuted in this very model. The
      record moved from [Certificates] (a txn write) to [ProposedCertificates]
      (a plain [Database::insert], certifier.rs:443), and the ignorance moved
      from the peer to the AUTHOR, which is both sharper and better grounded.
    - Card 3 asserted the equivocation ban UNCONDITIONALLY and asserted
      knowledge of the keccak256 epoch randomness. Both moved. Unconditional is
      false: the guard's own lookup table is written asynchronously, so a crash
      before the physical write leaves the lookup empty on restart and vote
      collection re-runs - that path is present in the pristine model, which is
      exactly why {!s2} conditions the safety half on [disk = C1]. The epoch
      randomness sits behind leader election and epoch close, far outside this
      scope, so asserting K about it would be unfaithful; it is replaced by the
      peer's ignorance of the durability precondition.
    - Card 2 (restart-stable-proposal-implies-known-stored-header) was DROPPED.
      Its K operand does not exist: [LastProposed] is a SINGLE slot at
      [LAST_PROPOSAL_KEY = 0], overwritten every round, so the claim is false at
      every state where V1 has advanced past r; and its safety half is refuted
      in the PRISTINE code (the same asynchronous [Database::insert] durability
      gap), so its proposed gate would not have been the load-bearing cause of
      any flip - an R4 failure in the redundant direction. Its surviving content
      is carried here: the store-before-release ordering by {!s3}, and the
      "restart stability rests on an unobservable durability step" by {!s1} and
      {!s2}, both on the correctly-keyed one-slot-per-digest
      [ProposedCertificates] table. {!s3} is a NEW statement occupying its
      slot. *)

open Own_durable_model

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

(** S1 - own-write-persists-yet-author-cannot-observe-durability [liveness].

    (A) INEVITABLE PERSIST, on the crash-free tail:
    AG( (mem=C1 /\\ commit_pending /\\ restarted) -> AF disk=C1 ). Grounding:
    [LayeredDatabase::insert] writes the mem layer immediately and only QUEUES a
    [DBMessage::Insert] (layered_db.rs:391-396); the background run loop applies
    it either directly with [ins.insert(&db)] when no physical txn is open
    (:220-227) or into the open physical txn (:210-219), which [end_txn] commits
    once the overlap count reaches 1 (:155-174, dispatched at :199-201).
    [TxnGuard::drop] sends [EndTxn] for an abandoned txn into that SAME
    [end_txn] (:60-70, :202-208), so the count cannot wedge and starve the
    commit. Composite wiring: certifier.rs:443 -> composite_db.rs:93-95 -> the
    Epoch [LayeredDatabase] (composite_db.rs:33, lib.rs:94 [TableHint::Epoch]).

    The [restarted] conjunct in the antecedent is the honest scoping, NOT a
    convenience. The writer thread is in-process (layered_db.rs:306-315), so a
    crash before it runs simply loses the queued insert; the model gives V1 a
    one-shot crash budget and asserts the [Af] exactly on the tail where that
    budget is spent. [t_own_durable.ml] proves the unscoped form is FALSE here:
    from the pre-restart state A the path A -> R1 -> Q1 -> Q3 -> Q7 never
    reaches disk=C1.

    (B) DURABILITY IS UNOBSERVABLE TO ITS OWN AUTHOR:
    AG( (disk=C1 /\\ ~restarted) -> ~K_V1(disk=C1) ). Grounding: the epoch DB is
    opened [full_memory = true] (composite_db.rs:33), so [get] answers mem-first
    for the whole epoch and never consults disk once the key is in mem
    (layered_db.rs:383-389; txn-level :30-38 and :86-94); [commit]'s own doc
    comment states the data "may not be committed on-disk yet" on return
    (:118-135); nothing on the certifier path calls [persist]/[sync_persist],
    and those only drain the message queue via [DBMessage::CaughtUp] anyway
    (:463-495, :247-249); [LayeredDatabase::stats] does expose [open_txn_count]
    (:250-255, :317-333) but no consensus write path calls it. R3 colliding
    pair: worlds B = (mem C1, disk C1, no pend) and A = (mem C1, disk none,
    pend) share V1's view [View_v1 (Cell_c1, false, false, false, false)] and
    disagree on disk=C1.

    The [~restarted] guard is the honest carve-out, not a dodge: after a restart
    the mem layer is reloaded FROM disk (layered_db.rs:347-356), so mem=C1 then
    genuinely DOES entail disk=C1. That post-restart class is a singleton, which
    is why the fact is documented here but deliberately NOT asserted as a
    positive K (it would violate R2).

    Mutation pin: {!Own_durable_model.No_disk_write} deletes both physical-write
    routes, so the persist transition becomes "clear the queue, leave disk
    untouched"; disk=C1 becomes unreachable and the run from the antecedent
    state P1 reaches a stutter-closed terminal with disk=C1 false forever,
    refuting conjunct A. Conjunct B goes vacuously true (disk=C1 never holds),
    so the refutation is cleanly attributable to A. The antecedent stays
    reachable under the mutation, so the verdict is [Refuted], not
    [Vacuous_antecedent]. *)
let s1 =
  let inevitable_persist =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [ atom Mem_c1; atom Commit_pending; atom Restarted ],
           Formula.Af (atom Disk_c1) ))
  in
  let durability_unobservable =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Disk_c1, Formula.Not (atom Restarted)),
           Formula.Not (Formula.K (Validator.V1, atom Disk_c1)) ))
  in
  {
    name = "own-write-persists-yet-author-cannot-observe-durability";
    bucket = Statements.Liveness;
    formula = Formula.And (inevitable_persist, durability_unobservable);
    antecedent =
      Formula.conj [ atom Mem_c1; atom Commit_pending; atom Restarted ];
  }

(** S2 - durable-own-certificate-record-forbids-signature-equivocation [safety].

    (A) A DURABLE RECORD BLOCKS EQUIVOCATION:
    AG( disk=C1 -> AG ~published(C2) ). Grounding: on reopen, [open_table]
    refills the full-memory mem layer from whatever reached disk
    (layered_db.rs:347-356, [full_memory = true] at composite_db.rs:33); the
    certifier's [spawn_header_proposal] then finds the certificate at
    certifier.rs:418-420, logs "already certified … skipping proposal and
    re-publishing", re-gossips the STORED certificate and returns (:421-429).
    Why a re-run would otherwise differ: [Certificate::digest()] is the header
    digest and excludes the aggregate signature (certificate.rs:473-479), and
    the vote-aggregation loop breaks the instant a quorum forms, in arrival
    order (certifier.rs:318-322, :331-347), so a second run over a different
    responding 2f+1 subset yields a different aggregate under the SAME key - the
    code's own comment at certifier.rs:422-424 says exactly this.

    The [disk=C1] antecedent is load-bearing and is the correction the mining
    card needed. The unconditional form is FALSE in this model by construction:
    [ProposedCertificates] is written by the asynchronous [Database::insert]
    (certifier.rs:443 -> layered_db.rs:391-396), so a crash before the physical
    write leaves the guard's lookup empty on restart, vote collection re-runs,
    and a second aggregate really can be published - published(C2) IS reachable
    pristine, on the crash-lost-the-write branch. That is what makes conjunct A
    a genuine restriction rather than a tautology, and [t_own_durable.ml] tests
    both directions.

    (B) THE PEER CANNOT SEE THE DURABILITY PRECONDITION:
    AG( (published(C1) /\\ ~published(C2)) -> ~K_V2(disk=C1) ). Grounding:
    [publish_certificate] (certifier.rs:454, and the guard's re-publish at :426)
    carries the certificate bytes and nothing about V1's storage, and neither
    does a [request_vote]; V2's view holds no component of V1's storage at all.
    R3 colliding pair: worlds D = (disk C1, published C1) and C = (disk none,
    write still queued, published C1) share
    [View_v2 (true, false, false)] and disagree on disk=C1. The post-restart
    re-certification class [View_v2 (true, false, true)] is covered too: it
    contains P2 = (mem C1, disk NONE, write queued, published C1, restarted,
    re-certified), so [disk=C1] is undetermined there as well.

    Mutation pin: {!Own_durable_model.No_proposed_cert_guard} deletes the
    certifier.rs:418-430 early return, so the re-certify transition no longer
    requires the lookup to have missed; from a state that ALREADY has disk=C1
    the node re-runs vote collection, can form C2, and publishes it - so
    published(C2) becomes reachable from a disk=C1 state, refuting conjunct A.
    Conjunct B is untouched (V2's class still contains disk=C1-false worlds), so
    the refutation is attributable to A.

    Deliberately NOT pinned to {!Own_durable_model.No_disk_write}: under that
    mutation this statement's antecedent disk=C1 is UNREACHABLE, so
    [prove_nonvacuous] correctly returns [Vacuous_antecedent] rather than
    [Refuted]. That is an honest non-result, not a pin. *)
let s2 =
  let durable_record_blocks_equivocation =
    Formula.Ag
      (Formula.Implies
         (atom Disk_c1, Formula.Ag (Formula.Not (atom Pub_c2))))
  in
  let peer_cannot_see_durability =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Pub_c1, Formula.Not (atom Pub_c2)),
           Formula.Not (Formula.K (Validator.V2, atom Disk_c1)) ))
  in
  {
    name = "durable-own-certificate-record-forbids-signature-equivocation";
    bucket = Statements.Safety;
    formula =
      Formula.And
        (durable_record_blocks_equivocation, peer_cannot_see_durability);
    antecedent = atom Disk_c1;
  }

(** S3 - published-own-certificate-implies-known-prior-persist [security].

    (A) STORE-BEFORE-RELEASE IS KNOWN TO THE PEER:
    AG( published(C1) -> K_V2(own_cert_stored) ). Grounding: certifier.rs:441-456
    - the certificate is inserted into [ProposedCertificates] at :443 and an
    insert error takes the [error!; return Err(TaskError::from_message(…))] arm
    at :444-446, strictly BEFORE [state_sync.process_own_certificate] (:448) and
    before [network.publish_certificate] (:454). The guard's own re-publish path
    (:426) likewise only fires on a value read back OUT of that table
    (:418-420). So every route by which a certificate for H reaches gossip is
    downstream of a successful own-store write.

    This is the family's only positive K, so R1/R2 are discharged explicitly.
    R1: [own_cert_stored] is a fact about the AUTHOR's storage engine,
    structurally absent from V2's view [(pub_c1, pub_c2, revote_requested)]; and
    it is NOT rigid - it is false at the initial state and at the reachable
    post-restart state R0 = (mem none, disk none, no pend, nothing published,
    restarted, NOT stored), the run in which V1 crashed before ever persisting.
    R2: the operative state C = (mem C1, disk none, pend, published C1) sits in
    the V2 class [View_v2 (true, false, false)] of FOUR reachable worlds - C, D
    = (mem C1, disk C1, published C1), R3 = (mem none, disk none, published C1,
    restarted) and R4 = (mem C1, disk C1, published C1, restarted);
    [t_own_durable.ml] proves the class is not a singleton by showing that at C,
    where disk=C1 is false, V2 nonetheless cannot rule disk=C1 out - which is
    only possible because D shares C's view.

    (B) A SILENT RE-RELEASE IS INDISTINGUISHABLE FROM A FIRST RELEASE:
    AG( (published(C1) /\\ ~published(C2) /\\ ~revote_requested) ->
        (~K_V2(restarted) /\\ ~K_V2(~restarted)) ). Grounding: on the guard's
    route the certifier re-publishes the SAME stored [Certificate] value
    (certifier.rs:426), and upstream the proposer re-sends the SAME stored
    [Header] verbatim rather than building a new one ([repropose_header],
    proposer.rs:563-586, stored by [store_and_send_header] at :240-274) - the
    bytes on the wire are identical, so THAT restart leaves no trace in V2's
    view. R3 colliding pair: C (restarted false) and R3 = (mem none, disk none,
    published C1, restarted, stored, not yet re-certified) share
    [View_v2 (true, false, false)] and disagree on [restarted].

    The [~revote_requested] restriction is the correction an adversarial review
    forced, and it is load-bearing rather than cosmetic. The earlier unrestricted
    form was FALSE OF THE REAL SYSTEM, and the model was hiding it: the guard's
    re-publish is only ONE of the two post-restart routes. When the
    [ProposedCertificates] lookup MISSES - the crash-lost-the-write branch that
    this very model carries as T5 - [spawn_header_proposal] falls through to
    [propose_header] (certifier.rs:431-440), which spawns a fresh [request_vote]
    task to EVERY other primary ([others_primaries_by_id], certifier.rs:286-312)
    for a header those peers have already voted on; the receiving handler
    recognises it directly ([read_vote_info], "we have already cast a vote for
    this header … recast it quickly", handler.rs:494-506) after pinning the
    requester to the header's author (:485-493). And the in-process alternative
    is closed: at any published(C1) state the insert at certifier.rs:443 already
    succeeded, the epoch DB is full-memory (composite_db.rs:33) and [get] is
    mem-first (layered_db.rs:383-389), so an in-process re-entry HITS the guard
    and re-publishes instead of re-voting. A repeat vote request for an
    already-certified digest therefore really does imply the restart, and V2
    really does see it. The model now gives V2 that component, and the conjunct
    is asserted exactly where the re-release is silent. [t_own_durable.ml]
    carries a witness that at a re-certifying state V2 DOES know the restart, so
    the restriction is watched to be load-bearing rather than assumed.

    The [~published(C2)] restriction is load-bearing on the same footing: once a
    SECOND certificate for H is on the wire, V2 CAN infer the restart (both
    worlds in V2's (true,true,true) class have restarted = true), and without the
    restriction this conjunct is FALSE at those two states.

    Mutation pin: {!Own_durable_model.No_store_before_publish} deletes the
    [return Err(…)] at certifier.rs:444-446, adding a publish transition enabled
    with the own-store slot still empty. That makes reachable a state with a
    certificate on the gossip topic that was never persisted, which joins V2's
    (published C1, no C2) class and makes [K_V2(own_cert_stored)] fail
    throughout it - refuting conjunct A. Conjunct B survives (the class still
    holds both restart values), so the refutation is attributable to A. *)
let s3 =
  let store_before_release_known =
    Formula.Ag
      (Formula.Implies
         ( atom Pub_c1,
           Formula.K (Validator.V2, atom Own_cert_stored) ))
  in
  let release_indistinguishable_from_rerelease =
    Formula.Ag
      (Formula.Implies
         ( Formula.conj
             [
               atom Pub_c1;
               Formula.Not (atom Pub_c2);
               Formula.Not (atom Revote_requested);
             ],
           Formula.And
             ( Formula.Not (Formula.K (Validator.V2, atom Restarted)),
               Formula.Not
                 (Formula.K (Validator.V2, Formula.Not (atom Restarted))) ) ))
  in
  {
    name = "published-own-certificate-implies-known-prior-persist";
    bucket = Statements.Security;
    formula =
      Formula.And
        (store_before_release_known, release_indistinguishable_from_rerelease);
    antecedent = atom Pub_c1;
  }

(** The family's statements: one liveness, one safety, one security, each pinned
    by a different gate deletion. *)
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
