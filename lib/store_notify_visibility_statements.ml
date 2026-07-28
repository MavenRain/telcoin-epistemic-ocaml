(** The STORE_NOTIFY_VISIBILITY family (S1, S2, S3): three statements about the
    seam between a certificate write and the handlers waiting to hear about it,
    encoded over {!Store_notify_visibility_model}. File citations refer to
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b].

    WHAT WAS MINED. A primary cannot vote on a header until it holds every
    parent certificate the header names, and it obtains them by parking on
    [CertificateStore::notify_read] (header_validator.rs:56-63,
    handler.rs:688-693). Three separate mechanisms have to hold for that park to
    be safe, and each is one statement here.

    - S1 is the RACE the re-read closes. Registration
      (certificate_store.rs:253) and the store write (:144, inside [save_cert])
      are not under a common lock, so a certificate written between the
      handler's decision to wait and its registration would notify an empty
      list. The block at :255-263 - register, then read, and on a hit return
      directly - is the only thing that turns such a registration into a
      resolution.
    - S2 is the FAN-OUT. [NotifyRead::notify] removes the whole registration
      list under the shard lock (notify_read.rs:33) and fires EVERY sender
      (:38-40). Waiters on one digest are one-per-inbound-header, i.e.
      one-per-peer-request, so a discipline that served only the first
      registrant would let one peer's vote request permanently outrank
      another's on the same dependency.
    - S3 is the VISIBILITY. [save_cert] notifies at :144, which is BEFORE
      [txn.commit()] at :183/:206. What makes that ordering safe is
      [LayeredDbTxMut::insert] writing the mem layer first
      (layered_db.rs:98) and [get] reading mem first (:383-389): the
      certificate is readable from the instant the notify fires, long before
      the background thread's physical commit (:162).

      SCOPE CORRECTION (R7). The candidate card aimed S3 at the cache mirror's
      commit-then-clear ordering (layered_db.rs:160-169). That ordering is dead
      code for this table: [Certificates] is [TableHint::Epoch] (lib.rs:91), the
      epoch layer is opened [full_memory = true] (composite_db.rs:33), and the
      writer thread therefore gets [mem_db = None] (:311), which disables the
      retention push (:217-219), the post-commit drain (:165-169) and the
      direct-write clear (:224-226) alike. The load-bearing visibility gate for
      a certificate is the mem-FIRST write at :98, and that is what S3 states
      and what the mutation deletes.

    READING GUIDE FOR THE K OPERANDS. Both agents are concurrent [notify_read]
    callers inside ONE validator, and each sees exactly two things: the state of
    its own call and the answer its own store gives it
    ({!Store_notify_visibility_model.view}).

    - S1-B is the family's one POSITIVE K, [K_V1(possessed(d))]. Its operand is
      a fact about OTHER validators' stores; a header carries parent digests,
      not certificates, so nothing V1 observes is a projection of it. It is not
      rigid either: on the fabricated-parent branch
      ({!Store_notify_visibility_model.initial_fabricated}) no validator holds
      d and [possessed] is false at every state of that component. What makes
      the K true is a mechanism fact and nothing else: V1's call can only return
      a certificate that some [save_cert] wrote (certificate_store.rs:144 or the
      re-read at :262), and [save_cert] can only run on a certificate that was
      delivered - so a resolved wait is a proof of existence somewhere, even
      though the wait itself is not. The operative view class is NOT a
      singleton: [(W_done, store_visible = true)] spans every reachable
      combination of the physical-commit bit and the other handler's state, and
      the R2 test in test/t_store_notify_visibility.ml witnesses that directly
      by proving V1 does not know [durable(d)] is false there.
    - S1-A, S2-B and S3-B are IGNORANCE conjuncts, each with a concrete witness
      pair and a [satisfiable] test in the contingency group. S1-A pairs an
      honest-branch pre-write state with the fabricated-branch state of the same
      shape. S2-B pairs two states differing only in whether the OTHER handler
      has registered, which V1 cannot see because the pending map is private and
      shard-locked (notify_read.rs:19, :64-74) and [save_cert] discards even the
      count [notify] returns (certificate_store.rs:144). S3-B pairs the
      pre-commit and post-commit states, which are indistinguishable because
      [commit] warns the data "may not be committed on-disk yet"
      (layered_db.rs:118-124), [persist]/[sync_persist] answer with a bare
      oneshot (:247-249, :463-495) and [stats] (:317-333) is called by no
      consensus path. *)

open Store_notify_visibility_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;  (** unique across every family *)
  bucket : Statements.bucket;  (** Safety | Liveness | Fairness | Security *)
  formula : atom Formula.t;  (** the CTLK claim *)
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S1 - post-registration-reread-resolves-a-parent-wait-that-began-too-late
    [liveness].

    Conjunct A (certificate_store.rs:251-266, header_validator.rs:56-63): at
    every state where V1's handler has entered [notify_read] for the parent
    digest d and its own store still answers [None], V1 does NOT know that any
    honest validator possesses d. A header names parent digests and carries no
    certificate, so the fabricated-parent branch is view-identical to the
    honest one until a write lands. This is why the wait exists at all, and why
    it has to be bounded by something other than the store.

    Conjunct B (certificate_store.rs:144, :262, notify_read.rs:39): at every
    state where V1's [notify_read] has RETURNED, V1 knows some honest validator
    possesses d. The only two ways the call can return a certificate are the
    re-read hit at :262 and the oneshot the notify fired at notify_read.rs:39,
    and both require a [save_cert] to have run on a delivered certificate. The
    resolved wait is therefore a proof of existence elsewhere - the one global
    fact this local event does certify.

    Conjunct C (certificate_store.rs:255-263): from every state where V1's
    handler is waiting and the certificate really is held somewhere, the wait
    inevitably resolves. Both orders are covered: a handler that registers
    BEFORE the write is woken by [save_cert]'s notify (:144), and a handler that
    registers AFTER it is resolved by the re-read (:255-263) - which is the only
    resolution available on the single-delivery branch.

    MUTATION PIN. {!No_post_registration_reread} deletes :255-263 and refutes
    conjunct C: it removes the transition "register while d is already stored ->
    resolve immediately", leaving the handler parked on a oneshot that the
    already-fired notify will never fire again. The duplicate-write sibling is
    modelled ({!Store_notify_visibility_model.t5_redeliver}, from
    cert_manager.rs:189-196 and handler.rs:267) and is a real partial repair,
    but it is a branch and not an obligation, so the single-delivery path
    (T6) reaches a terminal with the handler still parked. Nothing else repairs
    it: the production caller has no timeout (header_validator.rs:56-63 awaits
    the [FuturesOrdered] bare; only tests wrap it in [timeout]),
    [Registration::poll] awaits the oneshot and nothing else
    (notify_read.rs:109-125), and [Registration::drop] only de-registers
    (:127-135). *)
let s_1 =
  let conjunct_a =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom W1_want, Formula.Not (atom Store_visible)),
           Formula.Not (Formula.K (Validator.V1, atom Possessed)) ))
  in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies (atom W1_done, Formula.K (Validator.V1, atom Possessed)))
  in
  let conjunct_c =
    Formula.Ag
      (Formula.Implies
         (Formula.And (atom W1_want, atom Possessed), Formula.Af (atom W1_done)))
  in
  {
    name = "post-registration-reread-resolves-a-parent-wait-that-began-too-late";
    bucket = Statements.Liveness;
    formula = Formula.And (conjunct_a, Formula.And (conjunct_b, conjunct_c));
    antecedent = Formula.And (atom W1_want, Formula.Not (atom Store_visible));
  }

(** S2 - one-write-wakes-every-registered-parent-waiter [fairness].

    Conjunct A (notify_read.rs:31-42, certificate_store.rs:144): from every
    state where BOTH concurrent handlers are parked on the same parent digest
    and the certificate is held somewhere, BOTH resolve. The write takes the
    entire registration list out of the map with [remove(key)] (:33) and fires
    every sender in it (:38-40); registration appends with no priority (:64-66).
    No waiter is preferred by arrival order and none can be left behind by
    another's resolution. The waiters are one-per-inbound-vote-request, so this
    is a no-starvation property BETWEEN PEERS' requests, not merely an internal
    liveness detail.

    Conjunct B (notify_read.rs:19, :64-74, certificate_store.rs:144): at every
    state where V1's handler is parked, V1 does not know whether the other
    handler is parked too. The pending map is private and shard-locked, the
    bare [num_pending] counter (:76-78) is read by no consensus path, and
    [save_cert] discards even the remaining-count that [notify] returns. That
    mutual blindness is exactly why the fan-out has to live inside [notify]:
    neither caller could arrange it.

    MUTATION PIN. {!No_notify_fanout} deletes the loop at :38-40 and sends to a
    single registration, refuting conjunct A: the write resolves one handler and
    strands the other. No sibling repairs the stranded one, because [remove(key)]
    at :33 already took its sender out of the map before the send, so neither a
    duplicate [save_cert] (:144) nor another handler's re-read notify (:259)
    can find it - both re-enter [notify] and take the empty-key early return
    (:34-36). Both of those repair routes ARE in the model, and both are
    disabled by the same deletion, which is why the pin is real. On the real
    code the stranded receiver does not even fail quietly: the dropped sender
    turns [Registration::poll]'s [.expect("Sender never drops when registration
    is pending")] (:123) into a panic. *)
let s_2 =
  let conjunct_a =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom W1_reg, Formula.And (atom W2_reg, atom Possessed)),
           Formula.Af (Formula.And (atom W1_done, atom W2_done)) ))
  in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies
         (atom W1_reg, Formula.Not (Formula.K (Validator.V1, atom W2_reg))))
  in
  {
    name = "one-write-wakes-every-registered-parent-waiter";
    bucket = Statements.Fairness;
    formula = Formula.And (conjunct_a, conjunct_b);
    antecedent = Formula.And (atom W1_reg, atom W2_reg);
  }

(** S3 - certificate-is-store-visible-from-the-instant-its-write-notifies
    [safety].

    Conjunct A (certificate_store.rs:144 vs :183/:206, layered_db.rs:98,
    :383-389): there is no reachable state in which [save_cert] has run for d
    and [CertificateStore::read(d)] still answers [None]. The notify fires
    inside [save_cert], i.e. BEFORE the enclosing [txn.commit()], so any handler
    it wakes - and any handler that re-reads the store at
    certificate_store.rs:257, and any [contains]/[multi_contains] caller such as
    [get_missing_parents] (cert_manager.rs:158) - is reading a store that must
    already answer. What makes it answer is that [LayeredDbTxMut::insert] writes
    the mem layer first (:98) and [get] reads mem first (:383-389); the physical
    commit is still queued at that point and may stay queued indefinitely.

    Conjunct B (layered_db.rs:118-124, :162, :247-249, :463-495, :317-333): at
    every state where the store answers, V2 does not know the answer is durable.
    [commit]'s own doc comment says the data "may not be committed on-disk yet",
    [persist]/[sync_persist] are answered by a bare oneshot carrying nothing,
    and [LayeredDatabase::stats] is called by no consensus path - so a reader
    observes [Some]/[None] and no provenance whatever. Visibility is a logical
    property here, deliberately decoupled from durability.

    MUTATION PIN. {!No_mem_write_on_insert} deletes [self.mem_db.insert] from
    [LayeredDbTxMut::insert] (:98) and from its byte-identical sibling in
    [LayeredDatabase::insert] (:392), refuting conjunct A: it adds the states in
    which the notify has already fired while both layers still answer [None], so
    a woken handler's peers - and the re-read of certificate_store.rs:257 - see
    nothing. No third read source exists to repair it ([get] :383-389,
    [contains_key] :375-381, [is_empty] :412-418, [iter] :423-429 read exactly
    the two layers, with no retry and no re-fetch), [MemDatabase::get] returns
    [None] silently rather than erroring (mem_db.rs:145-147 via :12-21), the
    background thread's [insert_txn] (:210-219) writes into an uncommitted
    physical txn that a reader's separate read cannot see, and the sole
    re-population of the mem layer, [open_table]'s preload (:347-356), runs once
    at process start. The same deletion also collapses conjunct B, because
    visibility then coincides exactly with durability and V2's ignorance
    disappears - which is the sharpest statement of what the mem-first write
    buys. *)
let s_3 =
  let conjunct_a =
    Formula.Ag (Formula.Implies (atom Cert_written, atom Store_visible))
  in
  let conjunct_b =
    Formula.Ag
      (Formula.Implies
         ( atom Store_visible,
           Formula.Not (Formula.K (Validator.V2, atom Durable)) ))
  in
  {
    name = "certificate-is-store-visible-from-the-instant-its-write-notifies";
    bucket = Statements.Safety;
    formula = Formula.And (conjunct_a, conjunct_b);
    antecedent = atom Cert_written;
  }

(** The family's statements. *)
let all = [ s_1; s_2; s_3 ]

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
