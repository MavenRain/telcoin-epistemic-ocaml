(** The BATCH_PACK_SHARE statements over {!Batch_pack_share_model}: what one
    seal of one worker's batch guarantees about a single sender's share of it
    (S1, S2) and about where that sender's remainder sits afterwards (S3).

    {1 Reading guide for the K operands}

    Two knowledge agents, both with genuinely partial views:

    - {!Batch_pack_share_model.worker} = V0, the node that owns this pool. Its
      view carries its whole pool and its whole batch, so every fact about
      admission or packing is a projection of its own view and would be
      epistemically empty under [K]. V0 therefore appears only in IGNORANCE
      conjuncts, and only about the one fact its own pool provably does not hold:
      A's real balance. crates/batch-builder/src/batch.rs:132-139 hands the pool
      [balance: U256::MAX] with the in-tree comment "corrected by engine's
      canonical update" (:137), and the real figure arrives only with
      [process_canon_state_update] (crates/tn-reth/src/txn_pool.rs:191-199,
      [balance: acc.balance]). The model gives V0 a deliberately generous view -
      profile, stage, admitted count, sealed count, B's inclusion and the
      remainder's sub-pool label - which makes the ignorance claim harder to
      satisfy, not easier; it still holds, because at [Pool_synced] the pending
      label is identical whether or not A can pay.
    - {!Batch_pack_share_model.peer} = V1, a peer worker that received the
      broadcast batch. Its view is the batch and nothing else, because
      [validate_batch] (crates/batch-validator/src/validator.rs:39-82) checks
      digest, worker id, epoch, aggregate bytes, decodability, absence of blobs,
      aggregate gas and base fee, and consults no pool at any point. Both its
      claims are about a hidden possession - how many slots sender A occupies in
      {b V0's} pool - which no view of V1's carries.

    The single positive [K] is S2's [K_V1(|pool inter A| = S)]. It is not a
    projection of V1's own view: the batch tells V1 only that A has {b at least}
    [S] transactions in that pool; the upper half of the equality comes from the
    per-sender slot cap (crates/tn-reth/src/lib.rs:333-337, plumbed at
    crates/tn-reth/src/txn_pool.rs:87,98-99) and from nowhere else. It is not
    rigid either: the operand is false at every reachable [Solo] state, where A
    occupies one slot. And its class is not a singleton - at a [Flood] sealed
    state V1's class holds both hidden solvency branches and every later stage of
    the run - which test/t_batch_pack_share.ml asserts directly. Deleting the cap
    makes exactly that inference unsound, which is what pins S2.

    The ignorance conjuncts each have a concrete reachable witness pair, all
    asserted in the contingency group of test/t_batch_pack_share.ml:

    - [~K_V1(pool inter A \\ batch <> {})]: the [Heavy] sealed batch and the
      [Solo] sealed batch are the very same two transactions (A's nonce-0 gas-10
      and B's nonce-0 gas-5), yet in the first A still has two transactions stuck
      in V0's pool and in the second A has none. A peer cannot tell the two
      apart, so it cannot audit what the proposer left behind.
    - [~K_V0(balance(A) >= cost(next(A)))] and its negation: at a [Pool_synced]
      state with a remainder, the solvent and the insolvent run have byte-equal
      V0 views, because the synthetic [balance: U256::MAX] is what the pool
      believes in both.

    One positive [K] was considered and DROPPED: [Canon_applied /\ rest_pending
    -> K_V0(balance(A) >= cost(next(A)))]. It is true, but at that state V0's
    view class is a singleton - the canonical update makes the remainder's label
    a function of the solvency bit - so the knowledge would be trivially true and
    worthless (R2). The ignorance claim before the canonical update carries the
    whole content, and the repair step is still in the model as the reason S3 is
    scoped to [Pool_synced]. *)

open Batch_pack_share_model

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

(** S1 - gas-heavy-predecessor-starves-only-its-own-dependents [fairness].

    AG( sealed(w) /\ heavy -> b1 in sealed_batch(w) )
    /\ AG( sealed(w) /\ heavy -> ~(|sealed_batch(w) inter A| >= S) )
    /\ AG( pool(w) inter A \\ sealed_batch(w) <> {}
           -> ~K_V1( pool(w) inter A \\ sealed_batch(w) <> {} ) )

    Within one seal, a transaction whose gas limit does not fit the remaining
    budget is skipped and packing continues, so a transaction ordered {b behind}
    it still lands in the batch: crates/batch-builder/src/batch.rs:73-81 ends the
    over-budget arm with [continue], not [break], after notifying the iterator
    via [best_txs.exceeds_gas_limit(&pool_tx, gas_limit)]
    (crates/tn-reth/src/txn_pool.rs:331-336). The first conjunct says exactly
    that for sender B's transaction in the [heavy] profile, where A's second
    offer (gas 35) cannot fit beside anything.

    The second conjunct is the honest other half, and it is the reason this
    statement is not true by omission. [exceeds_gas_limit] is [mark_invalid], and
    the repo's own comment at batch.rs:74-77 states its scope: "all dependents for
    this transaction are now considered invalid before continuing loop". A's
    third offer (gas 5) would have fitted the remaining budget perfectly, and it
    is dropped anyway, because it is a dependent of the transaction that was
    skipped. Head-of-line blocking is eliminated {b across} senders and preserved
    {b within} one. The model runs that invalidation, so the first conjunct is
    stated over a packing loop that really does drop the successors.

    The third conjunct is what the discipline costs in auditability: the batch a
    peer receives in the [heavy] profile is the very same pair of transactions it
    receives in the [solo] profile, where nothing was left behind, and
    crates/batch-validator/src/validator.rs:39-82 gives it nothing else to go on.
    The proposer's fairness is not verifiable by the validators.

    Mutation pin: [Break_on_over_budget] (batch.rs:80, [continue] -> [break])
    refutes conjuncts one and three. It removes the transition in which packing
    resumes past the gas-heavy transaction, so B's transaction is dropped; and it
    makes the resulting batch observably different from the [solo] batch, which
    hands V1 the knowledge the third conjunct denies it. No sibling path repairs
    it within one seal: the loop at batch.rs:71-119 is the only place a
    transaction is appended, [mark_invalid] never touches the pool, the byte gate
    at batch.rs:97-105 is an independent condition rather than a second admission
    route, and the only pool-mutating call in the build path
    ([remove_eip4844_txs], batch.rs:126 -> txn_pool.rs:305-308) is blob-only. The
    builder does rebuild from the pool on the next seal (lib.rs:262-350), a
    partial repair {b across} seals - which is why every conjunct here is about
    the composition of this one sealed batch, which no later seal can change. *)
let s_1 =
  let fitting_other_sender_gets_in =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Batch_sealed, atom Heavy_offer),
           atom B_in_batch ))
  in
  let own_dependents_are_still_dropped =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Batch_sealed, atom Heavy_offer),
           Formula.Not (atom Batch_takes_cap_many_of_a) ))
  in
  let peers_cannot_audit_the_leftovers =
    Formula.Ag
      (Formula.Implies
         ( atom A_left_unsealed,
           Formula.Not (Formula.K (peer, atom A_left_unsealed)) ))
  in
  {
    name = "gas-heavy-predecessor-starves-only-its-own-dependents";
    bucket = Statements.Fairness;
    formula =
      Formula.conj
        [
          fitting_other_sender_gets_in;
          own_dependents_are_still_dropped;
          peers_cannot_audit_the_leftovers;
        ];
    antecedent = Formula.And (atom Batch_sealed, atom Heavy_offer);
  }

(** S2 - per-sender-slot-cap-bounds-a-share-and-makes-occupancy-peer-inferable
    [security].

    AG( |pool(w) inter A| <= S )
    /\ AG( sealed(w) /\ flood -> b1 in sealed_batch(w) )
    /\ AG( sealed(w) /\ |sealed_batch(w) inter A| >= S
           -> K_V1( |pool(w) inter A| = S ) )

    The pool admits at most [S] pending transactions per account -
    crates/tn-reth/src/lib.rs:333-337 sets [txpool.max_account_slots = 256]
    ("TN default: 256 slots per sender (Reth default is 16)") and
    crates/tn-reth/src/txn_pool.rs:87,98-99 plumbs [node_config.txpool
    .pool_config()] into [Pool::eth_pool]. Because the batch is drawn straight
    from the pending sub-pool (crates/batch-builder/src/batch.rs:56), that bound
    is the only thing on the whole batch path that limits one account's share:
    the packing loop keeps no per-sender counter (batch.rs:62-67, 108-118 track
    only [total_possible_gas], [total_bytes_size] and [sender_nonces]), and a
    peer's [validate_batch] (crates/batch-validator/src/validator.rs:39-82) has no
    per-sender count either - its byte and gas bounds are aggregate
    (:122-141, :162-185). The second conjunct is the consequence that matters:
    with four offers of gas 10 against a budget of 40, sender A takes the whole
    batch and B is squeezed out - unless the cap has already trimmed A to [S].

    The third conjunct is the epistemic half. A peer that sees [S] transactions
    of one sender in a batch learns that the sender is {b exactly} at its
    admission bound in a pool it cannot see. The lower half of that equality is
    read off the batch; the upper half comes from the cap and from nothing else.
    So the cap does not only bound a share, it is what makes a peer's inference
    about a proposer's pool occupancy sound.

    Mutation pin: [No_per_sender_slot_cap] (txn_pool.rs:87,98-99) refutes all
    three conjuncts. Admission then takes all four of A's offers, which (i)
    breaks the invariant, (ii) exhausts the gas budget before B's transaction is
    reached, and (iii) makes the peer's inference unsound - the batch still shows
    [S] or more of A's transactions while A in fact occupies more slots than
    that. No sibling path repairs it: there is no second per-identity bound
    anywhere - not in the packing loop, not in batch validation, not in the
    gossip ingress (validator.rs:89-106 routes by sender but imposes no quota),
    and reth's own network limits are all zeroed out
    (crates/tn-reth/src/lib.rs:344-392). *)
let s_2 =
  let cap_is_an_invariant = Formula.Ag (atom A_admission_within_cap) in
  let a_flood_cannot_take_the_whole_batch =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Batch_sealed, atom Flood_offer),
           atom B_in_batch ))
  in
  let peers_inference_about_occupancy_is_sound =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Batch_sealed, atom Batch_takes_cap_many_of_a),
           Formula.K (peer, atom A_admission_at_cap) ))
  in
  {
    name = "per-sender-slot-cap-bounds-a-share-and-makes-occupancy-peer-inferable";
    bucket = Statements.Security;
    formula =
      Formula.conj
        [
          cap_is_an_invariant;
          a_flood_cannot_take_the_whole_batch;
          peers_inference_about_occupancy_is_sound;
        ];
    antecedent = Formula.And (atom Batch_sealed, atom Flood_offer);
  }

(** S3 - post-seal-nonce-hint-keeps-a-remainder-pending-without-knowing-it-can-pay
    [safety].

    AG( pool_synced(w) /\ pool(w) inter A \\ sealed_batch(w) <> {}
        -> subpool(rest(A)) = pending )
    /\ AG( pool_synced(w) /\ pool(w) inter A \\ sealed_batch(w) <> {}
        -> ~K_V0( balance(A) >= cost(next(A)) )
           /\ ~K_V0( ~(balance(A) >= cost(next(A))) ) )

    When the seal's mined hashes are handed to the pool the sender's remaining
    transactions would look like a nonce gap, so the builder accumulates the
    per-sender maximum nonce (crates/batch-builder/src/batch.rs:115-118) and ships
    a synthetic account advance with it: batch.rs:128-139 builds
    [ChangedAccount { address, nonce: max_nonce + 1, balance: U256::MAX }], and
    batch.rs:26-30 states the purpose verbatim - "Keeps remaining transactions
    from the same sender in the pending sub-pool rather than being demoted to
    queued due to a perceived nonce gap". Both halves travel in the one
    [CanonicalStateUpdate] built at crates/tn-reth/src/txn_pool.rs:146-168, and
    lib.rs:320-332 sends it only after the quorum waiter acked - a refused quorum
    returns empty vectors and lib.rs:309-316 applies no pool change at all. The
    first conjunct is the guarantee: the sender's queue drains at batch rate
    rather than one transaction per consensus round.

    The second conjunct is the price. The balance in that hint is a deliberate
    falsehood, flagged as such in tree: "corrected by engine's canonical update"
    (batch.rs:137) and "`balance: U256::MAX` only affects whether the pool demotes
    accounts after mining the batch" (batch.rs:130-131). So at the moment the
    remainder is kept pending, the worker does not know - and cannot know from
    anything in its pool - whether the sender can still pay for it. The real
    figure arrives only with [process_canon_state_update]
    (crates/tn-reth/src/txn_pool.rs:183-217), which recomputes [changed_accounts]
    from committed state with [balance: acc.balance] (:191-199), a full consensus
    round later; that step is the [Canon_seen] transition of this model, and it is
    where a solvent and an insolvent sender finally part company.

    Mutation pin: [No_post_seal_nonce_hint] (batch.rs:128-139 returning an empty
    vector) refutes the first conjunct - the mined hashes still reach the pool, the
    advance does not, and the remainder is demoted to queued. The one genuine
    repair is [process_canon_state_update], and it IS in this model, as the step
    after [Pool_synced]; the statement is scoped to [Pool_synced] precisely
    because that repair is a round late, and under the mutation the [Canon_seen]
    state does return the remainder to pending. [set_block_info]
    (txn_pool.rs:224-227) carries no account data and nothing else re-promotes a
    queued transaction. The second conjunct is unaffected by the mutation - the
    demotion is identical in both solvency branches - and is pinned by nothing;
    it is asserted here because it is the epistemic content of the [U256::MAX]
    hint, and its witness pair is asserted directly in the contingency group. *)
let s_3 =
  let operative =
    Formula.And (atom Pool_synced_now, atom A_left_unsealed)
  in
  let remainder_stays_pending =
    Formula.Ag (Formula.Implies (operative, atom A_rest_pending))
  in
  let solvency_is_hidden_while_it_does =
    Formula.Ag
      (Formula.Implies
         ( operative,
           Formula.And
             ( Formula.Not (Formula.K (worker, atom A_funded)),
               Formula.Not (Formula.K (worker, Formula.Not (atom A_funded))) )
         ))
  in
  {
    name =
      "post-seal-nonce-hint-keeps-a-remainder-pending-without-knowing-it-can-pay";
    bucket = Statements.Safety;
    formula =
      Formula.conj [ remainder_stays_pending; solvency_is_hidden_while_it_does ];
    antecedent = operative;
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
