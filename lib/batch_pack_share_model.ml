(** BATCH_PACK_SHARE - the anti-monopolisation surface around ONE seal of ONE
    worker's batch in telcoin-network: who gets into the batch, how much of it a
    single sender may take, and where that sender's remainder sits afterwards.

    {1 The mechanism}

    A worker's batch builder polls its own reth transaction pool and, when the
    pending sub-pool is non-empty (crates/batch-builder/src/lib.rs:264-280),
    spawns one build task (:145-231). The build itself is
    [build_batch] (crates/batch-builder/src/batch.rs:44-143):

    - budgets are protocol constants read at batch.rs:50-51 -
      [max_batch_gas(epoch) = 30_000_000] and [max_batch_size(epoch) = 1_000_000]
      (crates/types/src/worker/sealed_batch.rs:190-200);
    - the packing loop walks [pool.best_transactions()] (batch.rs:56, 71). The gas
      gate is batch.rs:73-81: when [total_possible_gas + pool_tx.gas_limit() >
      gas_limit] it calls [best_txs.exceeds_gas_limit(&pool_tx, gas_limit)] and
      then [continue] - {b not} [break]. The byte gate at batch.rs:97-105 is the
      structurally identical twin;
    - [exceeds_gas_limit] (crates/tn-reth/src/txn_pool.rs:331-336) is
      [mark_invalid] on the [BestTransactions] iterator held for {b this} seal
      (txn_pool.rs:312-314, 355-361), so the skipped transaction survives in the
      pool. It is however NOT free: the repo's own comment at batch.rs:74-77 says
      "all dependents for this transaction are now considered invalid before
      continuing loop", i.e. the skipped sender's own higher-nonce transactions
      are dropped from this iteration too. That asymmetry - a different sender is
      unaffected, the same sender's successors are not - is modelled here and is
      asserted, not omitted;
    - after the loop the builder accumulates the per-sender maximum nonce
      (batch.rs:115-118) and turns it into [changed_accounts] at batch.rs:128-139
      with [nonce: max_nonce + 1] and a deliberately false [balance: U256::MAX]
      ("corrected by engine's canonical update", batch.rs:130-131,137). The
      purpose is spelled out at batch.rs:26-30: "Keeps remaining transactions
      from the same sender in the pending sub-pool rather than being demoted to
      queued due to a perceived nonce gap";
    - the update is applied only after the worker's quorum waiter acks
      (lib.rs:178-217). On [QuorumRejected | AntiQuorum | Timeout | NotValidator
      | FailedToReport | FailedQuorum] the task returns empty vectors and
      lib.rs:309-316 skips the pool update entirely: "this will apply no changes
      to transaction pool". On success lib.rs:320-332 calls
      [update_canonical_state] -> txn_pool.rs:146-168, which builds a
      [CanonicalStateUpdate] carrying BOTH the mined hashes and the synthetic
      [changed_accounts];
    - one consensus round later the engine's own canonical update arrives and
      [process_canon_state_update] (txn_pool.rs:183-217) recomputes
      [changed_accounts] from {b committed} state, with the {b real}
      [balance: acc.balance] (:191-199). That is the repair path for the
      synthetic hint, and it is modelled here as the [Canon_seen] step.

    The only per-identity quota anywhere on this path is the pool's per-account
    slot bound: crates/tn-reth/src/lib.rs:333-337 raises it from reth's default
    to 256 ("TN default: 256 slots per sender (Reth default is 16)"), and
    crates/tn-reth/src/txn_pool.rs:87,98-99 plumbs [node_config.txpool
    .pool_config()] into [Pool::eth_pool]. Nothing downstream re-imposes a
    per-sender bound: the packing loop tracks only [total_possible_gas],
    [total_bytes_size] and [sender_nonces] (batch.rs:62-67,108-118), and a peer's
    [validate_batch] (crates/batch-validator/src/validator.rs:39-82) checks
    digest, worker id, epoch, aggregate bytes (:122-141), decodability (:147-156),
    absence of blobs (:198-206), aggregate gas (:162-185) and base fee (:188-195)
    - and nothing per sender. The gossip ingress routes by sender without any
    quota (validator.rs:89-106) and reth's own networking limits are all zeroed
    (crates/tn-reth/src/lib.rs:344-392).

    {1 Components}

    - [profile]: what the two senders offer this run. A is the would-be
      monopolist, B the competing account. Gas figures are the real budget
      [max_batch_gas] scaled to 40 abstract units, and the real per-sender slot
      cap 256 scaled to [slot_cap] = 3; the scale is arbitrary, the ORDER of the
      quantities is what the statements range over.
    - [funding]: the hidden fact the [balance: U256::MAX] hint conceals - whether
      A's real balance, after the seal has spent it, still covers A's next
      transaction. Invisible to the pool until the engine's canonical update
      supplies [acc.balance].
    - [stage]: the one-seal pipeline - offers submitted, admission run, batch
      built and broadcast, quorum acked or refused, pool synced with the seal's
      hint, engine canonical update seen.
    - [a_admitted] / [a_sealed] / [b_sealed]: how many of A's offers the pool
      took, how many of them the seal took, whether B's transaction was taken.
    - [remainder]: the sub-pool label of A's admitted-but-unsealed transactions.

    {1 Role mapping}

    - {b V0 = the worker} that owns this pool and builds this batch. Its view is
      (profile, stage, [a_admitted], [a_sealed], [b_sealed], [remainder]) - it
      sees every submission it received, everything it admitted, its own batch
      and its own sub-pool labels. It does NOT see [funding]: that is exactly
      what batch.rs:137 replaces with [U256::MAX]. Deliberately generous: V0 is
      given more sight than strictly required, because the only V0 claims here
      are IGNORANCE claims, and a larger view makes them harder, not easier.
    - {b V1 = a peer worker} that receives the broadcast batch and runs
      [validate_batch]. Its view is the batch it received and nothing else: the
      per-sender transaction count and gas of the batch. It does NOT see V0's
      pool, V0's admission decisions or V0's stage, because validator.rs:39-82
      never consults any pool and no field of [Batch]
      (crates/types/src/worker/sealed_batch.rs) carries one. The observation is
      NOT artificially coarse: in the [Solo] and [Heavy] runs the sealed batch is
      the very same two transactions (A's nonce-0, gas 10, and B's nonce-0,
      gas 5), so no finer projection could separate them either.
    - {b V2 .. V9 = idle}: constant blank view, never appearing under [K].

    {1 Scope}

    Deliberately ONE seal. Across seals the pool is re-read (lib.rs:262-350) and a
    gas-skipped transaction is re-offered, which is a partial repair for the
    packing statement; the statements are therefore about the composition of a
    single sealed batch, which no later seal can change. *)

(** The batch gas budget, [max_batch_gas(epoch) = 30_000_000]
    (crates/types/src/worker/sealed_batch.rs:190-194) scaled to 40 units. *)
let gas_budget = 40

(** The per-sender pool slot bound, [txpool.max_account_slots = 256]
    (crates/tn-reth/src/lib.rs:333-337) scaled to 3 slots. *)
let slot_cap = 3

(** Which transactions the two senders offer worker V0 in this run. A run's
    profile is fixed at the initial state: it is what the clients submitted. *)
type profile
  = Solo
      (** A offers a single transaction (gas 10); B offers one (gas 5). Nothing
          is ever left behind, and the sealed batch is byte-identical to the
          {!Heavy} one - which is what makes V1's ignorance real. *)
  | Heavy
      (** A offers three in nonce order - gas 10, then a gas-35 transaction that
          cannot fit beside anything, then gas 5; B offers one (gas 5). The
          middle transaction trips the batch.rs:73-81 gas gate. *)
  | Flood
      (** A offers four transactions of gas 10; B offers one of gas 10. Four
          would exactly exhaust the budget, so this is the monopolisation
          attempt the slot cap is the only defence against. *)

(** Total order index for {!profile}. *)
let profile_index p = match p with Solo -> 0 | Heavy -> 1 | Flood -> 2

(** Total order on {!profile}. *)
let profile_compare a b = Int.compare (profile_index a) (profile_index b)

(** A's gas limits, in nonce order, for a profile (batch.rs:73 reads
    [pool_tx.gas_limit()]). *)
let a_offer_gas p =
  match p with
  | Solo -> [ 10 ]
  | Heavy -> [ 10; 35; 5 ]
  | Flood -> [ 10; 10; 10; 10 ]

(** B's single transaction's gas limit for a profile. *)
let b_offer_gas p = match p with Solo -> 5 | Heavy -> 5 | Flood -> 10

(** The first [n] elements of [l], built with a filter rather than a loop. *)
let prefix n l = List.filteri (fun i _ -> i < n) l

(** Whether A's real balance, after this seal has spent it, still covers A's
    next transaction. Hidden from the pool: batch.rs:137 hands the pool
    [balance: U256::MAX] instead ("corrected by engine's canonical update"). *)
type funding
  = Funded  (** A can still pay for its remaining transaction. *)
  | Short  (** A cannot; the engine's canonical update will demote it. *)

(** Total order index for {!funding}. *)
let funding_index f = match f with Funded -> 0 | Short -> 1

(** Total order on {!funding}. *)
let funding_compare a b = Int.compare (funding_index a) (funding_index b)

(** The one-seal pipeline of crates/batch-builder/src/lib.rs:145-350. *)
type stage
  = Offering  (** clients have submitted; pool admission has not run *)
  | Admitted  (** the pool has applied its per-sender slot bound *)
  | Sealed
      (** [build_batch] ran and [to_worker.send((batch, ack))] (lib.rs:165-175)
          put the sealed batch in front of the peers *)
  | Quorum_reached  (** the quorum waiter acked [Ok] (lib.rs:182-190) *)
  | Quorum_failed
      (** the waiter reported anti-quorum/timeout/rejection, so the task
          returned empty vectors and lib.rs:309-316 applies NO pool change *)
  | Pool_synced
      (** [update_canonical_state] (lib.rs:320-332 -> txn_pool.rs:146-168) has
          removed the mined hashes and applied the seal's synthetic
          [changed_accounts] *)
  | Canon_seen
      (** the engine's own canonical update has been processed
          (txn_pool.rs:183-217), replacing the synthetic account entry with the
          committed [nonce]/[balance] *)

(** Total order index for {!stage}. *)
let stage_index s =
  match s with
  | Offering -> 0
  | Admitted -> 1
  | Sealed -> 2
  | Quorum_reached -> 3
  | Quorum_failed -> 4
  | Pool_synced -> 5
  | Canon_seen -> 6

(** Total order on {!stage}. *)
let stage_compare a b = Int.compare (stage_index a) (stage_index b)

(** Has the batch been built and broadcast yet. *)
let sealed_yet s =
  match s with
  | Offering | Admitted -> false
  | Sealed | Quorum_reached | Quorum_failed | Pool_synced | Canon_seen -> true

(** Has the worker been told the batch reached quorum. *)
let quorum_yet s =
  match s with
  | Offering | Admitted | Sealed | Quorum_failed -> false
  | Quorum_reached | Pool_synced | Canon_seen -> true

(** The sub-pool label of A's admitted-but-unsealed transactions. *)
type remainder
  = Rest_absent  (** A has nothing left in the pool *)
  | Rest_pending  (** the remainder is in the pending sub-pool *)
  | Rest_queued
      (** the remainder was demoted to the queued sub-pool because the pool
          perceives a nonce gap (batch.rs:26-30) or, after the canonical
          update, because A cannot pay *)

(** Total order index for {!remainder}. *)
let remainder_index r =
  match r with Rest_absent -> 0 | Rest_pending -> 1 | Rest_queued -> 2

(** Total order on {!remainder}. *)
let remainder_compare a b = Int.compare (remainder_index a) (remainder_index b)

(** The joint global state of one seal. *)
type state = {
  profile : profile;  (** what the two senders offered *)
  funding : funding;  (** the hidden post-seal solvency of A *)
  stage : stage;  (** where in the one-seal pipeline this run is *)
  a_admitted : int;  (** how many of A's offers the pool holds *)
  a_sealed : int;  (** how many of them this batch took *)
  b_sealed : bool;  (** whether B's transaction is in this batch *)
  remainder : remainder;  (** sub-pool label of A's unsealed remainder *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = profile_compare s1.profile s2.profile in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = funding_compare s1.funding s2.funding in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = stage_compare s1.stage s2.stage in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Int.compare s1.a_admitted s2.a_admitted in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Int.compare s1.a_sealed s2.a_sealed in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Bool.compare s1.b_sealed s2.b_sealed in
            if Bool.not (Int.equal c5 0) then c5
            else remainder_compare s1.remainder s2.remainder

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** What a peer worker can observe of a broadcast batch: the per-sender
    transaction count and gas total it can read off the encoded transactions
    (crates/batch-validator/src/validator.rs:63-81 decodes exactly this much and
    consults no pool). *)
type peer_obs
  = Obs_no_batch  (** nothing has been broadcast to this peer yet *)
  | Obs_batch of int * int * int * int
      (** [(a_count, a_gas, b_count, b_gas)] of the received batch *)

(** Total order on {!peer_obs}; every constructor pair spelled. *)
let peer_obs_compare a b =
  match (a, b) with
  | Obs_no_batch, Obs_no_batch -> 0
  | Obs_no_batch, Obs_batch _ -> -1
  | Obs_batch _, Obs_no_batch -> 1
  | Obs_batch (c1, g1, d1, h1), Obs_batch (c2, g2, d2, h2) ->
      let c = Int.compare c1 c2 in
      if Bool.not (Int.equal c 0) then c
      else
        let ca = Int.compare g1 g2 in
        if Bool.not (Int.equal ca 0) then ca
        else
          let cb = Int.compare d1 d2 in
          if Bool.not (Int.equal cb 0) then cb else Int.compare h1 h2

(** A validator's local view. V0 sees its own pool and its own batch but never
    A's real balance; V1 sees the broadcast batch and nothing else; V2 and V3
    are idle. *)
type view
  = View_worker of profile * stage * int * int * bool * remainder
      (** V0: (offers received, pipeline stage, admitted count, sealed count,
          B taken, remainder label) *)
  | View_peer of peer_obs  (** V1: the received batch, or nothing yet *)
  | View_idle  (** the constant blank view of the non-agents V2, V3 *)

(** Total order on the V0 view payload. *)
let view_worker_compare (p1, st1, ad1, se1, bs1, r1) (p2, st2, ad2, se2, bs2, r2)
    =
  let c = profile_compare p1 p2 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = stage_compare st1 st2 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Int.compare ad1 ad2 in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Int.compare se1 se2 in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare bs1 bs2 in
          if Bool.not (Int.equal c4 0) then c4 else remainder_compare r1 r2

(** Total order on views: every constructor pair spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | ( View_worker (p1, st1, ad1, se1, bs1, r1),
      View_worker (p2, st2, ad2, se2, bs2, r2) ) ->
      view_worker_compare (p1, st1, ad1, se1, bs1, r1)
        (p2, st2, ad2, se2, bs2, r2)
  | View_worker _, (View_peer _ | View_idle) -> -1
  | (View_peer _ | View_idle), View_worker _ -> 1
  | View_peer o1, View_peer o2 -> peer_obs_compare o1 o2
  | View_peer _, View_idle -> -1
  | View_idle, View_peer _ -> 1
  | View_idle, View_idle -> 0

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** The worker that owns this pool and builds this batch: the acting knowledge
    agent whose view omits A's real balance. *)
let worker = Validator.V0

(** A peer worker that receives the broadcast batch and validates it: the second
    knowledge agent, whose view is the batch and nothing else. *)
let peer = Validator.V1

(** Gate deletion for the confirm-by-mutation test. *)
type mutation
  = Pristine  (** the code as written at 0c59c15b *)
  | Break_on_over_budget
      (** crates/batch-builder/src/batch.rs:80 - replace the [continue] of the
          gas gate (batch.rs:73-81) with a [break]. Removes the transitions in
          which packing resumes after an over-budget transaction and adds the
          transition that seals immediately at the first one, so a transaction
          ordered behind a gas-heavy predecessor is dropped even when it fits.
          No sibling path repairs it {b within this seal}: the loop at
          batch.rs:71-119 is the only place a transaction is appended;
          [exceeds_gas_limit] (crates/tn-reth/src/txn_pool.rs:331-336) is
          [mark_invalid] on the iterator and never re-admits anything; the byte
          gate (batch.rs:97-105) is an independent condition, not a second
          admission route; and the only pool-mutating call in the build path,
          [pool.remove_eip4844_txs] (batch.rs:126 ->
          crates/tn-reth/src/txn_pool.rs:305-308), is blob-only. Across seals
          the builder does re-read the pool (lib.rs:262-350), which is why every
          statement pinned by this mutation is about the composition of ONE
          sealed batch, which no later seal can alter. *)
  | No_per_sender_slot_cap
      (** crates/tn-reth/src/txn_pool.rs:87,98-99 - drop
          [node_config.txpool.pool_config()] and admit every offer, i.e. neutralise
          the [max_account_slots = 256] bound set at
          crates/tn-reth/src/lib.rs:333-337. Adds the admission transitions in
          which one sender occupies more than [slot_cap] pending slots and
          therefore more of the batch. Nothing repairs it: the packing loop keeps
          no per-sender counter (batch.rs:62-67, 108-118 accumulate only gas,
          bytes and max nonce), a peer's [validate_batch]
          (crates/batch-validator/src/validator.rs:39-82, with :122-141, :162-185
          aggregate-only) has no per-sender count, the gossip ingress routes by
          sender but imposes no quota (validator.rs:89-106), and reth's own
          network limits are zeroed out (crates/tn-reth/src/lib.rs:344-392,
          [max_concurrent_tx_requests: 0], [disable_tx_gossip: true]). *)
  | No_post_seal_nonce_hint
      (** crates/batch-builder/src/batch.rs:128-139 - return an empty
          [changed_accounts] instead of [{ address; nonce: max_nonce + 1;
          balance: U256::MAX }]. The mined hashes still travel to the pool
          (lib.rs:326-332), so removing them without the accompanying nonce
          advance leaves a perceived gap and demotes the sender's remainder to
          the queued sub-pool - the consequence batch.rs:26-30 documents
          verbatim. The only other supplier of an account advance is
          [process_canon_state_update] (crates/tn-reth/src/txn_pool.rs:183-217),
          which derives [changed_accounts] from COMMITTED state (:191-199) and so
          arrives a full consensus round later; it is modelled here as the
          [Canon_seen] step and does repair the demotion - one step later, which
          is precisely why the pinned statement is scoped to [Pool_synced].
          [set_block_info] (txn_pool.rs:224-227) carries no account data, and
          nothing else re-promotes a queued transaction. *)

(** How many of A's offers the pool admits: bounded by {!slot_cap} unless the
    bound has been deleted. *)
let admitted_count mut p =
  let offered = List.length (a_offer_gas p) in
  match mut with
  | Pristine | Break_on_over_budget | No_post_seal_nonce_hint ->
      if offered > slot_cap then slot_cap else offered
  | No_per_sender_slot_cap -> offered

(** Which sender a queue entry belongs to. *)
type sender
  = Sender_a  (** the would-be monopolist *)
  | Sender_b  (** the competing account *)

(** The state of the packing loop (batch.rs:71-119) part-way through. *)
type pack = {
  pk_used : int;  (** [total_possible_gas] so far *)
  pk_taken_a : int;  (** how many of A's transactions were appended *)
  pk_taken_b : bool;  (** whether B's transaction was appended *)
  pk_a_dead : bool;
      (** an earlier A transaction was [mark_invalid]ed, so batch.rs:74-77 has
          declared all of A's dependents invalid for this iteration *)
  pk_halted : bool;  (** the mutated [break] fired *)
}

(** What the gas gate does to a sender-A entry that does not fit. *)
let over_budget_a mut acc =
  match mut with
  | Break_on_over_budget -> { acc with pk_halted = true }
  | Pristine | No_per_sender_slot_cap | No_post_seal_nonce_hint ->
      { acc with pk_a_dead = true }

(** What the gas gate does to the sender-B entry when it does not fit. B offers
    a single transaction, so there are no B dependents to invalidate. *)
let over_budget_b mut acc =
  match mut with
  | Break_on_over_budget -> { acc with pk_halted = true }
  | Pristine | No_per_sender_slot_cap | No_post_seal_nonce_hint -> acc

(** One iteration of the packing loop over one queue entry. *)
let pack_step mut acc entry =
  let sender, gas = entry in
  if acc.pk_halted then acc
  else
    match sender with
    | Sender_a ->
        if acc.pk_a_dead then acc
        else if acc.pk_used + gas > gas_budget then over_budget_a mut acc
        else
          {
            acc with
            pk_used = acc.pk_used + gas;
            pk_taken_a = acc.pk_taken_a + 1;
          }
    | Sender_b ->
        if acc.pk_used + gas > gas_budget then over_budget_b mut acc
        else { acc with pk_used = acc.pk_used + gas; pk_taken_b = true }

(** The pending queue [best_transactions] hands the builder: A's admitted
    transactions in nonce order, then B's. A ahead of B is the adversarial
    ordering for the fairness claims, so it is the honest one to state them
    against. *)
let pack_queue p admitted =
  List.map (fun g -> (Sender_a, g)) (prefix admitted (a_offer_gas p))
  @ [ (Sender_b, b_offer_gas p) ]

(** Run the whole packing loop for one seal. *)
let pack_batch mut p admitted =
  List.fold_left (pack_step mut)
    {
      pk_used = 0;
      pk_taken_a = 0;
      pk_taken_b = false;
      pk_a_dead = false;
      pk_halted = false;
    }
    (pack_queue p admitted)

(** The sub-pool label of A's remainder before the post-seal pool update:
    everything the pool admitted is pending. *)
let rest_before_sync admitted sealed =
  if admitted > sealed then Rest_pending else Rest_absent

(** The sub-pool label after [update_canonical_state] with the seal's hint. With
    the hint the remainder's nonce is exactly the advertised next nonce and it
    stays pending (batch.rs:26-30); without it the pool sees a gap. *)
let rest_after_sync mut admitted sealed =
  if admitted > sealed then
    match mut with
    | No_post_seal_nonce_hint -> Rest_queued
    | Pristine | Break_on_over_budget | No_per_sender_slot_cap -> Rest_pending
  else Rest_absent

(** The sub-pool label after the engine's canonical update, which replaces the
    synthetic entry with the committed nonce and the REAL balance
    (txn_pool.rs:191-199). This is where A's solvency stops being hidden. *)
let rest_after_canon f admitted sealed =
  if admitted > sealed then
    match f with Funded -> Rest_pending | Short -> Rest_queued
  else Rest_absent

(** The transition relation: the one-seal pipeline advances one stage at a time;
    the only branch is the quorum waiter's verdict. *)
let next_with mut s =
  match s.stage with
  | Offering ->
      let admitted = admitted_count mut s.profile in
      [
        {
          s with
          stage = Admitted;
          a_admitted = admitted;
          remainder = rest_before_sync admitted 0;
        };
      ]
  | Admitted ->
      let p = pack_batch mut s.profile s.a_admitted in
      [
        {
          s with
          stage = Sealed;
          a_sealed = p.pk_taken_a;
          b_sealed = p.pk_taken_b;
          remainder = rest_before_sync s.a_admitted p.pk_taken_a;
        };
      ]
  | Sealed ->
      [ { s with stage = Quorum_reached }; { s with stage = Quorum_failed } ]
  | Quorum_reached ->
      [
        {
          s with
          stage = Pool_synced;
          remainder = rest_after_sync mut s.a_admitted s.a_sealed;
        };
      ]
  | Quorum_failed -> []
  | Pool_synced ->
      [
        {
          s with
          stage = Canon_seen;
          remainder = rest_after_canon s.funding s.a_admitted s.a_sealed;
        };
      ]
  | Canon_seen -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** A fresh run: clients have submitted, nothing admitted, nothing sealed. *)
let start p f =
  {
    profile = p;
    funding = f;
    stage = Offering;
    a_admitted = 0;
    a_sealed = 0;
    b_sealed = false;
    remainder = Rest_absent;
  }

(** A offers one transaction and can still pay afterwards. *)
let initial_solo_funded = start Solo Funded

(** A offers one transaction and cannot pay afterwards. *)
let initial_solo_short = start Solo Short

(** A offers a gas-heavy middle transaction and can still pay afterwards. This
    is the reference initial state {!initial}. *)
let initial_heavy_funded = start Heavy Funded

(** A offers a gas-heavy middle transaction and cannot pay afterwards. *)
let initial_heavy_short = start Heavy Short

(** A floods four transactions and can still pay afterwards. *)
let initial_flood_funded = start Flood Funded

(** A floods four transactions and cannot pay afterwards. *)
let initial_flood_short = start Flood Short

(** The reference initial state required by the shared wiring: the gas-heavy
    profile with a solvent sender. *)
let initial = initial_heavy_funded

(** Every initial state: the three submission profiles crossed with the hidden
    solvency bit. Both dimensions are genuine client-side choices, so all six
    are roots. *)
let all_initials =
  [
    initial_solo_funded;
    initial_solo_short;
    initial_heavy_funded;
    initial_heavy_short;
    initial_flood_funded;
    initial_flood_short;
  ]

(** The atom vocabulary this family's statements quantify over. *)
type atom
  = Solo_offer  (** profile(run) = solo *)
  | Heavy_offer  (** profile(run) = heavy *)
  | Flood_offer  (** profile(run) = flood *)
  | Batch_sealed  (** sealed(w): the batch is built and broadcast *)
  | B_in_batch  (** b1 in sealed_batch(w) *)
  | Batch_takes_cap_many_of_a
      (** the sealed batch carries at least [slot_cap] of A's transactions -
          a quantity a peer reads straight off the batch *)
  | A_admission_at_cap  (** |pool(w) inter A| = slot_cap: A is exactly at its bound *)
  | A_admission_within_cap  (** |pool(w) inter A| <= slot_cap *)
  | A_left_unsealed
      (** after the seal, A has admitted transactions this batch did not take *)
  | Pool_synced_now  (** update_canonical_state with the seal's hint just ran *)
  | A_rest_pending  (** A's remainder is in the pending sub-pool *)
  | A_funded  (** the hidden fact: A can still pay for its remainder *)
  | Quorum_acked  (** the worker was told the batch reached quorum *)
  | Canon_applied  (** the engine's canonical update has been processed *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Solo_offer -> ( match s.profile with Solo -> true | Heavy | Flood -> false)
  | Heavy_offer -> (
      match s.profile with Heavy -> true | Solo | Flood -> false)
  | Flood_offer -> (
      match s.profile with Flood -> true | Solo | Heavy -> false)
  | Batch_sealed -> sealed_yet s.stage
  | B_in_batch -> s.b_sealed
  | Batch_takes_cap_many_of_a -> s.a_sealed >= slot_cap
  | A_admission_at_cap -> Int.equal s.a_admitted slot_cap
  | A_admission_within_cap -> s.a_admitted <= slot_cap
  | A_left_unsealed -> sealed_yet s.stage && s.a_admitted > s.a_sealed
  | Pool_synced_now -> (
      match s.stage with
      | Pool_synced -> true
      | Offering | Admitted | Sealed | Quorum_reached | Quorum_failed
      | Canon_seen ->
          false)
  | A_rest_pending -> (
      match s.remainder with
      | Rest_pending -> true
      | Rest_absent | Rest_queued -> false)
  | A_funded -> ( match s.funding with Funded -> true | Short -> false)
  | Quorum_acked -> quorum_yet s.stage
  | Canon_applied -> (
      match s.stage with
      | Canon_seen -> true
      | Offering | Admitted | Sealed | Quorum_reached | Quorum_failed
      | Pool_synced ->
          false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string a =
  match a with
  | Solo_offer -> "profile=solo"
  | Heavy_offer -> "profile=heavy"
  | Flood_offer -> "profile=flood"
  | Batch_sealed -> "sealed(w)"
  | B_in_batch -> "b1 in sealed_batch(w)"
  | Batch_takes_cap_many_of_a -> "|sealed_batch(w) inter A| >= S"
  | A_admission_at_cap -> "|pool(w) inter A| = S"
  | A_admission_within_cap -> "|pool(w) inter A| <= S"
  | A_left_unsealed -> "pool(w) inter A \\ sealed_batch(w) <> {}"
  | Pool_synced_now -> "pool_synced(w)"
  | A_rest_pending -> "subpool(rest(A)) = pending"
  | A_funded -> "balance(A) >= cost(next(A))"
  | Quorum_acked -> "quorum_ack(batch)"
  | Canon_applied -> "canonical_update_seen(w)"

(** The gas total of A's transactions in the sealed batch, as a peer reads it
    off the encoded transactions. *)
let a_sealed_gas p n = List.fold_left ( + ) 0 (prefix n (a_offer_gas p))

(** What a peer worker observes of this run. Before the broadcast, nothing. *)
let peer_obs_of s =
  if sealed_yet s.stage then
    Obs_batch
      ( s.a_sealed,
        a_sealed_gas s.profile s.a_sealed,
        (if s.b_sealed then 1 else 0),
        if s.b_sealed then b_offer_gas s.profile else 0 )
  else Obs_no_batch

(** View projection. V0 (the worker) and V1 (a peer worker) are the knowledge
    agents; V2 .. V9 are idle non-agents with the constant blank view and never
    appear under [K]. V0 sees its whole pool and its whole batch but never
    [funding], which batch.rs:137 replaces with [U256::MAX]; V1 sees only the
    batch it received, because crates/batch-validator/src/validator.rs:39-82
    consults no pool. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_worker
        (s.profile, s.stage, s.a_admitted, s.a_sealed, s.b_sealed, s.remainder)
  | Validator.V1 -> View_peer (peer_obs_of s)
  | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5 | Validator.V6
  | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** The CTLK checker over this family's ordered state and view: the presheaf-topos
    denotation, pinned to agree with {!System} at every reachable world by
    test/t_batch_pack_share_topos.ml. Every transition advances {!stage} by one
    position of a fixed order and reverses nothing, so reachability is
    antisymmetric - asserted by that gate under every mutation, not assumed
    here. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the six initial states, the
    mutation-parameterized transitions, the two-agent view, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = all_initials; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
