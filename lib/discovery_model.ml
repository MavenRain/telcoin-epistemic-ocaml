(** Finite interpreted system for the DISCOVERY family: the kad/peer-exchange
    discovery surface of telcoin-network's libp2p peer manager, abstracted to
    the three routes by which a remote party can influence what network endpoint
    the local node resolves for a committee authority A. File citations refer to
    Telcoin-Association/telcoin-network at git HEAD [0c59c15b].

    The modeled mechanism, route by route:

    - OUTBOUND KAD GET (the [Ep_query] episode). A GET is opened only for a BLS
      key ABSENT from [known_peers] ([trigger_missing_authorities],
      manager.rs:749-755, filters on [!known_peers.contains_key];
      [find_authorities], manager.rs:878-892, does the same), so the query
      episode starts from [C_none] - there is no cached endpoint to roll back on
      this route. Each [GetRecord] hit is signature-validated first
      (consensus.rs:1744-1755 -> [peer_record_valid], consensus.rs:531-565) and
      then folded into [KadQuery.result] (types.rs:988-1001) by
      [process_kad_query_result] (consensus.rs:1980-2012). The fold is a STRICT
      MAX on timestamp: the arm
      [Some(tracked) if tracked.info.timestamp < new_record.info.timestamp =>
      *tracked = new_record] (consensus.rs:1995-1997) is what makes the outcome
      order-independent; with only [None =>] and [Some(_) => {}] the query would
      be first-response-wins. On [step.last] (consensus.rs:2008-2012)
      [close_kad_query] hands exactly [query.result] to [add_discovered_peer]
      (consensus.rs:2015-2024), which after the committee gate
      (manager.rs:787-797) reaches [cache_known_peer] and the unconditional
      [known_peers.insert] (manager.rs:851-875, the insert at :868).

    - INBOUND KAD PUT (the [Ep_put] episode). [process_kad_put_request]
      (consensus.rs:1874-1947) validates the record, then gates the store write
      AND [add_self_advertised_peer] behind [is_newer_record]
      (consensus.rs:1916; the predicate at consensus.rs:1954-1972). A
      signature-valid but non-newer record takes the else branch
      (consensus.rs:1932-1937), which log-only and deliberately assesses NO
      penalty. The two Fatal penalties on this route are the missing-publisher
      branch (consensus.rs:1903-1906) and the invalid-record branch
      (consensus.rs:1938-1944). Note that for a COMMITTEE key
      [add_self_advertised_peer] caches a RELAYED record too (manager.rs:820-821:
      the [source == advertised] test only guards the non-committee
      else-branch), so :1916 really is the sole thing standing between a relayed
      stale record and [known_peers.insert].

      What :1916 actually compares is the crux of statement SB and is modelled
      explicitly rather than hardwired away. [is_newer_record] consults the LOCAL
      KAD RECORD STORE ([kademlia.store_mut().get(&record.key)],
      consensus.rs:1955-1957) - NOT [known_peers] - and its else arm is literally
      [true] with the doc comment "Also returns true if the record is not found"
      (consensus.rs:1968-1971); [KadStore::get] also returns [None] once a stored
      record's TTL has passed (kad.rs:325-337). That store has exactly two
      writers: [provide_our_data], which publishes OUR OWN record under our own
      key (consensus.rs:569-573), and the accept branch at :1917-1922 itself.
      The GET route never writes it - [kad::QueryResult::GetRecord]
      (consensus.rs:1744-1755) only folds into [KadQuery.result] and
      [close_kad_query] (consensus.rs:2015-2024) calls [add_discovered_peer] -
      and the startup restore goes straight to [add_known_peer] ->
      [cache_known_peer] (consensus.rs:438-439, manager.rs:771-774). So
      "[known_peers] resolves A to r1 while the kad store holds NO unexpired
      entry for A's key" is an ordinary configuration - it is exactly what this
      family's own GET episode leaves behind - and in it a byte-valid OLDER
      record relayed by S makes :1916 evaluate TRUE: the record is stored, the
      committee branch of [add_self_advertised_peer] (manager.rs:820-821, not
      source-gated) runs, and the unconditional [known_peers.insert]
      (manager.rs:868, no timestamp compare) REGRESSES the entry to r0. The
      [store] component below carries that branch, so the PUT statement is scoped
      to the configuration in which the gate is genuinely load-bearing.

    - PEER EXCHANGE (the [Ep_px] episode). [PeerExchangeMap] is a bare unsigned
      [HashMap<BlsPublicKey,(NetworkPublicKey,HashSet<Multiaddr>)>]
      (peers/types.rs:169), intercepted straight off the req-res path
      (consensus.rs:1129-1141). [process_peer_exchange] (manager.rs:614-652)
      destructures [|(_, (net_key, addrs))|] at :624 - THROWING THE ADVERTISED
      BLS KEY AWAY - and only ever writes [self.discovery_peers] (:649). No
      bls<->peer_id binding can come from px content. The repair path IS
      modelled: a hinted endpoint is dialed, connects, and pushes its OWN signed
      record, at which point [add_self_advertised_peer] (manager.rs:813-838)
      confirms the identity through [AllPeers::upsert_peer]
      (all_peers.rs:212-256).

    Components. The three episodes share ONE hidden world component and are
    modelled as a DISJOINT UNION ([episode], an OCaml variant, not a product):
    a run stays inside one episode, which is what keeps the graph at 35 states
    rather than the product's hundreds.

    - [nature] - the hidden world. [N_current]: authority A never published
      beyond r0 and the remote peer S is honest. [N_lagging]: A published a
      strictly newer record r1, held by some DHT peer that may never answer;
      S is honest but holds only r0 - a restart from a persisted store, or
      kad's periodic replication of a record S did not publish (KadStore::put,
      kad.rs:339-379, stores whatever it is handed). [N_replayer]: A published
      r1, S holds r1 and deviates - it replays r0, forges signature-invalid
      records, and fabricates sybil px entries. Deriving
      [Newer_record_exists = N_lagging | N_replayer] and
      [Source_deviated = N_replayer] from one component is what makes the
      cross-nature view classes non-singleton.
    - [cache] - V0's [known_peers] entry for A ([C_none | C_r0 | C_r1]), the
      thing [known_peers.insert] (manager.rs:868) overwrites.
    - [store] (inside the PUT episode) - what the LOCAL kad record store holds
      for A's key as the inbound PUT is evaluated: an unexpired entry no older
      than the relayed record ([St_fresh], so :1916 is false), or nothing
      ([St_absent], so :1916 is true). It is a separate component from [cache]
      precisely because the two are written by disjoint sets of call sites.
    - [episode] - which discovery route this run exercises, carrying everything
      V0 has processed on it.

    Role mapping (a knowledge agent must be a validator with a real,
    non-constant view; a blank-view party may never appear under K):
    - V0 is the LOCAL node running the peer manager and the ONLY knowledge
      agent. It SEES its [known_peers] entry for A and the whole running
      episode: which records it received and validated in the query, what
      [KadQuery.result] tracks, whether the query closed, which inbound PUT
      event it processed, what its OWN kad record store held for A's key when
      that PUT was evaluated (the store is local - [store_mut().get],
      consensus.rs:1955-1957), any penalty it assessed, and the px
      hint/identity state. It does NOT see [nature]: not whether A has published beyond the
      record V0 holds, not whether the peer that answered or relayed is an
      honest lagging replicator or a replayer holding the newer record, and not
      whether px-listed endpoints are distinct nodes or sybils of the sender.
    - A (the authority whose record is being resolved) and S (the answering /
      relaying / exchanging remote peer) are phantom parties folded into
      [nature]; they are never a {!Validator.t} and never appear under K.
    - V1, V2, V3 are idle non-agents with the constant blank [View_idle] and
      never appear under K.

    Modelling assumptions stated openly. (1) [put_invalid] is enabled only in
    [N_replayer]: emitting bytes that fail [peer_record_valid] is itself the
    deviation the atom names, and no honest replicator's store holds such a
    record. (2) The modelled PUT source is a NON-COMMITTEE DHT replicator, so
    the [TrustBasis] penalty exemption (peer.rs:209-237) and
    [forgive_temporarily_banned] (manager.rs:737-745) - both committee/allowlist
    scoped - cannot silently suppress the penalty the [Penalize_stale_record]
    mutation adds. (3) The pool-size half of the mined px card (kad candidates
    are never evicted by px ingestion) is DELIBERATELY NOT MODELLED: it is false
    as stated, because [process_peers_for_discovery] (manager.rs:992-997) is
    uncapped and [discovery_heartbeat] (manager.rs:1000-1058) both dial-removes
    and randomly prunes candidates. *)

(** The hidden world component: what authority A published and whether the
    remote peer S deviates. Nothing in any view projects it. *)
type nature =
  | N_current
      (** A never published beyond r0; S is honest and holds r0. No newer
          record exists anywhere in the system. *)
  | N_lagging
      (** A published a strictly newer record r1 held by some DHT peer that may
          never answer; S is HONEST but holds only r0 - a restart from a
          persisted store, or kad replication of a record S did not publish
          (kad.rs:339-379). *)
  | N_replayer
      (** A published r1 and S HOLDS r1 yet deviates: it replays r0 to pin V0 to
          the old endpoint, can forge signature-invalid records, and can
          fabricate sybil peer-exchange entries. *)

(** Total order index for {!nature}. *)
let nature_index = function N_current -> 0 | N_lagging -> 1 | N_replayer -> 2

(** Total order on {!nature}. *)
let nature_compare a b = Int.compare (nature_index a) (nature_index b)

(** [true] iff authority A has published a record strictly newer than r0
    somewhere in the system. *)
let nature_newer_exists = function
  | N_current -> false
  | N_lagging -> true
  | N_replayer -> true

(** [true] iff the remote peer S holds the newer record and deviates. *)
let nature_deviated = function
  | N_current -> false
  | N_lagging -> false
  | N_replayer -> true

(** V0's [known_peers] entry for authority A (manager.rs:868). *)
type cache =
  | C_none  (** no entry - the state in which a kad GET is ever opened *)
  | C_r0  (** the entry resolves A to the OLDER record's endpoint *)
  | C_r1  (** the entry resolves A to the NEWER record's endpoint *)

(** Total order index for {!cache}. *)
let cache_index = function C_none -> 0 | C_r0 -> 1 | C_r1 -> 2

(** Total order on {!cache}. *)
let cache_compare a b = Int.compare (cache_index a) (cache_index b)

(** [true] iff [known_peers] resolves A to the newer record. *)
let cache_is_r1 = function C_none -> false | C_r0 -> false | C_r1 -> true

(** [KadQuery.result] (types.rs:988-1001): the best record the running query
    tracks so far. *)
type qres =
  | Q_none  (** [None] - no valid response folded in yet *)
  | Q_r0  (** [Some] the older record *)
  | Q_r1  (** [Some] the newer record *)

(** Total order index for {!qres}. *)
let qres_index = function Q_none -> 0 | Q_r0 -> 1 | Q_r1 -> 2

(** Total order on {!qres}. *)
let qres_compare a b = Int.compare (qres_index a) (qres_index b)

(** [true] iff the query tracks no record yet. *)
let qres_is_none = function Q_none -> true | Q_r0 -> false | Q_r1 -> false

(** [true] iff the query tracks the older record. *)
let qres_is_r0 = function Q_none -> false | Q_r0 -> true | Q_r1 -> false

(** [true] iff the query tracks the newer record. *)
let qres_is_r1 = function Q_none -> false | Q_r0 -> false | Q_r1 -> true

(** Whether the outbound query is still accumulating responses or has hit
    [step.last] and been handed to [close_kad_query] (consensus.rs:2008-2012). *)
type qphase =
  | Q_open  (** still accumulating: further responses can still fold in *)
  | Q_closed  (** [step.last] fired; the result was committed *)

(** Total order index for {!qphase}. *)
let qphase_index = function Q_open -> 0 | Q_closed -> 1

(** Total order on {!qphase}. *)
let qphase_compare a b = Int.compare (qphase_index a) (qphase_index b)

(** [true] iff the query is still open. *)
let qphase_is_open = function Q_open -> true | Q_closed -> false

(** [true] iff the query has closed. *)
let qphase_is_closed = function Q_open -> false | Q_closed -> true

(** One outbound kad GET for authority A's record. *)
type query = {
  got_r1 : bool;
      (** a signature-valid response CARRYING the newer record arrived during
          this query (consensus.rs:1744-1755) *)
  res : qres;  (** what [KadQuery.result] currently tracks *)
  phase : qphase;  (** open, or closed and committed *)
}

(** Total deterministic order over all fields of a {!query}. *)
let query_compare qa qb =
  let c = Bool.compare qa.got_r1 qb.got_r1 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = qres_compare qa.res qb.res in
    if Bool.not (Int.equal c1 0) then c1 else qphase_compare qa.phase qb.phase

(** The inbound-PUT event processed on this run (consensus.rs:1912-1944). *)
type put_ev =
  | P_pending  (** nothing processed yet *)
  | P_stale
      (** a signature-valid but NON-newer record for A, relayed by S: the
          [is_newer_record] else branch (consensus.rs:1932-1937) *)
  | P_invalid
      (** a record that failed [peer_record_valid]: the Fatal branch
          (consensus.rs:1938-1944) *)

(** Total order index for {!put_ev}. *)
let put_ev_index = function P_pending -> 0 | P_stale -> 1 | P_invalid -> 2

(** Total order on {!put_ev}. *)
let put_ev_compare a b = Int.compare (put_ev_index a) (put_ev_index b)

(** [true] iff no inbound PUT has been processed yet on this run. *)
let put_ev_is_pending = function
  | P_pending -> true
  | P_stale -> false
  | P_invalid -> false

(** [true] iff the processed event was a signature-valid but non-newer record. *)
let put_ev_is_stale = function
  | P_pending -> false
  | P_stale -> true
  | P_invalid -> false

(** What V0's LOCAL kad record store holds for authority A's key at the moment
    an inbound PUT is evaluated - the only thing [is_newer_record] looks at
    (consensus.rs:1955-1971). It is NOT [known_peers]: the two are written by
    disjoint call sites, so their contents can disagree. *)
type store =
  | St_fresh
      (** an unexpired stored record for A's key whose timestamp is not older
          than the relayed one, so [existing.info.timestamp < new.info.timestamp]
          (consensus.rs:1962-1965) is FALSE and the gate rejects. Reached when
          A itself PUT its record to V0 earlier, which is the one route that
          writes this store for a remote key (consensus.rs:1917-1922). *)
  | St_absent
      (** no unexpired entry for A's key, so [store.get] returns [None] and the
          gate's else arm returns [true] (consensus.rs:1968-1971). Reached
          whenever [known_peers(A)] came from a kad GET (which only folds into
          [KadQuery.result] and calls [add_discovered_peer],
          consensus.rs:1744-1755, :2015-2024 - it never writes the store) or
          from the startup restore ([add_known_peer], consensus.rs:438-439,
          manager.rs:771-774), or once the stored record's TTL has passed
          ([KadStore::get], kad.rs:325-337). *)

(** Total order index for {!store}. *)
let store_index = function St_fresh -> 0 | St_absent -> 1

(** Total order on {!store}. *)
let store_compare a b = Int.compare (store_index a) (store_index b)

(** [true] iff the local kad store still holds a record for A's key that is not
    older than the relayed one, i.e. [is_newer_record] returns false. *)
let store_is_fresh = function St_fresh -> true | St_absent -> false

(** The inbound-PUT episode: which event was processed, what the local kad store
    held for A's key when it was evaluated, and whether a Fatal was assessed
    against the PUT's source ([process_penalty], all_peers.rs:261). *)
type put = {
  ev : put_ev;  (** the event processed on this run *)
  store : store;
      (** the local kad store's entry for A's key as the PUT is evaluated
          (consensus.rs:1955-1971). One inbound PUT per run, so the accept
          branch's own store write (consensus.rs:1917-1922) is never re-read and
          this component is not updated by the step. *)
  penalized : bool;  (** a Fatal was assessed against the source *)
}

(** Total deterministic order over all fields of a {!put}. *)
let put_compare pa pb =
  let c = put_ev_compare pa.ev pb.ev in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = store_compare pa.store pb.store in
    if Bool.not (Int.equal c1 0) then c1
    else Bool.compare pa.penalized pb.penalized

(** The peer-exchange episode for one exchanged endpoint. *)
type px = {
  hinted : bool;
      (** a [PeerExchangeMap] was accepted into [discovery_peers]
          (manager.rs:647-649) *)
  signed_seen : bool;
      (** a signature-validated kad record FROM that endpoint has been
          processed (consensus.rs:1914 -> manager.rs:813-838) *)
  bound : bool;
      (** a [PeerIdentity::Confirmed] bls<->peer_id binding exists for it
          (all_peers.rs:220, :254-255) *)
}

(** Total deterministic order over all fields of a {!px}. *)
let px_compare xa xb =
  let c = Bool.compare xa.hinted xb.hinted in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Bool.compare xa.signed_seen xb.signed_seen in
    if Bool.not (Int.equal c1 0) then c1 else Bool.compare xa.bound xb.bound

(** The discovery route this run exercises. A run stays inside one episode: the
    three routes are independent code paths on distinct events, and modelling
    them as a disjoint union rather than a product is what keeps the reachable
    graph small (R6). *)
type episode =
  | Ep_query of query  (** one outbound kad GET for A's record *)
  | Ep_put of put  (** one inbound kad PUT for A's record, relayed by S *)
  | Ep_px of px  (** one peer-exchange map received from S *)

(** Total order on {!episode}: [Ep_query] < [Ep_put] < [Ep_px], with the
    field-wise order inside each constructor. All nine constructor pairs are
    spelled: no wildcard arm on the finite episode sum. *)
let episode_compare a b =
  match (a, b) with
  | Ep_query qa, Ep_query qb -> query_compare qa qb
  | Ep_query _, Ep_put _ -> -1
  | Ep_query _, Ep_px _ -> -1
  | Ep_put _, Ep_query _ -> 1
  | Ep_put pa, Ep_put pb -> put_compare pa pb
  | Ep_put _, Ep_px _ -> -1
  | Ep_px _, Ep_query _ -> 1
  | Ep_px _, Ep_put _ -> 1
  | Ep_px xa, Ep_px xb -> px_compare xa xb

(** The joint global state: the hidden world, V0's cached endpoint for A, and
    the running discovery episode. *)
type state = {
  nature : nature;  (** the hidden world component - in NO view *)
  cache : cache;  (** V0's [known_peers] entry for A *)
  ep : episode;  (** the running discovery episode *)
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = nature_compare s1.nature s2.nature in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = cache_compare s1.cache s2.cache in
    if Bool.not (Int.equal c1 0) then c1 else episode_compare s1.ep s2.ep

(** The ordered state module for {!System.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's local view. [View_local] is V0's peer-manager-local
    projection: its [known_peers] entry for A plus everything it has processed
    in the running episode. It carries NO component of [nature], so V0 can never
    distinguish an honest lagging peer from a replayer, nor a world where a
    newer record exists from one where it does not. [View_idle] is the constant
    blank view of the non-agents V1, V2, V3. *)
type view =
  | View_local of cache * episode  (** V0's projection *)
  | View_idle  (** the constant blank view of V1, V2, V3 *)

(** Total order on views: [View_idle] < [View_local], with the field-wise order
    inside [View_local]. Every constructor pair is spelled: no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_local _ -> -1
  | View_local _, View_idle -> 1
  | View_local (ca, ea), View_local (cb, eb) ->
      let c = cache_compare ca cb in
      if Bool.not (Int.equal c 0) then c else episode_compare ea eb

(** The ordered view module for {!System.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection. V0 - the local node running the peer manager - is the ONLY
    knowledge agent and the only validator that ever appears under K; V1, V2, V3
    are idle non-agents with the constant blank view. *)
let view v s =
  match v with
  | Validator.V0 -> View_local (s.cache, s.ep)
  | Validator.V1 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | No_query_max_fold
      (** delete the strict-max arm
          [Some(tracked) if tracked.info.timestamp < new_record.info.timestamp
          => *tracked = new_record] of [process_kad_query_result]
          (consensus.rs:1995-1997), leaving only [None =>] and [Some(_) => {}],
          i.e. first-response-wins across the query's steps. This ADDS the
          [recv_r1] transition (got_r1=false, res=Q_r0) -> (got_r1=true,
          res=Q_r0) in both newer-record worlds, making [Ep_query{true, Q_r0,
          Q_open}] and its closed twin (with cache=[C_r0]) reachable and taking
          the reachable count 35 -> 39. NO SIBLING PATH repairs it: the only
          recency predicate in the crate, [is_newer_record]
          (consensus.rs:1954-1972), has exactly ONE call site - consensus.rs:1916
          on the PUT route - and the GET route never calls it;
          [add_discovered_peer] (manager.rs:787-797) gates on committee
          membership only (which key, not which version); [cache_known_peer]
          ends in the unconditional [known_peers.insert] (manager.rs:868);
          [AllPeers::upsert_peer] (all_peers.rs:212-256) carries reputation and
          re-keys on rotation but has no timestamp logic; and [KadStore::put]
          (kad.rs:339-379) has only a value-size and a max-records cap - and the
          GET route never writes the store anyway. A later self-PUT by A could
          restore the endpoint, but that is a DIFFERENT event, modelled here as
          its own episode, and this statement's atoms are scoped to the query's
          own result and its close-time write. *)
  | No_put_freshness_gate
      (** delete the [if self.is_newer_record(&record)] conditional
          (consensus.rs:1916) so every signature-valid record takes the
          store-and-cache branch (consensus.rs:1917-1931). Pristine that
          conditional is load-bearing on exactly the [St_fresh] half of the PUT
          episode (on the [St_absent] half it already evaluates true and the
          relayed record is already adopted); the mutation makes the [put_stale]
          transition set cache := [C_r0] on the [St_fresh] half TOO, so the
          reachable state [Ep_put{P_stale; St_fresh; false}] carries [C_r0]
          instead of [C_r1] (reachable count unchanged). NO SIBLING PATH repairs
          it:
          [KadStore::put] (kad.rs:339-379) overwrites unconditionally (only a
          value-size cap and a max-records/TTL path, no timestamp compare);
          [add_self_advertised_peer] (manager.rs:813-838) sends a COMMITTEE key
          straight to [cache_known_peer] - the [source == advertised] test at
          :822 only guards the non-committee else-branch, so a RELAYED record
          for a committee authority is cached - and [cache_known_peer] ends in
          [known_peers.insert] (manager.rs:868), a full overwrite of
          [NetworkInfo]; [AllPeers::upsert_peer] (all_peers.rs:212-256) has no
          recency logic; [peer_record_valid] (consensus.rs:531-565) checks the
          BLS signature, the multiaddr cap and publisher==advertised network
          key but NEVER the timestamp and never the source, so a verbatim replay
          passes it; and the banned-source/publisher pre-check
          (consensus.rs:1880-1888) rejects on ban status only. *)
  | Penalize_stale_record
      (** delete the deliberate no-penalty carve-out of the stale branch
          (consensus.rs:1932-1937, "A peer republishing a slightly stale (but
          signature-valid) record is expected after restarts and benign - log
          only; no penalty") and replace it with the invalid branch's
          [process_penalty(source, Penalty::Fatal)] (consensus.rs:1943). This
          makes the [put_stale] transition set penalized := true, so
          [Ep_put{P_stale,true}] is reachable in BOTH newer-record worlds -
          including [N_lagging], where the source is an honest restarted
          replicator (reachable count unchanged at 35). NO SIBLING PATH
          un-attributes the added penalty within scope: the real candidate, the
          [TrustBasis] exemption in [Peer::apply_penalty] (peer.rs:213-233,
          reached via [AllPeers::process_penalty], all_peers.rs:261-264), fires
          only for operator-allowlisted or committee peers, and
          [forgive_temporarily_banned] (manager.rs:737-745) lifts bans only for
          committee members - while the modelled source is a NON-COMMITTEE DHT
          replicator, exactly the honest-restart story the deleted comment
          describes. The only other penalty sites on this path are the
          missing-publisher Fatal (consensus.rs:1903-1906) and the
          invalid-record Fatal (consensus.rs:1938-1944), neither of which a
          signature-valid record with a publisher can take. *)
  | Px_binds_identity
      (** delete the BLS-key discard in [process_peer_exchange]: the
          [filter_map(|(_, (net_key, addrs))| ...)] binding at manager.rs:624
          throws the exchange map's advertised [BlsPublicKey] away and builds a
          bare [PeerInfo] that only ever reaches [self.discovery_peers.insert]
          (:649); the mutation keeps the key and calls
          [self.peers.upsert_peer(bls, net_key, addrs)] with it, trusting the
          UNSIGNED map. This makes the [recv_px] transition also set bound :=
          true, so [Ep_px{hinted=true; signed_seen=false; bound=true}] is
          reachable in all three worlds (reachable count unchanged at 35). NO
          SIBLING PATH rejects or undoes the unsigned binding:
          [AllPeers::upsert_peer] (all_peers.rs:212-256) performs NO validation
          - it evicts/migrates, calls [peer.update_net], then inserts
          [bls_by_peer_id] and a [PeerIdentity::Confirmed] record
          unconditionally (:254-255); [eligible_for_discovery]
          (manager.rs:980-987) screens self-identity, ip validity/bans and
          dialability but never identity provenance; the reciprocal disconnect
          after px (consensus.rs:1137-1139) drops the SENDER of the map, not the
          listed endpoints, and touches no stored identity; and
          [discovery_heartbeat] (manager.rs:1000-1058) prunes and dials
          candidates without ever inspecting bindings. A later genuine signed
          record from the real key owner would re-key through [upsert_peer], but
          nothing forces that peer to ever connect and PUT. *)

(** The in-query fold applied to [KadQuery.result] when a response carrying the
    NEWER record arrives (consensus.rs:1993-1999). Pristine (and under every
    mutation that does not touch this gate) it is the strict max, so a newer
    record always displaces a tracked older one; under
    {!No_query_max_fold} the [Some(tracked) if ...] arm is gone, so a tracked
    older record survives - first-response-wins. Every mutation arm is spelled. *)
let query_fold mut res =
  let keep_max = match res with Q_none -> Q_r1 | Q_r0 -> Q_r1 | Q_r1 -> Q_r1 in
  let first_wins =
    match res with Q_none -> Q_r1 | Q_r0 -> Q_r0 | Q_r1 -> Q_r1
  in
  match mut with
  | Pristine -> keep_max
  | No_query_max_fold -> first_wins
  | No_put_freshness_gate -> keep_max
  | Penalize_stale_record -> keep_max
  | Px_binds_identity -> keep_max

(** The close-time write: [close_kad_query] calls [add_discovered_peer] only
    when [query.result] is [Some] (consensus.rs:2015-2024), so a query that
    tracked nothing leaves [known_peers] untouched. *)
let commit_cache c res =
  match res with Q_none -> c | Q_r0 -> C_r0 | Q_r1 -> C_r1

(** The cached endpoint after a byte-valid but OLDER relayed record is processed
    by an inbound PUT. Pristine the outcome is decided by the LOCAL KAD STORE,
    which is what [is_newer_record] reads (consensus.rs:1955-1971): with
    [St_fresh] the comparison at :1962-1965 is false, the else branch at
    :1932-1937 only logs and the cache is untouched; with [St_absent] the else
    arm of the store lookup returns [true] (:1968-1971), so the record is stored
    (:1917-1922) and [add_self_advertised_peer] runs - and because A is a
    committee authority the not-source-gated branch at manager.rs:820-821 sends
    it to [cache_known_peer] and the unconditional [known_peers.insert]
    (manager.rs:868), REGRESSING the entry to [C_r0]. Under
    {!No_put_freshness_gate} the conditional is gone, so the [St_fresh] half
    regresses as well. Every mutation arm is spelled. *)
let put_stale_cache mut st c =
  let gated = match st with St_fresh -> c | St_absent -> C_r0 in
  match mut with
  | Pristine -> gated
  | No_query_max_fold -> gated
  | No_put_freshness_gate -> C_r0
  | Penalize_stale_record -> gated
  | Px_binds_identity -> gated

(** Whether a Fatal is assessed against the source of a stale inbound PUT.
    Pristine the carve-out at consensus.rs:1932-1937 assesses none; under
    {!Penalize_stale_record} it assesses one. Every mutation arm is spelled. *)
let put_stale_penalized mut =
  match mut with
  | Pristine -> false
  | No_query_max_fold -> false
  | No_put_freshness_gate -> false
  | Penalize_stale_record -> true
  | Px_binds_identity -> false

(** Whether ingesting a peer-exchange map confers a bls<->peer_id binding.
    Pristine the BLS key is discarded at manager.rs:624 so it does not; under
    {!Px_binds_identity} the unsigned map is fed to [upsert_peer]. Every
    mutation arm is spelled. *)
let px_recv_bound mut b =
  match mut with
  | Pristine -> b
  | No_query_max_fold -> b
  | No_put_freshness_gate -> b
  | Penalize_stale_record -> b
  | Px_binds_identity -> true

(** Enabled steps of the outbound-GET episode: a responder returns A's older
    record ([recv_r0], only while nothing is tracked - with [Q_r0] or [Q_r1]
    already tracked an r0 arrival hits [Some(_) => {}] or fails the strict-newer
    test and changes nothing); a responder returns the newer record ([recv_r1],
    possible only in a world where one exists, and only once); and [step.last]
    closes the query, committing [query.result]. [Q_closed] is terminal and is
    stutter-closed by the kernel. *)
let query_next mut s q =
  let is_open = qphase_is_open q.phase in
  let recv_r0 =
    if is_open && qres_is_none q.res then
      [ { s with ep = Ep_query { q with res = Q_r0 } } ]
    else []
  in
  let recv_r1 =
    if is_open && nature_newer_exists s.nature && Bool.not q.got_r1 then
      [
        {
          s with
          ep = Ep_query { q with got_r1 = true; res = query_fold mut q.res };
        };
      ]
    else []
  in
  let close_step =
    if is_open then
      [
        {
          s with
          cache = commit_cache s.cache q.res;
          ep = Ep_query { q with phase = Q_closed };
        };
      ]
    else []
  in
  List.concat [ recv_r0; recv_r1; close_step ]

(** Enabled steps of the inbound-PUT episode: S relays a signature-valid but
    non-newer record ([put_stale]), whose effect on the cache depends on what the
    local kad store held (see {!put_stale_cache}), or - only in the deviating
    world - pushes a record that fails [peer_record_valid], drawing the Fatal at
    consensus.rs:1943 and storing nothing ([put_invalid]). One inbound PUT per
    run, so [P_stale] and [P_invalid] are terminal and the store component is
    carried through unchanged. *)
let put_next mut s p =
  let pending = put_ev_is_pending p.ev in
  let put_stale =
    if pending then
      [
        {
          s with
          cache = put_stale_cache mut p.store s.cache;
          ep =
            Ep_put
              {
                ev = P_stale;
                store = p.store;
                penalized = put_stale_penalized mut;
              };
        };
      ]
    else []
  in
  let put_invalid =
    if pending && nature_deviated s.nature then
      [
        {
          s with
          ep = Ep_put { ev = P_invalid; store = p.store; penalized = true };
        };
      ]
    else []
  in
  List.concat [ put_stale; put_invalid ]

(** Enabled steps of the peer-exchange episode: the map is ingested into
    [discovery_peers] ([recv_px]), and then the hinted endpoint is dialed,
    connects and pushes its OWN signed record, so [source == advertised] and
    [add_self_advertised_peer] confirms the binding ([self_signed_put]) - the
    real repair path by which a px hint DOES eventually acquire an identity.
    (true,true,true) is terminal. *)
let px_next mut s x =
  let recv_px =
    if Bool.not x.hinted then
      [
        {
          s with
          ep = Ep_px { x with hinted = true; bound = px_recv_bound mut x.bound };
        };
      ]
    else []
  in
  let self_signed_put =
    if x.hinted && Bool.not x.signed_seen then
      [ { s with ep = Ep_px { x with signed_seen = true; bound = true } } ]
    else []
  in
  List.concat [ recv_px; self_signed_put ]

(** The transition relation under a mutation: dispatch on the running episode.
    Each episode is a small acyclic graph whose terminals the kernel
    stutter-closes. *)
let next_with mut s =
  match s.ep with
  | Ep_query q -> query_next mut s q
  | Ep_put p -> put_next mut s p
  | Ep_px x -> px_next mut s x

(** The pristine transition relation. *)
let next = next_with Pristine

(** A fresh outbound GET: nothing received, nothing tracked, still open. *)
let query_start = Ep_query { got_r1 = false; res = Q_none; phase = Q_open }

(** A fresh inbound-PUT episode over a given local kad store state: no event
    processed, no penalty assessed. *)
let put_start st = Ep_put { ev = P_pending; store = st; penalized = false }

(** A fresh peer-exchange episode: no hints, no signed record, no binding. *)
let px_start = Ep_px { hinted = false; signed_seen = false; bound = false }

(** The initial states - one per (world, episode, local-store) combination that
    the real code can start from. The GET episodes start at [C_none] because a
    kad lookup is only ever opened for a committee key MISSING from
    [known_peers] (manager.rs:749-755, :878-892). The PUT episodes exist only in
    the two newer-record worlds and start at [C_r1], because a stale-replay
    attempt presupposes both that a newer record exists and that V0 already
    holds it - in [N_current] there is no r1 to hold - and each such world is
    taken with BOTH local-store states, because how V0 came to hold r1 decides
    the store: A's own PUT wrote it ([St_fresh], consensus.rs:1917-1922) while a
    kad GET or the startup restore did not ([St_absent], consensus.rs:1744-1755,
    :2015-2024, :438-439), and a stored entry expires on its own
    ([KadStore::get], kad.rs:325-337). The px episodes start at [C_none] in all
    three worlds. *)
let initial =
  [
    { nature = N_current; cache = C_none; ep = query_start };
    { nature = N_lagging; cache = C_none; ep = query_start };
    { nature = N_replayer; cache = C_none; ep = query_start };
    { nature = N_lagging; cache = C_r1; ep = put_start St_fresh };
    { nature = N_replayer; cache = C_r1; ep = put_start St_fresh };
    { nature = N_lagging; cache = C_r1; ep = put_start St_absent };
    { nature = N_replayer; cache = C_r1; ep = put_start St_absent };
    { nature = N_current; cache = C_none; ep = px_start };
    { nature = N_lagging; cache = C_none; ep = px_start };
    { nature = N_replayer; cache = C_none; ep = px_start };
  ]

(** Lift a query-episode predicate to the global state; false off that episode.
    Every episode constructor is spelled. *)
let in_query f s =
  match s.ep with Ep_query q -> f q | Ep_put _ -> false | Ep_px _ -> false

(** Lift a PUT-episode predicate to the global state; false off that episode.
    Every episode constructor is spelled. *)
let in_put f s =
  match s.ep with Ep_query _ -> false | Ep_put p -> f p | Ep_px _ -> false

(** Lift a px-episode predicate to the global state; false off that episode.
    Every episode constructor is spelled. *)
let in_px f s =
  match s.ep with Ep_query _ -> false | Ep_put _ -> false | Ep_px x -> f x

(** The atom vocabulary the three DISCOVERY statements quantify over. *)
type atom =
  | Newer_record_exists
      (** HIDDEN: authority A has published a record strictly newer than r0
          somewhere in the system ([nature] is [N_lagging] or [N_replayer]) *)
  | Source_deviated
      (** HIDDEN: the remote peer S holds the newer record and deviates -
          replays r0, forges invalid records, fabricates sybil px entries
          ([nature] is [N_replayer]) *)
  | Query_closed
      (** the running kad GET hit [step.last] and was handed to
          [close_kad_query] (consensus.rs:2008-2012) *)
  | Query_got_r1
      (** a signature-valid response CARRYING the newer record arrived during
          this query (consensus.rs:1744-1755) *)
  | Query_result_r1  (** [KadQuery.result] holds the newer record *)
  | Query_result_r0  (** [KadQuery.result] holds the older record *)
  | Cache_r1  (** [known_peers] resolves A to the newer record *)
  | Put_stale_processed
      (** the inbound PUT event processed was a signature-valid but non-newer
          record (consensus.rs:1932-1937) *)
  | Kad_store_fresh
      (** the LOCAL kad record store held an unexpired entry for A's key, no
          older than the relayed record, when the inbound PUT was evaluated - so
          [is_newer_record] (consensus.rs:1954-1972) returned false and the
          :1916 gate rejected. False in every other episode. *)
  | Put_source_penalized
      (** a Fatal penalty was assessed against the PUT's source *)
  | Px_hints_ingested
      (** a peer-exchange map was accepted into [discovery_peers]
          (manager.rs:647-649) *)
  | Px_identity_bound
      (** a [PeerIdentity::Confirmed] bls<->peer_id binding exists for the
          exchanged endpoint (all_peers.rs:220, :254-255) *)
  | Signed_record_seen
      (** a signature-validated kad record from that endpoint has been
          processed *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Newer_record_exists -> nature_newer_exists s.nature
  | Source_deviated -> nature_deviated s.nature
  | Query_closed -> in_query (fun q -> qphase_is_closed q.phase) s
  | Query_got_r1 -> in_query (fun q -> q.got_r1) s
  | Query_result_r1 -> in_query (fun q -> qres_is_r1 q.res) s
  | Query_result_r0 -> in_query (fun q -> qres_is_r0 q.res) s
  | Cache_r1 -> cache_is_r1 s.cache
  | Put_stale_processed -> in_put (fun p -> put_ev_is_stale p.ev) s
  | Kad_store_fresh -> in_put (fun p -> store_is_fresh p.store) s
  | Put_source_penalized -> in_put (fun p -> p.penalized) s
  | Px_hints_ingested -> in_px (fun x -> x.hinted) s
  | Px_identity_bound -> in_px (fun x -> x.bound) s
  | Signed_record_seen -> in_px (fun x -> x.signed_seen) s

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Newer_record_exists -> "newer_record_exists"
  | Source_deviated -> "source_deviated"
  | Query_closed -> "query_closed"
  | Query_got_r1 -> "query_got_r1"
  | Query_result_r1 -> "query_result=r1"
  | Query_result_r0 -> "query_result=r0"
  | Cache_r1 -> "known_peers(A)=r1"
  | Put_stale_processed -> "put_stale_processed"
  | Kad_store_fresh -> "kad_store_fresh"
  | Put_source_penalized -> "put_source_penalized"
  | Px_hints_ingested -> "px_hints_ingested"
  | Px_identity_bound -> "px_identity_bound"
  | Signed_record_seen -> "signed_record_seen"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the ten initial states,
    mutation-parameterized transitions, the single-agent view, the atom
    valuation. *)
let spec_of mut =
  { Checker.init = initial; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
