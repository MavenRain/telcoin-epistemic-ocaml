(** The libp2p request-response / state-sync slice behind the
    verified-response statement: requester V1 pulls one consensus output
    over the primary sync stream from a chosen responder and digest-verifies
    the bytes BEFORE caching them. The abstracted mechanism is
    [get_consensus_output] (telcoin-network
    crates/state-sync/src/consensus.rs:42-94): the invariant doc
    (consensus.rs:34-41) promises the node never caches an output that is
    not verified, the digest gate (consensus.rs:84-87) rejects a
    wrong/forked response with [Retry], and only then does the
    [ConsensusCache] insert run (consensus.rs:89).

    Role mapping:
    - V1, the requester, the ONLY knowledge agent. Its local state is its
      outstanding request slot plus its verified cache: the sync stream is
      opened to one specific BLS peer
      (crates/consensus/primary/src/network/mod.rs:714-722), and the
      requester-side accept/reject of the answer is mod.rs:774-806 (Ack
      with bytes accepted; Deny, empty output, and errors rejected).
    - V2, the honest responder: it serves only bytes it locally holds
      (handler.rs:963-988 reads the local consensus chain via the pack read
      in crates/storage/src/consensus.rs:882-904, wired at
      handler.rs:1383), so its possession is rigid - K over Held(V2)
      collapses to a constant and is deliberately NOT the statement's
      target.
    - V3, the Byzantine responder with hidden contingent possession - the
      entire epistemic payload. It may genuinely hold the bytes and serve
      them, hold them yet shed with a Deny frame (the acknowledged
      load-shed path: "sync-capable, but shedding load or lacking the
      output", crates/consensus/primary/src/network/mod.rs:791-795; an
      at-capacity responder denies without reading the request,
      mod.rs:1892-1910, DenyReason::AtCapacity in
      crates/network-libp2p/src/sync/frame.rs:46-53), shed with
      Deny(Unavailable) exactly as an honest lacker would
      (crates/consensus/primary/src/network/sync_codec.rs:330-347), or
      serve digest-invalid bytes.
    - V0, idle: constant view, never under a knowledge operator.

    Delivery binding is not remodeled: libp2p hands a response only to the
    (peer, request_id) pair that issued the request
    (crates/network-libp2p/src/consensus.rs:1191-1198 and 2150-2157), so a
    single global in-flight [response] field, invisible to V1 until
    verification, is faithful. *)

(* The two peers V1 may fetch from. An answer is attributable to exactly
   one responder because the sync stream is opened to one chosen BLS peer
   (mod.rs:714-722) and the response rides that stream back
   (network-libp2p consensus.rs:1191-1198, 2150-2157). *)
type responder = Resp_v2 | Resp_v3

(* Canonical index for the total order on responders. *)
let responder_index = function Resp_v2 -> 0 | Resp_v3 -> 1

(* Total deterministic order on responders. *)
let responder_compare a b = Int.compare (responder_index a) (responder_index b)

(* Responder equality, for atom valuation. *)
let responder_equal a b = Int.equal (responder_compare a b) 0

(* Rendering for atom pretty-printing. *)
let responder_to_string = function Resp_v2 -> "v2" | Resp_v3 -> "v3"

(* The run's hidden peer choice, resolved at the first transition: which
   responder V1 addresses (the peer argument of open_stream,
   mod.rs:714-722). Global and hidden; V1 records its own copy in
   [req_to]. *)
type target = T_unchosen | T_v2 | T_v3

(* Canonical index for the total order on targets. *)
let target_index = function T_unchosen -> 0 | T_v2 -> 1 | T_v3 -> 2

(* Total deterministic order on targets. *)
let target_compare a b = Int.compare (target_index a) (target_index b)

(* The responder a resolved target addresses; the unresolved target
   addresses nobody (no stream opened yet, mod.rs:714-722). *)
let responder_of = function
  | T_unchosen -> None
  | T_v2 -> Some Resp_v2
  | T_v3 -> Some Resp_v3

(* The hidden Byzantine branch, resolved at the first transition iff V3 is
   engaged: [Genuine] holds the bytes and serves them faithfully (the
   local read, storage consensus.rs:882-904, succeeds as it would for an
   honest node); [Withhold] HOLDS the bytes yet sheds with a Deny frame -
   the acknowledged holds-and-denies behavior (requester gloss
   "sync-capable, but shedding load or lacking the output",
   crates/consensus/primary/src/network/mod.rs:791-795; an at-capacity
   responder denies without reading, mod.rs:1892-1910 with
   DenyReason::AtCapacity, crates/network-libp2p/src/sync/frame.rs:46-53),
   which a Byzantine holder may mimic at will; [Deny] lacks them and sheds
   with Deny(Unavailable) exactly as an honest lacker does
   (sync_codec.rs:330-347); [Fabricate] lacks them and serves
   digest-invalid bytes - the "wrong/forked output" the requester-side
   gate rejects (state-sync consensus.rs:82-87). *)
type v3_mode = M_unchosen | Genuine | Withhold | Deny | Fabricate

(* Canonical index for the total order on Byzantine branches. *)
let v3_mode_index = function
  | M_unchosen -> 0
  | Genuine -> 1
  | Withhold -> 2
  | Deny -> 3
  | Fabricate -> 4

(* Total deterministic order on Byzantine branches. *)
let v3_mode_compare a b = Int.compare (v3_mode_index a) (v3_mode_index b)

(* The in-flight answer, global and OUTSIDE V1's view until verified:
   [Valid j] carries bytes whose digest matches the requested hash,
   [Bogus j] digest-invalid bytes, [Denied j] the Deny(Unavailable) frame
   (sync_codec.rs:320-347). Delivered only via the (peer, request_id)
   binding (network-libp2p consensus.rs:1191-1198, 2150-2157). *)
type response =
  | R_none
  | Valid of responder
  | Bogus of responder
  | Denied of responder

(* Canonical index for the total order on responses, every constructor and
   payload spelled. *)
let response_index = function
  | R_none -> 0
  | Valid Resp_v2 -> 1
  | Valid Resp_v3 -> 2
  | Bogus Resp_v2 -> 3
  | Bogus Resp_v3 -> 4
  | Denied Resp_v2 -> 5
  | Denied Resp_v3 -> 6

(* Total deterministic order on responses. *)
let response_compare a b = Int.compare (response_index a) (response_index b)

(* V1's verified-output cache, tagged with the responder that served the
   row: the [ConsensusCache] insert (state-sync consensus.rs:89) runs only
   after the digest gate, and a cached row is read back as verified
   (consensus.rs:54-55). *)
type cache = Uncached | Cached_from of responder

(* Canonical index for the total order on cache states. *)
let cache_index = function
  | Uncached -> 0
  | Cached_from Resp_v2 -> 1
  | Cached_from Resp_v3 -> 2

(* Total deterministic order on cache states. *)
let cache_compare a b = Int.compare (cache_index a) (cache_index b)

(* The responder credited by the cache, if any. *)
let cached_responder = function Uncached -> None | Cached_from j -> Some j

(* The fetch walk of [get_consensus_output] (state-sync consensus.rs:42-94)
   as a phase machine: Init resolves the hidden branches and issues the
   request (consensus.rs:63-64), Serving is the responder's turn, Verifying
   is the requester-side decode plus digest gate (consensus.rs:71-87), Done
   is terminal - one fetch suffices for the statement, so the walk's
   continuation to other numbers is out of scope. *)
type phase = Init | Serving | Verifying | Done

(* Canonical index for the total order on phases. *)
let phase_index = function Init -> 0 | Serving -> 1 | Verifying -> 2 | Done -> 3

(* Total deterministic order on phases. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(* The global state. [target] and [v3_mode] are the run's hidden branches;
   [response] is the in-flight answer; [req_to] and [cache] are V1-local -
   the ONLY fields in V1's view. [target] and [req_to] agree once
   resolved: the former is the hidden branch selector, the latter V1's own
   record of whom it asked (the peer of mod.rs:714-722). *)
type state = {
  phase : phase;
  target : target;
  v3_mode : v3_mode;
  response : response;
  req_to : responder option;
  cache : cache;
}

(* Pre-request state: nothing chosen, nothing in flight, nothing cached. *)
let initial =
  {
    phase = Init;
    target = T_unchosen;
    v3_mode = M_unchosen;
    response = R_none;
    req_to = None;
    cache = Uncached;
  }

(* Total deterministic order over every field, as the kernel requires. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = target_compare s1.target s2.target in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = v3_mode_compare s1.v3_mode s2.v3_mode in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = response_compare s1.response s2.response in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Option.compare responder_compare s1.req_to s2.req_to in
          if Bool.not (Int.equal c4 0) then c4
          else cache_compare s1.cache s2.cache

(* The ordered state module the kernel functor consumes. *)
module State = struct
  type t = state

  let compare = state_compare
end

(* Per-validator projections, the knowledge ground for K_i. V1 sees ONLY
   its own request slot and verified cache - phase, target, v3_mode, and
   the in-flight response are invisible to it until the digest gate lands
   the bytes in its cache (state-sync consensus.rs:84-89). V3 sees its own
   hidden branch; V2 rigidly holds the served data (storage
   consensus.rs:882-904); V0 is idle. *)
type view =
  | Vw_requester of responder option * cache
  | Vw_honest_holder
  | Vw_byz of v3_mode
  | Vw_idle

(* Total deterministic order on views: constructor tag first, then payload
   fields, absent payloads collapsed to their least element. *)
let view_compare a b =
  let key = function
    | Vw_requester (r, c) -> (0, r, c, M_unchosen)
    | Vw_honest_holder -> (1, None, Uncached, M_unchosen)
    | Vw_byz m -> (2, None, Uncached, m)
    | Vw_idle -> (3, None, Uncached, M_unchosen)
  in
  let t1, r1, ca1, m1 = key a in
  let t2, r2, ca2, m2 = key b in
  let c = Int.compare t1 t2 in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Option.compare responder_compare r1 r2 in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = cache_compare ca1 ca2 in
      if Bool.not (Int.equal c2 0) then c2 else v3_mode_compare m1 m2

(* The ordered view module the kernel functor consumes. *)
module View = struct
  type t = view

  let compare = view_compare
end

(* The view projection: exactly what each node locally possesses on the
   fetch path - V1 its request slot and cache (mod.rs:714-722,
   consensus.rs:54-55, :89), V2 its rigid possession (storage
   consensus.rs:882-904), V3 its own hidden branch, V0 nothing. *)
let view v s =
  match v with
  | Validator.V0 | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7
  | Validator.V8 | Validator.V9 ->
      Vw_idle
  | Validator.V1 -> Vw_requester (s.req_to, s.cache)
  | Validator.V2 -> Vw_honest_holder
  | Validator.V3 -> Vw_byz s.v3_mode

(* Gate deletion for the confirm-by-mutation pin: [No_digest_gate] deletes
   the requester-side digest verification (state-sync consensus.rs:84-87,
   the [header.digest() != hash] reject that precedes the [ConsensusCache]
   insert at consensus.rs:89), so a fabricated response caches exactly like
   a valid one. No sibling path silently repairs the deletion: the
   responder-side Deny gate (sync_codec.rs:320-347) is the honest
   responder's self-check, which a fabricating V3 never runs, and retrying
   another peer is a separate run - the Verifying transition is
   self-contained, so the refuting cached-bogus state is genuinely
   reachable under the mutation. *)
type mutation = Pristine | No_digest_gate

(* Init: resolve the hidden peer choice and (iff V3 is engaged) the hidden
   Byzantine branch, and record the request V1 issued
   (request_consensus_output, state-sync consensus.rs:63-64; stream bound
   to the chosen peer, mod.rs:714-722). *)
let resolve target mode state =
  {
    state with
    phase = Serving;
    target;
    v3_mode = mode;
    req_to = responder_of target;
  }

(* The Init branch fan-out. Under [T_v2] the Byzantine branch stays
   [M_unchosen]: V3 is never engaged, so its hidden branch never resolves -
   the lean pin the family spec allows, keeping the honest-responder run to
   one branch. The Genuine, Withhold, Deny, AND Fabricate branches under
   [T_v3] are all mandatory: Deny and Fabricate populate the unheld
   false-witness members of V1's pre-verification view class, Fabricate
   must be reachable in the PRISTINE model so the digest gate
   (consensus.rs:84-87) is exercised through its Retry arm rather than
   sitting dead, and Withhold keeps the holds-and-denies run
   (mod.rs:791-795, :1892-1910) reachable so possession never hardwires to
   cooperation - an asked-and-possessing V3 may conclude the fetch
   unverified. *)
let init_branches =
  [
    (T_v2, M_unchosen);
    (T_v3, Genuine);
    (T_v3, Withhold);
    (T_v3, Deny);
    (T_v3, Fabricate);
  ]

(* Serving: the addressed responder answers. Honest V2 serves the bytes it
   locally holds (handler.rs:963-988, storage consensus.rs:882-904); V3
   answers per its hidden branch - faithful bytes, a Deny frame while
   holding (load-shed, mod.rs:791-795, :1892-1910) or while lacking
   (sync_codec.rs:330-347), or digest-invalid bytes. An unaddressed serve
   (unreachable: Init always resolves a target) answers nothing, keeping
   the function total. *)
let serve state =
  let answer j =
    match j with
    | Resp_v2 -> Valid Resp_v2
    | Resp_v3 -> (
        match state.v3_mode with
        | M_unchosen -> R_none
        | Genuine -> Valid Resp_v3
        | Withhold -> Denied Resp_v3
        | Deny -> Denied Resp_v3
        | Fabricate -> Bogus Resp_v3)
  in
  {
    state with
    phase = Verifying;
    response = Option.fold ~none:R_none ~some:answer state.req_to;
  }

(* Verifying: the requester-side gate. Valid bytes cache (the
   [ConsensusCache] insert, consensus.rs:89); digest-invalid bytes are
   rejected by the gate (consensus.rs:84-87) and the requester Retries -
   modeled self-contained as staying Uncached, no fall-through refetch; a
   Deny leaves the cache untouched (the requester tries elsewhere,
   mod.rs:774-806). Under [No_digest_gate] the Bogus payload caches like a
   Valid one. *)
let verify mut state =
  let cached =
    match state.response with
    | R_none -> Uncached
    | Valid j -> Cached_from j
    | Bogus j -> (
        match mut with Pristine -> Uncached | No_digest_gate -> Cached_from j)
    | Denied Resp_v2 -> Uncached
    | Denied Resp_v3 -> Uncached
  in
  { state with phase = Done; cache = cached }

(* The transition relation, parameterized by the gate deletion. Terminal
   [Done] returns [] and the kernel stutter-closes it. *)
let next_with mut state =
  match state.phase with
  | Init ->
      List.map (fun (target, mode) -> resolve target mode state) init_branches
  | Serving -> [ serve state ]
  | Verifying -> [ verify mut state ]
  | Done -> []

(* The pristine transition relation. *)
let next = next_with Pristine

(* The atom vocabulary the statement quantifies over.
   [Verified_from j]: V1's cache holds a digest-verified output served by j
   (insert only after the gate, consensus.rs:84-89).
   [Pending_from j]: V1 requested from j and holds nothing verified yet
   (the outstanding fetch of mod.rs:774-806).
   [Held j]: responder-side possession of the exact requested bytes -
   rigidly true for honest V2 (local pack read, storage
   consensus.rs:882-904), and for V3 the hidden Genuine and Withhold
   branches: possession is independent of cooperation (a holder may shed
   with a Deny frame, mod.rs:791-795, :1892-1910), and only a possessing
   branch can produce bytes matching the already-verified digest, while a
   denying or fabricating V3 lacks them.
   [At_done]: the fetch concluded. *)
type atom =
  | Verified_from of responder
  | Pending_from of responder
  | Held of responder
  | At_done

(* Atom valuation over global states. *)
let label a state =
  match a with
  | Verified_from j ->
      Option.fold ~none:false ~some:(responder_equal j)
        (cached_responder state.cache)
  | Pending_from j ->
      Option.fold ~none:false ~some:(responder_equal j) state.req_to
      && Option.is_none (cached_responder state.cache)
  | Held Resp_v2 -> true
  | Held Resp_v3 -> (
      match state.v3_mode with
      | M_unchosen -> false
      | Genuine -> true
      | Withhold -> true
      | Deny -> false
      | Fabricate -> false)
  | At_done -> (
      match state.phase with
      | Init -> false
      | Serving -> false
      | Verifying -> false
      | Done -> true)

(* Rendering for theorem and formula pretty-printing. *)
let atom_to_string = function
  | Verified_from j -> "verified-from(" ^ responder_to_string j ^ ")"
  | Pending_from j -> "pending-from(" ^ responder_to_string j ^ ")"
  | Held j -> "held(" ^ responder_to_string j ^ ")"
  | At_done -> "done"

(* The kernel instance for this family: exact CTLK checking over the
   reqres reachable graph (16 states pristine). *)
module Checker = System.Make (State) (View)

(* The spec under a chosen gate deletion. *)
let spec_of mut = { Checker.init = [ initial ]; next = next_with mut; view; label }

(* The pristine spec. *)
let spec = spec_of Pristine

(* Build the pristine interpreted system. *)
let make () = Checker.make spec
