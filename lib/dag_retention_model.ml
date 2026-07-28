(** Finite interpreted system for the DAG_RETENTION family: the resident dag of
    ONE validator's [ConsensusState] and the three different gates that read and
    write the same [last_committed] map over it. File citations refer to
    Telcoin-Association/telcoin-network at the working tree of git HEAD
    0c59c15b, and every one of them was opened in that checkout.

    THE MODELED MECHANISM. [ConsensusState] (state.rs:30-46) carries four
    coupled fields: [last_round] (the committed round and its gc round),
    [last_committed : HashMap<AuthorityIdentifier, Round>] - documented at
    state.rs:37-38 as the map that ensures "we don't commit twice the same
    certificate" - [last_committed_sub_dag] (the LAST committed sub-dag only)
    and [dag]. The dag deliberately RETAINS committed certificates: [update]
    purges with [self.dag.retain(|r, _| *r > self.last_round.gc_round)]
    (state.rs:182-183) and the default [gc_depth] is [MAX_GC_DEPTH = 50]
    (node.rs:302-305, types/src/primary/mod.rs:45), so in any window of a few
    rounds [gc_round] saturates to 0 and NOTHING is purged. Retention is what
    makes the two dedup gates load-bearing, and it is also what makes the
    straggler of S3 insertable at all - which is why all three statements share
    one model.

    The three gates, all reading [last_committed] or [committed_round]:

    - the WALK SKIP (utils.rs:33-44). [order_dag] is a DFS from the leader.
      Line 15-21 pushes whatever it pops into [ordered] unconditionally - so
      the walk ROOT is never deduped - and only the PARENTS are filtered:
      [skip = already_ordered.contains(&digest)] then
      [skip |= last_committed.get(origin).map_or_else(|| false, |r| &round <= r)].
      [already_ordered] is created fresh per call (utils.rs:16), so it dedups
      only WITHIN one walk; the [last_committed] disjunct is the only thing
      that dedups ACROSS walks, and [state.update] advances [last_committed]
      per sequenced certificate (state.rs:164-168) after each walk
      (bullshark.rs:224-233).
    - the LEADER SHORT-CIRCUIT (bullshark.rs:133-138).
      [if leader_round <= state.last_round.committed_round { return
      Ok((Outcome::LeaderBelowCommitRound, Vec::new())) }] - the single
      comparison that stops an already-committed leader round from being
      re-elected by a late certificate.
    - the ALWAYS-INSERT (state.rs:143-148), whose own comment reads "Always
      insert the certificate even if it is below last committed round of its
      origin, to allow verifying parent existence." The suppression of the
      election is carried by the RETURN VALUE instead
      ([Ok(round > last_committed[origin])], state.rs:159-160), which
      bullshark.rs:116-119 turns into [Outcome::CertificateBelowCommitRound].

    THE SCENARIO. Four authorities A, B, C, D, [f = 1]; [validity_threshold]
    is [ceil(4/3) = 2 = f + 1] (committee.rs:254-259). The round-2 leader is
    A's round-2 certificate L2; the round-4 leader is B's round-4 certificate
    L4. D is slow: it proposed its round-3 header off A's, B's and C's round-2
    certificates before its OWN round-2 certificate had collected its votes, so
    D3 does not name D2 among its parents. V0 therefore commits L4's sub-dag -
    which sequences B3, C3, D3 and their round-2 parents - and
    [last_committed[D]] becomes 3 while D2 has never been seen. D2 then
    arrives: [2 <= 3], the below-commit case, and the always-insert is the only
    reason it enters the dag. A, meanwhile, DID wait for D2 and its round-3
    certificate A3 names it among its [2f + 1] parents; when A3 arrives,
    [check_parents] (state.rs:198-208) demands D2 in [dag[2]] or returns
    [ConsensusError::MissingParent], which [new_certificate] propagates with
    [?] (state.rs:373-375) out of [run] - a [spawn_critical_task]
    (state.rs:347-349). A3 is also the only late certificate that can re-elect
    the round-2 leader: [r = 3 - 1 = 2] is even and [>= 2] (bullshark.rs:126-131)
    and A3 is above ITS origin's committed round ([3 > last_committed[A] = 2]),
    so it clears bullshark.rs:116-119 and reaches the leader short-circuit.
    One certificate, three gates.

    COMPONENTS.
    - [phase]: how far V0's commits have got. [Ph_open] nothing committed;
      [Ph_leader2] L2's sub-dag committed ([committed_round = 2]);
      [Ph_leader4] L4's sub-dag committed ([committed_round = 4],
      [last_committed[D] = 3]). The round-4 leader is elected by a ROUND-5
      certificate, since bullshark.rs:126-131 elects for [r = round - 1].
    - [strag]: D's round-2 certificate - in flight / resident in V0's dag /
      refused by the mutated insert gate.
    - [child]: A's round-3 certificate - in flight / resident / rejected with
      [MissingParent], which kills the critical consensus task.
    - [c1]: how many committed sub-dags have carried A's ROUND-1 certificate,
      an ancestor of L2 and (through D3 -> A2 = L2 -> A1) of L4.
    - [anchor]: how many committed sub-dags have been anchored on L2.
    - [peer_a], [peer_c]: the two hidden facts about other nodes' possession.

    ROLE MAPPING. [Validator.V0] is the local CVV whose [ConsensusState] this
    is, and it is the ONLY knowledge agent: its view is the projection of that
    struct - the phase, whether D2 is resident in the dag, what A3 looks like
    once resident (including its parent list, which the dag stores in full),
    and the sub-dag bookkeeping it emitted on its own [sequence] channel.
    [Validator.V1], [Validator.V2] and [Validator.V3] stand for the peer
    authorities A, C and D, whose local state this family does not model at
    all, and [Validator.V4] .. [Validator.V9] are outside this family's
    four-member roster (the isolated families keep their original four-member
    semantics, validator.mli:8-11); all nine carry the constant blank view
    [View_idle] and NEVER appear under [K].

    WHY THE VIEW PROJECTION IS WHAT IT IS. Two facts are outside the struct and
    outside every message V0 has received:
    - [peer_a]: whether A possessed D2 when it proposed its round-3 header, i.e.
      whether A3 names D2 among its parents. V0 learns this exactly when A3
      becomes resident, because the dag stores whole certificates and
      [check_parents] reads [certificate.header().parents()]
      (state.rs:201-202). Before that, nothing V0 holds mentions D2.
    - [peer_c]: whether C also possesses D2. C's round-3 certificate was
      certified and delivered to V0 before D2 finished assembling, so C's
      possession leaves NO trace in anything V0 sees in this window. Nothing in
      this model reads or writes [peer_c]: it is the residual propagation
      branch V0 can never resolve, and it is what keeps the [K] of S3 conjunct
      C a real quantification over two worlds instead of a lookup. It plays the
      same role {!Pending_gc_model.peer_d} plays in the PENDING_GC family.

    UPSTREAM CAUSAL DELIVERY IS MODELED, NOT OMITTED. The certificate manager
    forwards a certificate to consensus only after accepting every parent -
    cert_manager.rs:103-118 with its own comment at :106-107 ("this also
    ensures certificates are accepted in causal order which is a strict
    requirement for consensus to build the DAG correctly"), then
    [accept_verified_certificates] (cert_manager.rs:189-220) writing to storage
    at :196 and forwarding at :214. {!child_upstream_ready} is exactly that
    gate. It does NOT repair {!Insert_gated_on_last_committed}, because it
    checks the certificate STORE while the mutation drops the certificate from
    the CONSENSUS dag - so upstream still hands A3 over, and consensus still
    fails to find its parent. That asymmetry is the whole point of S3. *)

(** Whether authority A possessed D's round-2 certificate when it proposed its
    round-3 header - equivalently, whether A3 names D2 among its [2f + 1]
    parents (state.rs:201-202 reads that list). Frozen at init: A3 already
    exists and is in flight. *)
type peer_a = A_names_parent | A_omits_parent

(** Total order index for {!peer_a}. *)
let peer_a_index = function A_names_parent -> 0 | A_omits_parent -> 1

(** Total order on {!peer_a}. *)
let peer_a_compare a b = Int.compare (peer_a_index a) (peer_a_index b)

(** Whether authority C also possesses D's round-2 certificate. Frozen at init
    and read by nothing: C's round-3 certificate was delivered before D2
    finished assembling, so this possession leaves no trace in V0's
    [ConsensusState]. It is the hidden branch that keeps V0's knowledge from
    collapsing into its own dag. *)
type peer_c = C_holds_parent | C_without_parent

(** Total order index for {!peer_c}. *)
let peer_c_index = function C_holds_parent -> 0 | C_without_parent -> 1

(** Total order on {!peer_c}. *)
let peer_c_compare a b = Int.compare (peer_c_index a) (peer_c_index b)

(** How far V0's commits have advanced. [Ph_open]: nothing committed,
    [committed_round = 0]. [Ph_leader2]: L2's sub-dag committed,
    [committed_round = 2]. [Ph_leader4]: L4's sub-dag committed,
    [committed_round = 4] and [last_committed[D] = 3], so D's round-2
    certificate is now BELOW its origin's committed round
    (bullshark.rs:141-152, state.rs:164-169). *)
type phase = Ph_open | Ph_leader2 | Ph_leader4

(** Total order index for {!phase}. *)
let phase_index = function Ph_open -> 0 | Ph_leader2 -> 1 | Ph_leader4 -> 2

(** Total order on {!phase}. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** D's round-2 certificate, the leapfrogged straggler. [S_inflight]: assembled
    late, not yet delivered to V0. [S_resident]: inserted into V0's dag
    (state.rs:145-148). [S_refused]: delivered but dropped, which only the
    {!Insert_gated_on_last_committed} mutation can produce. *)
type strag = S_inflight | S_resident | S_refused

(** Total order index for {!strag}. *)
let strag_index = function S_inflight -> 0 | S_resident -> 1 | S_refused -> 2

(** Total order on {!strag}. *)
let strag_compare a b = Int.compare (strag_index a) (strag_index b)

(** A's round-3 certificate, the late child and the only late certificate that
    can re-trigger the round-2 leader election. [Ch_inflight]: certified and en
    route (delivery is therefore inevitable, which is what makes the [Af] of S3
    honest). [Ch_resident]: inserted. [Ch_fatal]: rejected with
    [ConsensusError::MissingParent] (state.rs:203-206), which propagates out of
    [run] (state.rs:373-375) and ends the critical consensus task
    (state.rs:347-349). *)
type child = Ch_inflight | Ch_resident | Ch_fatal

(** Total order index for {!child}. *)
let child_index = function Ch_inflight -> 0 | Ch_resident -> 1 | Ch_fatal -> 2

(** Total order on {!child}. *)
let child_compare a b = Int.compare (child_index a) (child_index b)

(** How many committed sub-dags have carried A's round-1 certificate [c1],
    saturating at two. [Seq_twice] is the double-delivery to execution that the
    walk skip forbids. *)
type seq = Seq_none | Seq_once | Seq_twice

(** Total order index for {!seq}. *)
let seq_index = function Seq_none -> 0 | Seq_once -> 1 | Seq_twice -> 2

(** Total order on {!seq}. *)
let seq_compare a b = Int.compare (seq_index a) (seq_index b)

(** How many committed sub-dags have been ANCHORED on the round-2 leader L2,
    saturating at two. [An_twice] is a second [CommittedSubDag] carrying the
    same leader nonce (bullshark.rs:218, :240-246). *)
type anchor = An_none | An_once | An_twice

(** Total order index for {!anchor}. *)
let anchor_index = function An_none -> 0 | An_once -> 1 | An_twice -> 2

(** Total order on {!anchor}. *)
let anchor_compare a b = Int.compare (anchor_index a) (anchor_index b)

(** The joint global state: two frozen hidden peer-possession facts and five
    components of V0's own [ConsensusState] and output trace. *)
type state = {
  peer_a : peer_a;
  peer_c : peer_c;
  phase : phase;
  strag : strag;
  child : child;
  c1 : seq;
  anchor : anchor;
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = peer_a_compare s1.peer_a s2.peer_a in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = peer_c_compare s1.peer_c s2.peer_c in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = phase_compare s1.phase s2.phase in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = strag_compare s1.strag s2.strag in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = child_compare s1.child s2.child in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = seq_compare s1.c1 s2.c1 in
            if Bool.not (Int.equal c5 0) then c5
            else anchor_compare s1.anchor s2.anchor

(** The ordered state module for {!Denote.Make}. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** Whether a certificate is present in V0's dag, as V0 sees it: a certificate
    that was delivered and refused is indistinguishable from one that never
    arrived, because [ConsensusState] records only what the dag holds. *)
type slot = Slot_absent | Slot_resident

(** Total order index for {!slot}. *)
let slot_index = function Slot_absent -> 0 | Slot_resident -> 1

(** Total order on {!slot}. *)
let slot_compare a b = Int.compare (slot_index a) (slot_index b)

(** What V0 sees of the late child A3. [Cv_awaited]: not in the dag.
    [Cv_resident_plain]: resident and naming A2, B2, C2 as its parents.
    [Cv_resident_citing]: resident and naming D2 - the dag stores whole
    certificates, so the parent list is visible (state.rs:201-202).
    [Cv_lost]: the consensus task died on it. *)
type child_view =
  | Cv_awaited
  | Cv_resident_plain
  | Cv_resident_citing
  | Cv_lost

(** Total order index for {!child_view}. *)
let child_view_index = function
  | Cv_awaited -> 0
  | Cv_resident_plain -> 1
  | Cv_resident_citing -> 2
  | Cv_lost -> 3

(** Total order on {!child_view}. *)
let child_view_compare a b =
  Int.compare (child_view_index a) (child_view_index b)

(** A validator's local view. [View_consensus] is V0's [ConsensusState]
    projection plus the sub-dag trace it emitted itself; it does NOT carry
    [peer_a] or [peer_c], which are facts about other nodes' possession.
    [View_idle] is the constant blank view of the peer authorities, whose local
    state this family does not model. *)
type view =
  | View_consensus of phase * slot * child_view * seq * anchor
  | View_idle

(** Total order on the {!View_consensus} payload, field by field. *)
let view_consensus_compare (p, sl, cv, sq, an) (p', sl', cv', sq', an') =
  let c = phase_compare p p' in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = slot_compare sl sl' in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = child_view_compare cv cv' in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = seq_compare sq sq' in
        if Bool.not (Int.equal c3 0) then c3 else anchor_compare an an'

(** Total order on views: every constructor spelled, no wildcard arm. *)
let view_compare a b =
  match (a, b) with
  | View_idle, View_idle -> 0
  | View_idle, View_consensus _ -> -1
  | View_consensus _, View_idle -> 1
  | View_consensus (p, sl, cv, sq, an), View_consensus (p', sl', cv', sq', an')
    ->
      view_consensus_compare (p, sl, cv, sq, an) (p', sl', cv', sq', an')

(** The ordered view module for {!Denote.Make}. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** Is D's round-2 certificate in V0's dag? [S_refused] reads as absent: the
    struct has no record of a refusal. *)
let straggler_slot s =
  match s.strag with
  | S_resident -> Slot_resident
  | S_inflight | S_refused -> Slot_absent

(** What V0 sees of A3. Once resident, its parent list is in the dag, so
    [peer_a] is revealed exactly there and nowhere earlier. *)
let child_view_of s =
  match s.child with
  | Ch_inflight -> Cv_awaited
  | Ch_fatal -> Cv_lost
  | Ch_resident -> (
      match s.peer_a with
      | A_names_parent -> Cv_resident_citing
      | A_omits_parent -> Cv_resident_plain)

(** View projection. V0 is the local CVV and the only knowledge agent; V1, V2
    and V3 stand for the peer authorities A, C and D, whose local state this
    family does not model, and V4..V9 are outside this family's four-member
    roster entirely. All nine are idle non-agents with the constant blank view
    and never appear under [K]. *)
let view v s =
  match v with
  | Validator.V0 ->
      View_consensus
        (s.phase, straggler_slot s, child_view_of s, s.c1, s.anchor)
  | Validator.V1 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      View_idle

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | No_last_committed_skip
      (** delete the [last_committed] disjunct of the walk skip
          (utils.rs:37-40), so [order_dag] re-pushes parents that an earlier
          sub-dag already sequenced. Adds
          (Ph_leader2, c1 = Seq_once) -> (Ph_leader4, c1 = Seq_twice): L4's
          walk descends through D3 into A2 = L2 and on into A1 = c1, which the
          pristine skip stops dead. NO SIBLING REPAIRS IT: [already_ordered] is
          built fresh per call (utils.rs:16) so it dedups only within one walk;
          [dag.retain] keeps every committed certificate until
          [round <= gc_round] (state.rs:182-183) and [gc_round] is 0 here
          (node.rs:302-305, primary/mod.rs:45), so nothing is physically
          removed; try_insert's below-commit return (state.rs:159-160,
          bullshark.rs:116-119) only suppresses ELECTIONS for newly ARRIVING
          certificates and never filters a walk; and [save_consensus]
          (state-sync/src/lib.rs:105-114) writes the output with no
          uniqueness check. *)
  | No_below_commit_shortcircuit
      (** delete the leader short-circuit (bullshark.rs:136-138), so a late
          certificate re-elects an already-committed leader round. Adds
          (phase >= Ph_leader2, child = Ch_inflight) ->
          (child = Ch_resident, anchor = An_twice): A3 arrives, [r = 2] is even
          and [>= 2], and [commit_leader 2] runs again. NO SIBLING REPAIRS IT:
          A3 is at round 3, ABOVE [last_committed[A] = 2], so
          bullshark.rs:116-119 passes it through; L2 is still in the dag
          (state.rs:182-183); the support recount at bullshark.rs:192-206 sees
          the same round-3 certificates and still clears
          [validity_threshold = 2] (committee.rs:254-259);
          [order_leaders]'s range [committed_round + 2 ..= leader_round - 2] is
          empty (bullshark.rs:290) so [to_commit = [L2]]; [order_dag] pushes
          the walk ROOT into [ordered] with no skip check at all
          (utils.rs:15-21); [wait_for_execution] (state.rs:421-434) passes
          because the re-committed leader's [latest_execution_block] is old and
          execution is already past it; and the [assert_eq] at state.rs:470
          still holds because [committed_round] is unchanged. *)
  | Insert_gated_on_last_committed
      (** guard the dag insertion with [round > last_committed[origin]],
          deleting the always-insert semantics of state.rs:143-148. Adds
          (Ph_leader4, S_inflight) -> (Ph_leader4, S_refused) and hence
          (Ch_inflight) -> (Ch_fatal). NO SIBLING REPAIRS IT: [check_parents]'
          horizon skip exempts only [round <= gc_round + 1 = 1]
          (state.rs:195-197) and A3 is at round 3; [order_dag]'s tolerant
          [None] arm (utils.rs:46) never runs because [check_parents] errors
          first, at INSERT time; [ConsensusError::MissingParent]
          (consensus/mod.rs:35) is constructed at state.rs:203 and matched
          NOWHERE, so there is no catch or retry in [run]/[new_certificate];
          the recovery path shares the very function being mutated
          ([construct_dag_from_cert_store] calls [try_insert_in_dag],
          state.rs:102), so a restart inherits the drop rather than repairing
          it; and upstream causal delivery (cert_manager.rs:103-124, modeled
          here as {!child_upstream_ready}) checks the certificate STORE, not
          the consensus dag, so it still hands A3 over. *)

(** COMMIT_L2: a round-3 certificate carrying [f + 1 = 2] support for L2
    arrives, [r = 2] is even and above [committed_round = 0]
    (bullshark.rs:126-138), the support check clears
    [validity_threshold] (bullshark.rs:192-206, committee.rs:254-259) and
    [order_dag] sequences L2 together with its round-1 parents, [c1] among them
    (utils.rs:15-48). [state.update] then advances [last_committed] and
    [committed_round] (state.rs:164-169). *)
let commit_leader2_step s =
  match s.phase with
  | Ph_open ->
      [ { s with phase = Ph_leader2; c1 = Seq_once; anchor = An_once } ]
  | Ph_leader2 | Ph_leader4 -> []

(** Does L4's walk re-sequence [c1]? Under the pristine skip it does not: the
    walk reaches A2 = L2 as a parent of D3 and stops, because
    [2 <= last_committed[A] = 2] (utils.rs:37-40). With the skip deleted it
    descends into L2's round-1 parents and [c1] is delivered a second time. *)
let walk_resequences_c1 mut current =
  match mut with
  | No_last_committed_skip -> Seq_twice
  | Pristine | No_below_commit_shortcircuit | Insert_gated_on_last_committed ->
      current

(** COMMIT_L4: a ROUND-5 certificate arrives, so [r = 4] is the elected leader
    round (bullshark.rs:126-131), it is above [committed_round = 2], and L4's
    sub-dag is committed. [order_leaders]' range
    [committed_round + 2 ..= leader_round - 2] is [4 ..= 2], i.e. empty
    (bullshark.rs:290), so no earlier leader is back-committed and
    [to_commit = [L4]]. The walk sequences B3, C3, D3 and their round-2
    parents; [last_committed[D]] becomes 3, which is what leapfrogs D2. *)
let commit_leader4_step mut s =
  match s.phase with
  | Ph_leader2 ->
      [ { s with phase = Ph_leader4; c1 = walk_resequences_c1 mut s.c1 } ]
  | Ph_open | Ph_leader4 -> []

(** Where D2 lands when it is delivered. Before L4's commit its round is ABOVE
    its origin's committed round ([2 > last_committed[D] <= 1]), so every
    variant inserts it - the mutation is inert there, exactly as the real guard
    would be. At [Ph_leader4] it is the below-commit case ([2 <= 3]) and only
    the always-insert of state.rs:143-148 keeps it. *)
let straggler_landing mut ph =
  match ph with
  | Ph_open | Ph_leader2 -> S_resident
  | Ph_leader4 -> (
      match mut with
      | Insert_gated_on_last_committed -> S_refused
      | Pristine | No_last_committed_skip | No_below_commit_shortcircuit ->
          S_resident)

(** DELIVER_STRAGGLER: D's round-2 certificate reaches [process_certificate]
    (bullshark.rs:107-119) and goes through [try_insert] (state.rs:114-161).
    It never triggers an election in any variant: at [Ph_open]/[Ph_leader2] it
    yields [r = 1], which is odd (bullshark.rs:129-131), and at [Ph_leader4]
    it returns false from try_insert and stops at bullshark.rs:116-119. *)
let deliver_straggler_step mut s =
  match s.strag with
  | S_inflight -> [ { s with strag = straggler_landing mut s.phase } ]
  | S_resident | S_refused -> []

(** The upstream gate: the certificate manager forwards A3 to consensus only
    once it has accepted every parent (cert_manager.rs:103-118, comment at
    :106-107; :189-220 writes at :196 and forwards at :214). It reads the
    certificate STORE, so a certificate the consensus dag dropped still counts
    as accepted here - which is why this repair path cannot cover for
    {!Insert_gated_on_last_committed}. *)
let child_upstream_ready s =
  match s.peer_a with
  | A_omits_parent -> true
  | A_names_parent -> (
      match s.strag with
      | S_resident | S_refused -> true
      | S_inflight -> false)

(** The consensus-side gate: [check_parents] demands every named parent in
    [dag[round - 1]] or returns [ConsensusError::MissingParent]
    (state.rs:198-208). Its horizon exemption is [round <= gc_round + 1 = 1]
    (state.rs:195-197) and A3 is at round 3, so it does not apply. *)
let child_parents_present s =
  match s.peer_a with
  | A_omits_parent -> true
  | A_names_parent -> (
      match s.strag with
      | S_resident -> true
      | S_inflight | S_refused -> false)

(** Does A3's insertion re-anchor L2? Only with the short-circuit deleted, and
    only once L2 has been committed: at [Ph_open] the election for [r = 2] runs
    but [commit_leader] finds A3's lone vote below [validity_threshold = 2] and
    returns [Outcome::NotEnoughSupportForLeader] (bullshark.rs:203-206). *)
let reanchor mut ph current =
  match mut with
  | No_below_commit_shortcircuit -> (
      match ph with Ph_leader2 | Ph_leader4 -> An_twice | Ph_open -> current)
  | Pristine | No_last_committed_skip | Insert_gated_on_last_committed ->
      current

(** DELIVER_CHILD: A's round-3 certificate reaches consensus. It is inserted
    when its parents are present, and it is the trigger the leader
    short-circuit exists for. When the parents are NOT present - which only the
    insert mutation can arrange - [check_parents] errors and the critical
    consensus task exits (state.rs:203-206, :373-375, :347-349). *)
let deliver_child_step mut s =
  match s.child with
  | Ch_inflight ->
      if Bool.not (child_upstream_ready s) then []
      else if child_parents_present s then
        [ { s with child = Ch_resident; anchor = reanchor mut s.phase s.anchor } ]
      else [ { s with child = Ch_fatal } ]
  | Ch_resident | Ch_fatal -> []

(** The transition relation: the four single-step rules, each contributing the
    empty list when disabled, and nothing at all once the consensus task has
    exited. Every component is monotone, so the reachable graph is a finite
    DAG whose only stuttering states are fully advanced ones - which is what
    makes S3's [Af] honest and what makes the
    {!Insert_gated_on_last_committed} pin bite, since it creates a stuttering
    state in which the child is dead instead of resident. *)
let next_with mut s =
  match s.child with
  | Ch_fatal -> []
  | Ch_inflight | Ch_resident ->
      List.concat
        [
          commit_leader2_step s;
          commit_leader4_step mut s;
          deliver_straggler_step mut s;
          deliver_child_step mut s;
        ]

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state of the world in which A did NOT wait for D2 (its round-3
    certificate names A2, B2, C2) and C does not hold D2 either: nothing is
    committed, D2 is still assembling, A3 is certified and in flight. *)
let initial =
  {
    peer_a = A_omits_parent;
    peer_c = C_without_parent;
    phase = Ph_open;
    strag = S_inflight;
    child = Ch_inflight;
    c1 = Seq_none;
    anchor = An_none;
  }

(** Sibling init: A still did not wait for D2, but C does hold it. Differs from
    {!initial} only in the frozen hidden bit no channel reports. *)
let initial_peer_c_holds = { initial with peer_c = C_holds_parent }

(** Sibling init: A DID wait for D2 and named it among A3's parents, while C
    does not hold it. This is the branch in which the always-insert is
    load-bearing. *)
let initial_peer_a_names = { initial with peer_a = A_names_parent }

(** Sibling init: A named D2 among A3's parents AND C holds D2. The pair
    {!initial_peer_a_names} / this state is what stops V0's knowledge of A's
    possession from being a lookup: at the state where A3 has arrived citing
    D2, these two worlds are still indistinguishable to V0. *)
let initial_peer_a_names_c_holds =
  { initial with peer_a = A_names_parent; peer_c = C_holds_parent }

(** The atom vocabulary this family's statements quantify over. *)
type atom =
  | Leader2_committed
      (** phase >= Ph_leader2 : a sub-dag anchored on the round-2 leader has
          been committed (committed_leader(L2)) *)
  | Leader2_reanchored
      (** anchor = An_twice : a SECOND sub-dag carrying L2's nonce has been
          committed (reanchored(L2)) *)
  | C1_sequenced
      (** c1 >= Seq_once : A's round-1 certificate has been carried by a
          committed sub-dag (sequenced(c1)) *)
  | C1_resequenced
      (** c1 = Seq_twice : it has been carried by a SECOND committed sub-dag
          (resequenced(c1)) *)
  | Leapfrogged
      (** phase = Ph_leader4 : last_committed[D] = 3 has passed D2's round, so
          D2 is below its origin's committed round (leapfrogged(D2)) *)
  | Straggler_resident
      (** strag = S_resident : D2 is in V0's dag (resident(D2)) *)
  | Child_resident
      (** child = Ch_resident : A3 is in V0's dag (resident(A3)) *)
  | Child_cites_straggler
      (** child = Ch_resident and peer_a = A_names_parent : the resident A3
          names D2 among its parents - a fact V0 reads off the certificate
          (cites(A3, D2)) *)
  | Consensus_dead
      (** child = Ch_fatal : the critical consensus task exited on
          ConsensusError::MissingParent (dead(consensus)) *)
  | Peer_a_holds_straggler
      (** peer_a = A_names_parent : authority A possessed D2 when it proposed
          its round-3 header (holds_A(D2)) - the hidden possession fact *)
  | Peer_c_holds_straggler
      (** peer_c = C_holds_parent : authority C also possesses D2
          (holds_C(D2)) - the hidden branch nothing in this window reports *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Leader2_committed -> (
      match s.phase with
      | Ph_leader2 | Ph_leader4 -> true
      | Ph_open -> false)
  | Leader2_reanchored -> (
      match s.anchor with An_twice -> true | An_none | An_once -> false)
  | C1_sequenced -> (
      match s.c1 with Seq_once | Seq_twice -> true | Seq_none -> false)
  | C1_resequenced -> (
      match s.c1 with Seq_twice -> true | Seq_none | Seq_once -> false)
  | Leapfrogged -> (
      match s.phase with
      | Ph_leader4 -> true
      | Ph_open | Ph_leader2 -> false)
  | Straggler_resident -> (
      match s.strag with
      | S_resident -> true
      | S_inflight | S_refused -> false)
  | Child_resident -> (
      match s.child with
      | Ch_resident -> true
      | Ch_inflight | Ch_fatal -> false)
  | Child_cites_straggler -> (
      match child_view_of s with
      | Cv_resident_citing -> true
      | Cv_awaited | Cv_resident_plain | Cv_lost -> false)
  | Consensus_dead -> (
      match s.child with
      | Ch_fatal -> true
      | Ch_inflight | Ch_resident -> false)
  | Peer_a_holds_straggler -> (
      match s.peer_a with
      | A_names_parent -> true
      | A_omits_parent -> false)
  | Peer_c_holds_straggler -> (
      match s.peer_c with
      | C_holds_parent -> true
      | C_without_parent -> false)

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Leader2_committed -> "committed_leader(L2)"
  | Leader2_reanchored -> "reanchored(L2)"
  | C1_sequenced -> "sequenced(c1)"
  | C1_resequenced -> "resequenced(c1)"
  | Leapfrogged -> "leapfrogged(D2)"
  | Straggler_resident -> "resident(D2)"
  | Child_resident -> "resident(A3)"
  | Child_cites_straggler -> "cites(A3,D2)"
  | Consensus_dead -> "dead(consensus)"
  | Peer_a_holds_straggler -> "holds_A(D2)"
  | Peer_c_holds_straggler -> "holds_C(D2)"

(** The CTLK checker over this family's ordered state and view: the
    presheaf-topos denotation ({!Denote}, lib/internal/DESIGN.md), pinned to
    agree with {!System} at every reachable world by
    test/t_dag_retention_topos.ml. *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: the four initial states (the frozen
    hidden peer branches), mutation-parameterized transitions, the
    one-agent-plus-three-idle view projection, the atom valuation. *)
let spec_of mut =
  {
    Checker.init =
      [
        initial;
        initial_peer_c_holds;
        initial_peer_a_names;
        initial_peer_a_names_c_holds;
      ];
    next = next_with mut;
    view;
    label;
  }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
