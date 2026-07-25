(** Transition function, atoms, and checker instance for the telcoin-network
    abstraction in {!Tn_state}.

    Faithfulness notes, keyed to the mechanisms the statements cite:
    - votes gate on BATCH possession (the batch-validator availability gate,
      worker handler.rs:231-263 / validator.rs:39-81); missing parents are
      fetched at vote time (the synchronizer, handler.rs:693-738), so a
      delayed certificate delivery defers knowledge, never liveness;
    - vote-once per slot (handler.rs:787-847): an honest validator never
      signs two variants of one slot, which is what makes conflicting
      certificates impossible at f = 1 (3 + 3 votes from 4 validators need
      two double voters, and only V3 double-votes);
    - certificates exist only when the model has assembled quorum votes
      (votes.rs:42-89 / certificate.rs:225-251, unforgeability by
      construction);
    - the anchor (V0's R1 header) commits iff f+1 = 2 R2 certificates
      reference it as parent, evaluated by each validator on ITS OWN DAG
      view (bullshark.rs:192-206); agreement is a checked property, not a
      construction;
    - liveness verdicts are under bounded-delay fairness: every broadcast is
      delivered by the next Deliver phase (the one modeled delay defers the
      anchor by exactly one round, forced at Deliver R2), and the phase
      machine never idles.

    [mutation] is the confirm-by-mutation harness: each variant deletes one
    gate the statements depend on, and the paired test asserts that exactly
    the statements pinned to that gate flip to refuted while the pristine
    model proves all seven. *)

open Tn_state

let honest = [ Validator.V0; Validator.V1; Validator.V2 ]

let byz = Validator.V3

let leader = Validator.V0

let anchor = { author = leader; round = R1; variant = A }

let is_honest v = List.exists (fun h -> Validator.equal h v) honest

(* Gate deletions for confirm-by-mutation tests. *)
type mutation =
  | Pristine
  | Drop_batch_gate  (** honest voters skip the availability check *)
  | Weak_quorum  (** certificates form at 2 votes instead of 2f+1 = 3 *)
  | No_support_check  (** commit without the f+1 leader-support count *)
  | Unbounded_delay
      (** the delayed anchor is never delivered AND the synchronizer fetch
          is disabled - knowledge propagation genuinely fails; with only
          the delivery removed, fetch-on-vote silently repairs the gap *)
  | Leader_censors_v2  (** the leader omits V2's R0 certificate from its parents *)
  | No_vote_once  (** honest voters re-vote slots, and equivocation reaches everyone *)

(* --- helpers over locals --- *)

let update_local v f state =
  { state with locals = Validator_map.add v (f (local_of state v)) state.locals }

let update_all_locals f state =
  List.fold_left (fun acc v -> update_local v (f v) acc) state Validator.all

(* --- propose --- *)

let prev_certs_of mut author r state =
  let censored d =
    match mut with
    | Pristine -> false
    | Drop_batch_gate -> false
    | Weak_quorum -> false
    | No_support_check -> false
    | Unbounded_delay -> false
    | Leader_censors_v2 ->
        Validator.equal author leader
        && Int.equal (round_index r) (round_index R1)
        && Validator.equal d.author Validator.V2
    | No_vote_once -> false
  in
  Option.fold ~none:Digest_set.empty
    ~some:(fun pr ->
      Digest_set.filter
        (fun d ->
          Int.equal (round_index d.round) (round_index pr)
          && Bool.not (censored d))
        (local_of state author).dag)
    (round_pred r)

let byz_digests r = function
  | Byz_unchosen -> []
  | Cooperate -> [ { author = byz; round = r; variant = A } ]
  | Starve_batch -> [ { author = byz; round = r; variant = A } ]
  | Equivocate ->
      [
        { author = byz; round = r; variant = A };
        { author = byz; round = r; variant = B };
      ]
  | Silent -> []
  | Leader_crash -> [ { author = byz; round = r; variant = A } ]

let honest_proposers r strategy =
  match strategy with
  | Byz_unchosen -> honest
  | Cooperate -> honest
  | Starve_batch -> honest
  | Equivocate -> honest
  | Silent -> honest
  | Leader_crash ->
      if Int.equal (round_index r) (round_index R1) then
        List.filter (fun v -> Bool.not (Validator.equal v leader)) honest
      else honest

(* Batch dissemination for a proposed slot: honest batches reach every
   worker before votes are requested; a starved Byzantine batch reaches only
   its author. *)
let disseminate_batch sl state =
  let receivers =
    if Validator.equal sl.s_author byz then
      match state.strategy with
      | Byz_unchosen -> []
      | Cooperate -> Validator.all
      | Starve_batch -> [ byz ]
      | Equivocate -> Validator.all
      | Silent -> []
      | Leader_crash -> Validator.all
    else Validator.all
  in
  List.fold_left
    (fun acc v ->
      update_local v (fun l -> { l with batches = Slot_set.add sl l.batches }) acc)
    state receivers

let propose mut r state =
  let honest_ds =
    List.map
      (fun v -> { author = v; round = r; variant = A })
      (honest_proposers r state.strategy)
  in
  let ds = List.append honest_ds (byz_digests r state.strategy) in
  let with_headers =
    List.fold_left
      (fun acc d ->
        {
          acc with
          headers = Digest_map.add d (prev_certs_of mut d.author r acc) acc.headers;
        })
      state ds
  in
  let slots = List.sort_uniq slot_compare (List.map slot_of ds) in
  {
    (List.fold_left (fun acc sl -> disseminate_batch sl acc) with_headers slots)
    with phase = Vote r;
  }

(* --- vote --- *)

(* Equivocation split: variant B goes to V2 (and its author); the A variant
   of an equivocating slot goes to V0/V1 (and its author). Honest headers
   are broadcast to everyone. Under [No_vote_once] the split is removed as
   well, so both variants reach every validator - visibility is part of the
   dissemination discipline that mutation deletes. *)
let visible_to mut v d strategy =
  if Validator.equal d.author byz then
    match strategy with
    | Byz_unchosen -> false
    | Cooperate -> true
    | Starve_batch -> true
    | Equivocate -> (
        match mut with
        | No_vote_once -> true
        | Pristine | Drop_batch_gate | Weak_quorum | No_support_check
        | Unbounded_delay | Leader_censors_v2 -> (
            match d.variant with
            | A ->
                Validator.equal v Validator.V0 || Validator.equal v Validator.V1
                || Validator.equal v byz
            | B -> Validator.equal v Validator.V2 || Validator.equal v byz))
    | Silent -> false
    | Leader_crash -> true
  else true

let already_voted_slot voter_local sl =
  Digest_set.exists
    (fun d -> Int.equal (slot_compare (slot_of d) sl) 0)
    voter_local.voted

(* Casting a vote also runs the synchronizer: the voter fetches the header's
   parent certificates it is missing (handler.rs:693-738 blocks the vote on
   parent retrieval), which is why a delayed delivery defers knowledge but
   never round progress. [Unbounded_delay] deletes the fetch. *)
let cast mut v d state =
  let fetched =
    match mut with
    | Unbounded_delay -> Digest_set.empty
    | Pristine | Drop_batch_gate | Weak_quorum | No_support_check
    | Leader_censors_v2 | No_vote_once ->
        Option.fold ~none:Digest_set.empty ~some:Fun.id
          (Digest_map.find_opt d state.headers)
  in
  update_local v
    (fun l ->
      {
        l with
        voted = Digest_set.add d l.voted;
        dag = Digest_set.union fetched l.dag;
      })
    { state with votes = Vote_set.add { voter = v; subject = d } state.votes }

let round_headers r state =
  Digest_map.fold
    (fun d _ acc ->
      if Int.equal (round_index d.round) (round_index r) then d :: acc else acc)
    state.headers []

let batch_gate mut v d state =
  match mut with
  | Drop_batch_gate -> true
  | Pristine | Weak_quorum | No_support_check | Unbounded_delay
  | Leader_censors_v2 | No_vote_once ->
      Slot_set.mem (slot_of d) (local_of state v).batches

let vote_once_gate mut v d state =
  match mut with
  | No_vote_once -> Bool.not (Digest_set.mem d (local_of state v).voted)
  | Pristine | Drop_batch_gate | Weak_quorum | No_support_check
  | Unbounded_delay | Leader_censors_v2 ->
      Bool.not (already_voted_slot (local_of state v) (slot_of d))

let honest_votes mut v r state =
  List.filter
    (fun d ->
      visible_to mut v d state.strategy
      && batch_gate mut v d state
      && vote_once_gate mut v d state)
    (List.sort digest_compare (round_headers r state))

let byz_votes mut r state =
  match state.strategy with
  | Byz_unchosen -> []
  | Silent -> []
  | Cooperate | Starve_batch | Equivocate | Leader_crash ->
      List.filter
        (fun d -> visible_to mut byz d state.strategy)
        (List.sort digest_compare (round_headers r state))

let vote mut r state =
  let voted =
    List.fold_left
      (fun acc v ->
        List.fold_left
          (fun acc' d -> cast mut v d acc')
          acc
          (if is_honest v then honest_votes mut v r acc else byz_votes mut r acc))
      state Validator.all
  in
  { voted with phase = Certify r }

(* --- certify --- *)

let votes_for d state =
  Vote_set.cardinal
    (Vote_set.filter (fun vt -> Int.equal (digest_compare vt.subject d) 0) state.votes)

let cert_threshold = function
  | Weak_quorum -> 2
  | Pristine | Drop_batch_gate | No_support_check | Unbounded_delay
  | Leader_censors_v2 | No_vote_once ->
      Validator.quorum

let certify mut r state =
  let formed =
    List.filter
      (fun d -> cert_threshold mut <= votes_for d state)
      (List.sort digest_compare (round_headers r state))
  in
  let with_certs =
    List.fold_left
      (fun acc d ->
        update_local d.author
          (fun l -> { l with dag = Digest_set.add d l.dag })
          { acc with certs = Digest_set.add d acc.certs })
      state formed
  in
  { with_certs with phase = Deliver r }

(* --- deliver --- *)

let delayed_validator = function
  | Delay_unchosen -> None
  | No_delay -> None
  | Delay_v1 -> Some Validator.V1
  | Delay_v2 -> Some Validator.V2

let round_certs r state =
  Digest_set.filter
    (fun d -> Int.equal (round_index d.round) (round_index r))
    state.certs

let deliver_cert d skip state =
  List.fold_left
    (fun acc v ->
      if Option.fold ~none:false ~some:(Validator.equal v) skip then acc
      else update_local v (fun l -> { l with dag = Digest_set.add d l.dag }) acc)
    state Validator.all

let deliver_round r ~delay state =
  let skip_for d =
    if Int.equal (digest_compare d anchor) 0 then delayed_validator delay
    else None
  in
  Digest_set.fold
    (fun d acc -> deliver_cert d (skip_for d) acc)
    (round_certs r state)
    { state with delay }

let deliver mut r state =
  match r with
  | R0 -> [ { (deliver_round R0 ~delay:state.delay state) with phase = Propose R1 } ]
  | R1 ->
      List.map
        (fun delay -> { (deliver_round R1 ~delay state) with phase = Propose R2 })
        [ No_delay; Delay_v1; Delay_v2 ]
  | R2 ->
      let all =
        { (deliver_round R2 ~delay:state.delay state) with phase = Commit_eval }
      in
      let forced_late =
        match mut with
        | Unbounded_delay -> all
        | Pristine | Drop_batch_gate | Weak_quorum | No_support_check
        | Leader_censors_v2 | No_vote_once ->
            Option.fold ~none:all
              ~some:(fun v ->
                if Digest_set.mem anchor all.certs then
                  update_local v
                    (fun l -> { l with dag = Digest_set.add anchor l.dag })
                    all
                else all)
              (delayed_validator all.delay)
      in
      [ forced_late ]

(* --- commit + execute --- *)

let causal_closure d state =
  let parents_of d' =
    Option.fold ~none:Digest_set.empty ~some:Fun.id
      (Digest_map.find_opt d' state.headers)
  in
  let ps = parents_of d in
  Digest_set.add d
    (Digest_set.fold
       (fun p acc -> Digest_set.union (Digest_set.add p (parents_of p)) acc)
       ps Digest_set.empty)

let own_support state l =
  Digest_set.cardinal
    (Digest_set.filter
       (fun d ->
         Int.equal (round_index d.round) (round_index R2)
         && Option.fold ~none:false ~some:(Digest_set.mem anchor)
              (Digest_map.find_opt d state.headers))
       l.dag)

(* Each validator counts, in ITS OWN dag, the R2 certificates whose header
   references the anchor; f+1 of them commit the anchor's causal closure. *)
let commit mut state =
  let closure = causal_closure anchor state in
  let supported l =
    match mut with
    | No_support_check -> true
    | Pristine | Drop_batch_gate | Weak_quorum | Unbounded_delay
    | Leader_censors_v2 | No_vote_once ->
        Validator.support <= own_support state l && Digest_set.mem anchor l.dag
  in
  let commit_one _ l = if supported l then { l with committed = closure } else l in
  [ { (update_all_locals commit_one state) with phase = Execute } ]

let execute state =
  [
    {
      (update_all_locals (fun _ l -> { l with executed = Some l.committed }) state)
      with phase = Done;
    };
  ]

(* --- the transition relation --- *)

let next_with mut state =
  match state.phase with
  | Propose R0 ->
      List.map
        (fun strategy -> propose mut R0 { state with strategy })
        [ Cooperate; Starve_batch; Equivocate; Silent; Leader_crash ]
  | Propose r -> [ propose mut r state ]
  | Vote r -> [ vote mut r state ]
  | Certify r -> [ certify mut r state ]
  | Deliver r -> deliver mut r state
  | Commit_eval -> commit mut state
  | Execute -> execute state
  | Done -> []

let next = next_with Pristine

(* --- atoms --- *)

type atom =
  | Cert_formed of digest  (** a certificate for this digest exists globally *)
  | Quorum_voted of digest  (** >= 2f+1 votes exist globally for this digest *)
  | Conflicting_certs
      (** two formed certificates occupy one slot with different variants *)
  | Honest_double_vote
      (** some honest validator has voted two variants of one slot *)
  | Voted of Validator.t * digest
  | Holds_batch of Validator.t * slot
  | Parents_certified of digest
      (** every parent of this proposed header is a formed certificate *)
  | In_dag of Validator.t * digest
  | Committed of Validator.t * digest
  | Support_quorum
      (** >= f+1 R2 certificates referencing the anchor exist globally *)
  | Own_support_ge of Validator.t
      (** the validator's OWN dag holds >= f+1 anchor-supporting R2 certs *)
  | Quorum_certs of round
      (** certificates for >= 2f+1 distinct slots of this round exist *)
  | Header_proposed of Validator.t * round
  | Honest_holders_ge of slot
      (** >= f+1 honest validators hold this slot's batch *)
  | Byz_equivocating  (** the hidden Byzantine branch is Equivocate *)
  | Equivocation_evidence of Validator.t
      (** v locally holds a conflicting (vote, cert/vote) pair for one slot *)
  | At_done
  | Anchor_author_agreed
      (** the round-robin anchor slot of R1 is V0 - rigid in every reachable
          state because every validator derives it from the same committee
          config; the perturbed-committee mutation is what would break it *)

let same_slot d d' = Int.equal (slot_compare (slot_of d) (slot_of d')) 0

let conflict_in ds =
  Digest_set.exists
    (fun d ->
      Digest_set.exists
        (fun d' -> same_slot d d' && Bool.not (Int.equal (digest_compare d d') 0))
        ds)
    ds

let label a state =
  match a with
  | Cert_formed d -> Digest_set.mem d state.certs
  | Quorum_voted d -> Validator.quorum <= votes_for d state
  | Conflicting_certs -> conflict_in state.certs
  | Honest_double_vote ->
      List.exists (fun v -> conflict_in (local_of state v).voted) honest
  | Voted (v, d) -> Vote_set.mem { voter = v; subject = d } state.votes
  | Holds_batch (v, sl) -> Slot_set.mem sl (local_of state v).batches
  | Parents_certified d ->
      Option.fold ~none:false
        ~some:(fun ps -> Digest_set.subset ps state.certs)
        (Digest_map.find_opt d state.headers)
  | In_dag (v, d) -> Digest_set.mem d (local_of state v).dag
  | Committed (v, d) -> Digest_set.mem d (local_of state v).committed
  | Support_quorum ->
      Validator.support
      <= Digest_set.cardinal
           (Digest_set.filter
              (fun d ->
                Int.equal (round_index d.round) (round_index R2)
                && Option.fold ~none:false ~some:(Digest_set.mem anchor)
                     (Digest_map.find_opt d state.headers))
              state.certs)
  | Own_support_ge v -> Validator.support <= own_support state (local_of state v)
  | Quorum_certs r ->
      Validator.quorum
      <= Slot_set.cardinal
           (Digest_set.fold
              (fun d acc -> Slot_set.add (slot_of d) acc)
              (round_certs r state) Slot_set.empty)
  | Header_proposed (v, r) ->
      Option.is_some
        (Digest_map.find_opt { author = v; round = r; variant = A } state.headers)
  | Honest_holders_ge sl ->
      Validator.support
      <= List.length
           (List.filter
              (fun v -> Slot_set.mem sl (local_of state v).batches)
              honest)
  | Byz_equivocating -> (
      match state.strategy with
      | Equivocate -> true
      | Byz_unchosen | Cooperate | Starve_batch | Silent | Leader_crash -> false)
  | Equivocation_evidence v ->
      conflict_in
        (Digest_set.union (local_of state v).voted (local_of state v).dag)
  | At_done -> (
      match state.phase with
      | Done -> true
      | Propose _ | Vote _ | Certify _ | Deliver _ | Commit_eval | Execute ->
          false)
  | Anchor_author_agreed -> Validator.equal anchor.author leader

let atom_to_string = function
  | Cert_formed d -> "cert(" ^ digest_to_string d ^ ")"
  | Quorum_voted d -> "quorum-voted(" ^ digest_to_string d ^ ")"
  | Conflicting_certs -> "conflicting-certs"
  | Honest_double_vote -> "honest-double-vote"
  | Voted (v, d) -> "voted(" ^ Validator.to_string v ^ "," ^ digest_to_string d ^ ")"
  | Holds_batch (v, sl) ->
      "batch(" ^ Validator.to_string v ^ "," ^ Validator.to_string sl.s_author
      ^ "/" ^ round_to_string sl.s_round ^ ")"
  | Parents_certified d -> "parents-certified(" ^ digest_to_string d ^ ")"
  | In_dag (v, d) -> "dag(" ^ Validator.to_string v ^ "," ^ digest_to_string d ^ ")"
  | Committed (v, d) ->
      "committed(" ^ Validator.to_string v ^ "," ^ digest_to_string d ^ ")"
  | Support_quorum -> "support-quorum"
  | Own_support_ge v -> "own-support(" ^ Validator.to_string v ^ ")"
  | Quorum_certs r -> "quorum-certs(" ^ round_to_string r ^ ")"
  | Header_proposed (v, r) ->
      "proposed(" ^ Validator.to_string v ^ "," ^ round_to_string r ^ ")"
  | Honest_holders_ge sl ->
      "honest-holders(" ^ Validator.to_string sl.s_author ^ "/"
      ^ round_to_string sl.s_round ^ ")"
  | Byz_equivocating -> "byz-equivocating"
  | Equivocation_evidence v -> "equiv-evidence(" ^ Validator.to_string v ^ ")"
  | At_done -> "done"
  | Anchor_author_agreed -> "anchor-author-agreed"

(* --- checker instance --- *)

module Checker = System.Make (Tn_state) (Tn_state.Local)

let spec_of mut =
  {
    Checker.init = [ initial ];
    next = next_with mut;
    view = (fun v s -> local_of s v);
    label;
  }

let spec = spec_of Pristine

let make () = Checker.make spec
