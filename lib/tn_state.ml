(** The abstracted telcoin-network global state: 4 validators (V3 Byzantine),
    f = 1, three Narwhal rounds driven by a phase machine (propose -> vote ->
    certify -> deliver per round, then commit evaluation, execution, terminal
    stutter). The Bullshark anchor is V0's R1 header; R2 certificates
    referencing it are its support.

    The abstraction keeps exactly the structure the statements quantify over:
    headers with an equivocation variant bit, batch possession (the
    batch-validator availability gate), votes with vote-once-per-slot
    discipline, 2f+1 certificates, per-validator DAG views (the knowledge
    ground for K_i), the f+1 leader-support commit rule, and a deterministic
    execution digest. Signatures are unforgeability by construction: a
    certificate value exists only if the model assembled quorum votes for
    it. *)

(* The Byzantine proposer may issue two conflicting headers for one slot;
   honest proposers only ever issue [A]. *)
type variant = A | B

let variant_index = function A -> 0 | B -> 1
let variant_compare a b = Int.compare (variant_index a) (variant_index b)
let variant_to_string = function A -> "A" | B -> "B"

type round = R0 | R1 | R2

let round_index = function R0 -> 0 | R1 -> 1 | R2 -> 2
let round_compare a b = Int.compare (round_index a) (round_index b)
let round_to_string r = "r" ^ Int.to_string (round_index r)

let round_pred = function R0 -> None | R1 -> Some R0 | R2 -> Some R1

(* A slot is one proposer's opportunity in one round; the vote-once
   discipline and batch payloads are keyed by slot, so an equivocating pair
   of headers shares its batch and an honest validator votes for at most one
   of the pair. *)
type slot = { s_author : Validator.t; s_round : round }

let slot_compare s1 s2 =
  let c = Validator.compare s1.s_author s2.s_author in
  if Int.equal c 0 then round_compare s1.s_round s2.s_round else c

module Slot_set = Set.Make (struct
  type t = slot

  let compare = slot_compare
end)

(* A digest identifies one concrete header (and its certificate, if formed):
   slot plus equivocation variant. *)
type digest = { author : Validator.t; round : round; variant : variant }

let slot_of d = { s_author = d.author; s_round = d.round }

let digest_compare d1 d2 =
  let c = Validator.compare d1.author d2.author in
  if Bool.not (Int.equal c 0) then c
  else
    let c' = round_compare d1.round d2.round in
    if Int.equal c' 0 then variant_compare d1.variant d2.variant else c'

let digest_to_string d =
  Validator.to_string d.author ^ "/" ^ round_to_string d.round ^ "/"
  ^ variant_to_string d.variant

module Digest = struct
  type t = digest

  let compare = digest_compare
end

module Digest_set = Set.Make (Digest)
module Digest_map = Map.Make (Digest)

type vote = { voter : Validator.t; subject : digest }

let vote_compare v1 v2 =
  let c = Validator.compare v1.voter v2.voter in
  if Int.equal c 0 then digest_compare v1.subject v2.subject else c

module Vote_set = Set.Make (struct
  type t = vote

  let compare = vote_compare
end)

module Validator_map = Map.Make (Validator)

(* The Byzantine strategy, one branch fixed at Propose R0 and applied
   uniformly each round: [Cooperate] follows the protocol; [Starve_batch]
   proposes but withholds the batch payload from honest workers (the
   availability attack); [Equivocate] issues variant A to V0/V1 and variant
   B to V2, voting for both; [Silent] proposes and votes nothing (the
   fail-stop / withholding attack liveness must survive); [Leader_crash] is
   the cooperative-Byzantine branch in which the HONEST leader V0 fails to
   propose its R1 anchor (the proposer-crash run the encodability analysis
   requires as the cert-free indistinguishability witness - the run where no
   anchor certificate ever forms, so knowing one formed is contingent).
   Crash composes only with a cooperative V3: crash plus a withholding V3
   is two faults, beyond f = 1. *)
type byz_strategy =
  | Byz_unchosen
  | Cooperate
  | Starve_batch
  | Equivocate
  | Silent
  | Leader_crash

let byz_strategy_index = function
  | Byz_unchosen -> 0
  | Cooperate -> 1
  | Starve_batch -> 2
  | Equivocate -> 3
  | Silent -> 4
  | Leader_crash -> 5

let byz_strategy_compare a b =
  Int.compare (byz_strategy_index a) (byz_strategy_index b)

let byz_strategy_to_string = function
  | Byz_unchosen -> "unchosen"
  | Cooperate -> "cooperate"
  | Starve_batch -> "starve-batch"
  | Equivocate -> "equivocate"
  | Silent -> "silent"
  | Leader_crash -> "leader-crash"

(* Whose delivery of the anchor certificate is deferred by one round
   (bounded-delay fairness: deferred at Deliver R1, forced at Deliver R2).
   The leader itself is never delayed: it aggregates the anchor. *)
type delay_choice = Delay_unchosen | No_delay | Delay_v1 | Delay_v2

let delay_index = function
  | Delay_unchosen -> 0
  | No_delay -> 1
  | Delay_v1 -> 2
  | Delay_v2 -> 3

let delay_compare a b = Int.compare (delay_index a) (delay_index b)

let delay_to_string = function
  | Delay_unchosen -> "unchosen"
  | No_delay -> "none"
  | Delay_v1 -> "v1"
  | Delay_v2 -> "v2"

type phase =
  | Propose of round
  | Vote of round
  | Certify of round
  | Deliver of round
  | Commit_eval
  | Execute
  | Done

let phase_index = function
  | Propose r -> 10 + round_index r
  | Vote r -> 20 + round_index r
  | Certify r -> 30 + round_index r
  | Deliver r -> 40 + round_index r
  | Commit_eval -> 50
  | Execute -> 51
  | Done -> 52

let phase_compare a b = Int.compare (phase_index a) (phase_index b)

let phase_to_string = function
  | Propose r -> "propose:" ^ round_to_string r
  | Vote r -> "vote:" ^ round_to_string r
  | Certify r -> "certify:" ^ round_to_string r
  | Deliver r -> "deliver:" ^ round_to_string r
  | Commit_eval -> "commit-eval"
  | Execute -> "execute"
  | Done -> "done"

(* Per-validator local state: exactly what a telcoin-network node holds and
   nothing more - the knowledge ground for K_i. [dag]: certificates received
   (certificate store / DAG view); [batches]: batch payloads its worker
   holds; [voted]: digests it has voted for (vote-once per slot derives from
   this); [committed]: the committed sub-DAG once its consensus commits;
   [executed]: the executed-chain digest, [None] until execution. Global
   fields (in-flight votes, other validators' views, the Byzantine branch
   taken) are invisible to it. *)
type local = {
  dag : Digest_set.t;
  batches : Slot_set.t;
  voted : Digest_set.t;
  committed : Digest_set.t;
  executed : Digest_set.t option;
}

let local_empty =
  {
    dag = Digest_set.empty;
    batches = Slot_set.empty;
    voted = Digest_set.empty;
    committed = Digest_set.empty;
    executed = None;
  }

let local_compare l1 l2 =
  let c = Digest_set.compare l1.dag l2.dag in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = Slot_set.compare l1.batches l2.batches in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Digest_set.compare l1.voted l2.voted in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Digest_set.compare l1.committed l2.committed in
        if Bool.not (Int.equal c3 0) then c3
        else Option.compare Digest_set.compare l1.executed l2.executed

module Local = struct
  type t = local

  let compare = local_compare
end

(* The global state. [headers] maps each proposed digest to its parent
   digests (the header body); [certs] the digests whose vote count reached
   the quorum. *)
type t = {
  phase : phase;
  strategy : byz_strategy;
  delay : delay_choice;
  headers : Digest_set.t Digest_map.t;
  votes : Vote_set.t;
  certs : Digest_set.t;
  locals : local Validator_map.t;
}

let local_of state v =
  Option.fold ~none:local_empty ~some:Fun.id
    (Validator_map.find_opt v state.locals)

let initial =
  {
    phase = Propose R0;
    strategy = Byz_unchosen;
    delay = Delay_unchosen;
    headers = Digest_map.empty;
    votes = Vote_set.empty;
    certs = Digest_set.empty;
    locals =
      List.fold_left
        (fun acc v -> Validator_map.add v local_empty acc)
        Validator_map.empty Validator.all;
  }

let compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = byz_strategy_compare s1.strategy s2.strategy in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = delay_compare s1.delay s2.delay in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 =
          Digest_map.compare Digest_set.compare s1.headers s2.headers
        in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Vote_set.compare s1.votes s2.votes in
          if Bool.not (Int.equal c4 0) then c4
          else
            let c5 = Digest_set.compare s1.certs s2.certs in
            if Bool.not (Int.equal c5 0) then c5
            else Validator_map.compare local_compare s1.locals s2.locals
