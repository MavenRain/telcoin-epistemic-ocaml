(** Finite interpreted system for the EXEC-TALLY family: a non-executing
    state-sync observer tallies gossiped consensus-output signatures and
    advances its watch only at f+1 = 2 distinct verified signers.

    Mechanisms modeled, keyed to Telcoin-Association/telcoin-network:
    - after saving the fully assembled consensus output to its consensus
      chain, an honest CVV signs and gossips a [ConsensusResult] for it,
      and only AFTERWARD hands the output to the engine for asynchronous
      execution, with nothing awaiting completion
      (crates/consensus/executor/src/subscriber.rs:280-325,
      [handle_consensus_output]: save :286, sign :298-302, publish
      :303-316, execution handoff :317); the signature covers only
      (epoch, round, number, consensus-header hash)
      (crates/types/src/primary/block.rs:116-160) - a commitment to the
      consensus chain, NOT execution: the twin sync path states the save
      "does NOT imply execution" (subscriber.rs:151-153). The model folds
      save-and-sign into the single [Save_sign] phase, so
      [signed_j := saved_j] for honest j with no extra field;
    - the primary network handler verifies committee signatures over the
      published result hash and collects DISTINCT signers
      (crates/consensus/primary/src/network/handler.rs:288-341, with
      [enough_sigs] derived at handler.rs:341);
    - the observer's [last_published_consensus_num_hash] watch advances only
      when [sigs >= enough_sigs] (handler.rs:404-425, the threshold gate at
      handler.rs:410) - the [advanced] field, written exclusively by
      [tally_deliver]'s single threshold gate;
    - the state-sync (non-executing) node is the consumer of that watch
      (crates/state-sync/src/consensus.rs:233-256);
    - the alternative epoch-record advance path (crates/state-sync/src/
      epoch.rs:61-73 and 98-169, crates/types/src/primary/epoch.rs:58-96)
      needs a certified epoch boundary and is unreachable in this
      single-epoch, single-output model, so gate (a) above is the only
      advance route - which is what makes the threshold mutation a real
      refuter with no sibling repair path.

    Role mapping (knowledge agents must be validators): V0 IS the dedicated
    non-executing observer O - the state-sync node; its local state, and the
    ONLY content of its view, is the signer tally (no phase component: the
    node does not observe the committee's internal phase). V1 and V2 are the
    honest CVVs and V3 the Byzantine CVV; none of the three is a
    knowledge agent in this family, so all three get the constant [Blind]
    view and never appear under K / Everyone / Common.

    Hidden branching: the Byzantine fabricate-result sub-choice starts
    [Fab_unchosen] and resolves into both branches at the first transition;
    in the [Fabricate_result] branch V3's validly self-signed BOGUS result
    reaches the observer before any honest CVV saves. The observer's view
    then collides across phases: tally = {V3} pre-[Save_sign] (no honest
    save) is indistinguishable from tally = {V3} post-[Save_sign] while
    the honest results are still in flight - a lone signature never
    grounds knowledge.
    Unforgeability by construction: a validator enters the tally only via a
    delivery of a result it signed itself. *)

(** Phase machine: the committed consensus output N is published (the
    fabricated result, if any, arrives here - before any honest save),
    honest CVVs save-and-sign (subscriber.rs:286, :298-302), signed
    results gossip with a delivery-delay choice {none, delay-observer},
    the delayed branch is force-delivered on the next tick (bounded-delay
    fairness), and [Done] is terminal (the kernel stutter-closes it). *)
type phase =
  | Output_committed
  | Save_sign
  | Result_gossip
  | Result_delayed
  | Done

(** Total order on phases via a fixed index. *)
let phase_index = function
  | Output_committed -> 0
  | Save_sign -> 1
  | Result_gossip -> 2
  | Result_delayed -> 3
  | Done -> 4

(** Phase comparison for the ordered state. *)
let phase_compare a b = Int.compare (phase_index a) (phase_index b)

(** The hidden Byzantine sub-choice, resolved at the first transition:
    [Fabricate_result] delivers V3's validly self-signed bogus
    ConsensusResult to the observer pre-[Save_sign] (signature verification at
    handler.rs:288-341 accepts it - the signature is genuine, the content
    is not); [No_fabricate] sends nothing. [Fab_unchosen] only labels the
    initial state. *)
type fabricate = Fab_unchosen | No_fabricate | Fabricate_result

(** Total order on the fabricate sub-choice via a fixed index. *)
let fabricate_index = function
  | Fab_unchosen -> 0
  | No_fabricate -> 1
  | Fabricate_result -> 2

(** Fabricate-choice comparison for the ordered state. *)
let fabricate_compare a b =
  Int.compare (fabricate_index a) (fabricate_index b)

(** Validator sets: the observer's tally is a set of distinct signers,
    mirroring the distinct-signer collection of handler.rs:288-341. *)
module Vset = Set.Make (Validator)

(** The global state. [tally] is the observer V0's local signer tally for
    the single modeled output N; [saved_v1]/[saved_v2] are the honest
    CVVs' saved-to-consensus-chain flags ([save_consensus] at
    subscriber.rs:286 in [handle_consensus_output], preceding the sign at
    :298-302 and the asynchronous execution handoff at :317); [advanced]
    is the observer's watch (state-sync/consensus.rs:233-256), set
    exclusively by the [tally_deliver] threshold gate. *)
type state = {
  phase : phase;
  fab : fabricate;
  tally : Vset.t;
  saved_v1 : bool;
  saved_v2 : bool;
  advanced : bool;
}

(** Total deterministic comparison over ALL state fields. *)
let state_compare s1 s2 =
  let c = phase_compare s1.phase s2.phase in
  if Bool.not (Int.equal c 0) then c
  else
    let c1 = fabricate_compare s1.fab s2.fab in
    if Bool.not (Int.equal c1 0) then c1
    else
      let c2 = Vset.compare s1.tally s2.tally in
      if Bool.not (Int.equal c2 0) then c2
      else
        let c3 = Bool.compare s1.saved_v1 s2.saved_v1 in
        if Bool.not (Int.equal c3 0) then c3
        else
          let c4 = Bool.compare s1.saved_v2 s2.saved_v2 in
          if Bool.not (Int.equal c4 0) then c4
          else Bool.compare s1.advanced s2.advanced

(** Ordered state module for the kernel functor. *)
module State = struct
  type t = state

  let compare = state_compare
end

(** A validator's view: the observer V0 sees exactly its tally (its entire
    local state - no phase, no other node's flags); every other validator
    is a non-agent in this family and gets the constant [Blind] view, so K
    at V1/V2/V3 would be degenerate and is never used. *)
type view = Observer_tally of Vset.t | Blind

(** Total order on views: [Blind] below every tally view. *)
let view_compare a b =
  match (a, b) with
  | Blind, Blind -> 0
  | Blind, Observer_tally _ -> -1
  | Observer_tally _, Blind -> 1
  | Observer_tally t1, Observer_tally t2 -> Vset.compare t1 t2

(** Ordered view module for the kernel functor. *)
module View = struct
  type t = view

  let compare = view_compare
end

(** View projection: V0 is the observer, V1/V2/V3 are blind non-agents. *)
let view v s =
  match v with
  | Validator.V0 -> Observer_tally s.tally
  | Validator.V1 | Validator.V2 | Validator.V3 | Validator.V4 | Validator.V5
  | Validator.V6 | Validator.V7 | Validator.V8 | Validator.V9 ->
      Blind

(** Gate deletion for the confirm-by-mutation test. *)
type mutation =
  | Pristine
  | Weak_sig_threshold
      (** the observer's watch advances on any lone verified signature
          instead of f+1 = 2 distinct signers - deletes the
          [sigs >= enough_sigs] check (handler.rs:410, [enough_sigs] from
          handler.rs:341), so V3's single fabricated signature advances the
          watch before any honest CVV saved the output *)

(* 4-member committee thresholds (f = 1): 2f+1 = 3, f+1 = 2. The global
   Validator.quorum/support now describe the ten-member tn committee. *)
let support = 2

(** The advance threshold: f+1 = 2 distinct signers pristine
    ([enough_sigs], handler.rs:341); 1 under the mutation. *)
let advance_threshold = function
  | Pristine -> support
  | Weak_sig_threshold -> 1

(** Deliver signed results to the observer and run the SINGLE advance gate
    (handler.rs:404-425): the watch advances iff the distinct-signer tally
    reaches the threshold, and stays advanced (the watch is monotone).
    Every tally write in the model goes through this function, so the
    mutation cannot be repaired by a sibling path. *)
let tally_deliver mut signers s =
  let tally = Vset.union signers s.tally in
  {
    s with
    tally;
    advanced = s.advanced || advance_threshold mut <= Vset.cardinal tally;
  }

(** The two honest CVVs' signed results, gossiped together at
    [Result_gossip] (the sole [publish_consensus] call site,
    subscriber.rs:303-316); by construction they exist only after
    [Save_sign] set the saved flags - signed = saved. *)
let honest_results = Vset.of_list [ Validator.V1; Validator.V2 ]

(** Resolve the hidden fabricate sub-choice and run the pre-[Save_sign]
    delivery window: in the [Fabricate_result] branch V3's validly signed
    bogus result enters the observer's tally before any honest save; the
    [Fab_unchosen] arm is never produced by [next_with] and delivers
    nothing. *)
let output_step mut fab s =
  let branched = { s with fab } in
  let delivered =
    match fab with
    | Fab_unchosen -> branched
    | No_fabricate -> branched
    | Fabricate_result ->
        tally_deliver mut (Vset.singleton Validator.V3) branched
  in
  { delivered with phase = Save_sign }

(** Honest CVVs save the consensus output to their consensus chains and
    sign it (subscriber.rs:286, then :298-302) - strictly BEFORE the
    output is handed off for asynchronous execution (:317, which nothing
    awaits); their self-signed results now exist (signed = saved) but
    have not yet reached the observer. *)
let save_sign_step s =
  { s with saved_v1 = true; saved_v2 = true; phase = Result_gossip }

(** Result gossip with the delivery-delay choice: either both honest signed
    results reach the observer now, or delivery to the observer is deferred
    one tick ([Result_delayed]) - the window in which the observer's
    tally = {V3} view collides with the pre-[Save_sign] fabricated
    state. *)
let result_gossip mut s =
  [
    { (tally_deliver mut honest_results s) with phase = Done };
    { s with phase = Result_delayed };
  ]

(** Forced delivery of the delayed honest results (bounded-delay fairness:
    the delay defers knowledge, never liveness). *)
let result_release mut s =
  [ { (tally_deliver mut honest_results s) with phase = Done } ]

(** The transition relation, parameterized by the gate mutation. [Done] is
    terminal; the kernel stutter-closes it. *)
let next_with mut s =
  match s.phase with
  | Output_committed ->
      List.map
        (fun fab -> output_step mut fab s)
        [ No_fabricate; Fabricate_result ]
  | Save_sign -> [ save_sign_step s ]
  | Result_gossip -> result_gossip mut s
  | Result_delayed -> result_release mut s
  | Done -> []

(** The pristine transition relation. *)
let next = next_with Pristine

(** The initial state: output committed, sub-choice hidden, empty tally,
    nothing saved, watch not advanced. *)
let initial =
  {
    phase = Output_committed;
    fab = Fab_unchosen;
    tally = Vset.empty;
    saved_v1 = false;
    saved_v2 = false;
    advanced = false;
  }

(** The atom vocabulary the EXEC-TALLY statement quantifies over. *)
type atom =
  | Advance_o
      (** the observer's watch advanced to the modeled output
          (handler.rs:404-425 via state-sync/consensus.rs:233-256) *)
  | Honest_saved
      (** some honest CVV saved the output to its consensus chain
          (subscriber.rs:286) - a commitment that deliberately does NOT
          imply execution (subscriber.rs:151-153) - the K operand *)
  | All_honest_saved
      (** both honest CVVs saved the output to their consensus chains *)
  | In_tally of Validator.t
      (** this validator's signed result is in the observer's tally *)

(** Atom valuation over the global state. *)
let label a s =
  match a with
  | Advance_o -> s.advanced
  | Honest_saved -> s.saved_v1 || s.saved_v2
  | All_honest_saved -> s.saved_v1 && s.saved_v2
  | In_tally v -> Vset.mem v s.tally

(** Render an atom in the surface notation of the statement docs. *)
let atom_to_string = function
  | Advance_o -> "advance(o)"
  | Honest_saved -> "honest-saved"
  | All_honest_saved -> "all-honest-saved"
  | In_tally v -> "in-tally(" ^ Validator.to_string v ^ ")"

(** The exact CTLK checker over this family's ordered state and view: the
    presheaf-topos internal-logic denotation ({!Denote}, lib/internal/DESIGN.md),
    with {!System} retained as the differential reduction oracle of this
    family's topos gate (test/t_*_topos.ml). *)
module Checker = Denote.Make (State) (View)

(** The checker spec under a mutation: single initial state, mutation-
    parameterized transitions, observer-only view, atom valuation. *)
let spec_of mut =
  { Checker.init = [ initial ]; next = next_with mut; view; label }

(** The pristine spec. *)
let spec = spec_of Pristine

(** Build the pristine interpreted system. *)
let make () = Checker.make spec
