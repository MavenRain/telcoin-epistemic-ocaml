(** The RPC_CODEC_SIZE family (S1, S2, S3) proves on the pristine
    {!Rpc_codec_size_model} through [prove_nonvacuous] (so each antecedent is
    also checked reachable), the reachable graph stays in its justified band,
    the three codec invariants the modelled gates enforce are genuinely
    unreachable-when-forbidden, and the epistemic layer is partial information
    rather than collapsed.

    The contingency group is where R2 and R3 are discharged. The family has
    exactly ONE positive knowledge conjunct - [K_V0(deviated(B))] in S1 conjunct
    D, the gossip contrast - so it carries both required R2 tests (operand
    contingency and a non-singleton view class) and one R3 witness pair per [~K]
    conjunct (S1 conjunct B, S2 conjunct B).

    The group also carries four HONESTY tests the contract does not demand but
    the family's own claims do. [exempt_refusal_is_free] and
    [scored_refusal_is_charged] prove that BOTH sides of the trust-basis
    exemption (peer.rs:213-233, all_peers.rs:847-873) are reachable, so S1's
    conjuncts A and C are each about a live branch rather than an empty one -
    this is the repair path an earlier draft of this family omitted, which would
    have made "the refusal costs B five points" true only by omission.
    [output_bound_repair_is_present] proves the post-decode equality check
    (codec.rs:96-101) fires in the PRISTINE model on a fully accumulated body,
    so S3's mutation has to survive the sibling path rather than benefit from
    its absence. And [honest_config_skew_is_reachable] proves the branch a
    skeptic would call a modelling artefact - an honest peer configured above
    V0 - is actually in the graph, which is what makes S1's ignorance conjunct
    load-bearing. *)

open Telcoin_epistemic
open Rpc_codec_size_model

(** Build the pristine system or fail the test on an impossible [Empty_init]. *)
let with_sys k =
  Result.fold ~ok:k
    ~error:(fun Checker.Empty_init -> Alcotest.fail "make: empty init")
    (make ())

(** Render a proof error for the assertion message. *)
let error_to_string = function
  | Checker.Refuted { failing_inits } ->
      "refuted at " ^ Int.to_string failing_inits ^ " initial state(s)"
  | Checker.Vacuous_antecedent -> "vacuous antecedent"

(** One proof case: the statement proves on the pristine model. *)
let prove_one st () =
  with_sys (fun sys ->
      Alcotest.(check string)
        (st.Rpc_codec_size_statements.name ^ " ["
        ^ Statements.bucket_to_string st.Rpc_codec_size_statements.bucket
        ^ "] proves")
        "proved"
        (Result.fold
           ~ok:(fun _ -> "proved")
           ~error:error_to_string
           (Rpc_codec_size_statements.prove sys st)))

(** Atom injection shorthand. *)
let f a = Formula.Atom a

(** The reading node: the only agent this family puts under [K]. *)
let reader = Validator.V0

(** [satisfiable] must be [expected] for [phi]. *)
let sat_is label expected phi () =
  with_sys (fun sys ->
      Alcotest.(check bool) label expected (Checker.satisfiable sys phi))

(* Loose product bound: 8 plans x 2 configs x 2 trust bases x 6 observations x 3
   buffer classes x 2 settlement values x 3 charge values = 3456. The pristine
   reachable set is exactly 53: 1 initial state, plus 26 codec-resolved states
   and 26 classified states, where 26 = 13 admissible (plan, config) pairs (7
   plans x 2 configs less the inadmissible honest-large-cap/default pair) x 2
   trust bases. All four mutants also have 53 reachable states: no gate deletion
   in this family adds or removes a branch, each only relabels one
   transition. *)
let reachable_bounded () =
  with_sys (fun sys ->
      let n = Checker.reachable_count sys in
      Alcotest.(check bool)
        ("reachable count in a sane band: " ^ Int.to_string n)
        true
        (1 <= n && n <= 3456))

(* The uncompressed-prefix gate is positioned BEFORE the streaming read loop:
   codec.rs:51-54 returns early and the loop starts at :73. So no reachable
   state has the prefix rejection together with any accumulated body byte - the
   oversize declaration costs V0 nothing but the two 4-byte prefixes. *)
let prefix_gate_precedes_the_read_loop =
  sat_is "not EF (rpc_prefix_size_reject /\\ body_read_ran)" false
    (Formula.And (f Rpc_prefix_size_reject, f Body_read_ran))

(* The compressed-length gate (codec.rs:61-67) is the invariant S3 states: the
   accumulation at :73-86 never exceeds max_compress_len(uncompressed_len). This
   is exactly the state No_compressed_length_gate makes reachable. *)
let compressed_gate_bounds_the_accumulation =
  sat_is "not EF buffer_amplified" false (f Buffer_amplified)

(* The UnexpectedEof exemption (consensus.rs:1281-1286) is exact and comes
   BEFORE the trust basis is consulted: no reachable state has a truncated body
   and any penalty against B, for either trust basis. This is the state
   No_inbound_eof_exemption makes reachable. *)
let eof_exemption_is_exact =
  sat_is "not EF (body_truncated /\\ charged_any)" false
    (Formula.And (f Body_truncated, f Charged_any))

(* The gossip reject path charges every relayer the score model applies to:
   RejectReason::TooLarge maps to RejectPenalty::FatalRelayer
   (consensus.rs:1063-1073), so no reachable state has a classified gossip size
   rejection from a scored peer with nothing charged. The exempt relayer is a
   different matter and is deliberately NOT covered here - Peer::apply_penalty
   suppresses even Fatal for an exempt peer (peer.rs:218-230). *)
let gossip_reject_charges_scored_relayers =
  sat_is
    "not EF (gossip_size_reject /\\ ~penalty_exempt /\\ exchange_settled /\\ \
     ~charged_any)" false
    (Formula.And
       ( f Gossip_size_reject,
         Formula.And
           ( Formula.Not (f Penalty_exempt),
             Formula.And (f Exchange_settled, Formula.Not (f Charged_any)) ) ))

(* R2, part one - the positive K of S1 conjunct D is CONTINGENT, not collapsed:
   there is a reachable state at which V0 does not know that B deviated. (It is
   every RPC prefix rejection, which is S1 conjunct B.) *)
let positive_k_is_contingent =
  sat_is "EF ~K_V0(deviated(B))" true
    (Formula.Not (Formula.K (reader, f Deviated)))

(* R2, part two - the view class carrying that positive K is NOT a singleton. At
   a gossip rejection, pick the atom peer_cap_above_ours(B), which is false at
   the default-configured branch: V0 does not know it is false, which is only
   possible if another reachable state shares V0's whole view - (obs,
   settlement, charge, trust) - and satisfies it. That state is the same gossip
   rejection from a peer whose max_rpc_message_size is the 2 MiB operator
   setting (config/network.rs:509), which V0 never observes. So the class has at
   least two members and K_V0(deviated(B)) there is a real knowledge claim. *)
let positive_k_class_is_not_a_singleton =
  sat_is "EF (gossip_size_reject /\\ ~K_V0(~peer_cap_above_ours(B)))" true
    (Formula.And
       ( f Gossip_size_reject,
         Formula.Not (Formula.K (reader, Formula.Not (f Peer_cap_above_ours)))
       ))

(* R3 for S1 conjunct B, the deviating half of the witness pair: B is a spammer
   declaring an oversized body (Plan_spam_oversize) and V0 still does not know
   it. codec.rs:51-54 raises the identical error for both intents. *)
let s1_ignorance_witness_deviating =
  sat_is "EF (rpc_prefix_size_reject /\\ deviated(B) /\\ ~K_V0(deviated(B)))"
    true
    (Formula.And
       ( f Rpc_prefix_size_reject,
         Formula.And (f Deviated, Formula.Not (Formula.K (reader, f Deviated)))
       ))

(* R3 for S1 conjunct B, the honest half: the same rejection from a peer that
   did NOT deviate - it runs the 2 MiB cap of config/network.rs:509 and sent a
   message its own encode_message accepted (codec.rs:133-136). *)
let s1_ignorance_witness_honest =
  sat_is "EF (rpc_prefix_size_reject /\\ ~deviated(B))" true
    (Formula.And (f Rpc_prefix_size_reject, Formula.Not (f Deviated)))

(* R3 for S2 conjunct B, the deliberate half: B withholds the declared body on
   purpose and V0 does not know it. *)
let s2_ignorance_witness_deliberate =
  sat_is
    "EF (body_truncated /\\ deliberate_truncation(B) /\\ \
     ~K_V0(deliberate_truncation(B)))" true
    (Formula.And
       ( f Body_truncated,
         Formula.And
           ( f Deliberate_truncation,
             Formula.Not (Formula.K (reader, f Deliberate_truncation)) ) ))

(* R3 for S2 conjunct B, the flap half: the same UnexpectedEof from an honest
   peer whose stream was reset (codec.rs:78-83 makes no distinction). *)
let s2_ignorance_witness_flap =
  sat_is "EF (body_truncated /\\ ~deliberate_truncation(B))" true
    (Formula.And (f Body_truncated, Formula.Not (f Deliberate_truncation)))

(* HONESTY, the exempt side of the trust basis: a peer whose confirmed BLS key
   is in the previous, current or next committee, or an operator-allowlisted
   peer (all_peers.rs:847-873), can trip the very same size refusal and pay
   nothing, because Peer::apply_penalty bypasses the score model entirely
   (peer.rs:218-233). If this state were unreachable S1's conjunct C would be
   vacuous - and, worse, S1's conjunct A would be an over-claim, since the real
   code does not charge every refused sender. *)
let exempt_refusal_is_free =
  sat_is
    "EF (rpc_prefix_size_reject /\\ penalty_exempt /\\ exchange_settled /\\ \
     ~charged_any)" true
    (Formula.And
       ( f Rpc_prefix_size_reject,
         Formula.And
           ( f Penalty_exempt,
             Formula.And (f Exchange_settled, Formula.Not (f Charged_any)) ) ))

(* HONESTY, the scored side: the same refusal from a peer outside the trust
   basis does reach the score (-5.0, peers/score.rs:91), so the exemption above
   is a real distinction and not the whole story. *)
let scored_refusal_is_charged =
  sat_is "EF (rpc_prefix_size_reject /\\ ~penalty_exempt /\\ charged_medium)"
    true
    (Formula.And
       ( f Rpc_prefix_size_reject,
         Formula.And (Formula.Not (f Penalty_exempt), f Charged_medium) ))

(* HONESTY - the post-decode output bound of codec.rs:96-101 ("decompressed size
   does not match reported uncompressed size") fires in the PRISTINE model on a
   body that was fully accumulated first, and charges Medium. That is the
   sibling path S3's mutation must survive rather than benefit from: it rejects
   the message, it does not bound the accumulation. *)
let output_bound_repair_is_present =
  sat_is "EF (body_read_ran /\\ charged_medium)" true
    (Formula.And (f Body_read_ran, f Charged_medium))

(* HONESTY - the branch a skeptic calls a modelling artefact is reachable: an
   HONEST peer, configured above V0 (config/network.rs:509, asserted at :525),
   whose message V0's codec refuses on the prefix. If this were unreachable S1's
   ignorance conjunct would be empty. *)
let honest_config_skew_is_reachable =
  sat_is
    "EF (rpc_prefix_size_reject /\\ ~deviated(B) /\\ peer_cap_above_ours(B))"
    true
    (Formula.And
       ( f Rpc_prefix_size_reject,
         Formula.And (Formula.Not (f Deviated), f Peer_cap_above_ours) ))

let () =
  Alcotest.run "rpc_codec_size"
    [
      ( "proofs",
        List.map
          (fun st ->
            Alcotest.test_case st.Rpc_codec_size_statements.name `Quick
              (prove_one st))
          Rpc_codec_size_statements.all );
      ( "sanity",
        [
          Alcotest.test_case "reachable-bounded" `Quick reachable_bounded;
          Alcotest.test_case "prefix-gate-precedes-the-read-loop" `Quick
            prefix_gate_precedes_the_read_loop;
          Alcotest.test_case "compressed-gate-bounds-the-accumulation" `Quick
            compressed_gate_bounds_the_accumulation;
          Alcotest.test_case "eof-exemption-is-exact" `Quick
            eof_exemption_is_exact;
          Alcotest.test_case "gossip-reject-charges-scored-relayers" `Quick
            gossip_reject_charges_scored_relayers;
        ] );
      ( "contingency",
        [
          Alcotest.test_case "positive-k-is-contingent" `Quick
            positive_k_is_contingent;
          Alcotest.test_case "positive-k-class-is-not-a-singleton" `Quick
            positive_k_class_is_not_a_singleton;
          Alcotest.test_case "s1-ignorance-witness-deviating" `Quick
            s1_ignorance_witness_deviating;
          Alcotest.test_case "s1-ignorance-witness-honest" `Quick
            s1_ignorance_witness_honest;
          Alcotest.test_case "s2-ignorance-witness-deliberate" `Quick
            s2_ignorance_witness_deliberate;
          Alcotest.test_case "s2-ignorance-witness-flap" `Quick
            s2_ignorance_witness_flap;
          Alcotest.test_case "exempt-refusal-is-free" `Quick
            exempt_refusal_is_free;
          Alcotest.test_case "scored-refusal-is-charged" `Quick
            scored_refusal_is_charged;
          Alcotest.test_case "output-bound-repair-is-present" `Quick
            output_bound_repair_is_present;
          Alcotest.test_case "honest-config-skew-is-reachable" `Quick
            honest_config_skew_is_reachable;
        ] );
    ]
