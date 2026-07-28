(** Confirm-by-mutation pins for the RPC_CODEC_SIZE family: each statement
    proves on the pristine model and REFUTES under the gate deletion it names,
    so the gate is load-bearing and the proof is not an artefact of the
    encoding. Each mutation is also asserted to LEAVE STANDING the statements it
    should not touch, which is what shows the four gates are four gates rather
    than one gate counted four times.

    - {!Rpc_codec_size_model.No_inbound_catchall_penalty} deletes the catch-all
      arm of the inbound [Io] classifier - [_ => { warn!(..); process_penalty(
      peer, Penalty::Medium) }] (consensus.rs:1289-1299). It pins S1 through
      conjunct A: the [AF charged_medium(B)] that a scored peer's prefix
      rejection is supposed to entail no longer holds, because the classify
      transition now settles at [Charge_none]. The ignorance conjunct B, the
      exemption conjunct C and the gossip conjunct D all survive, which is what
      makes this a targeted refutation. Sibling hunt: the outbound mirror
      (:1241-1251) fires on [OutboundFailure] - this node reading a RESPONSE - a
      different event with a different initiator; the gossip route
      (:1063-1073) is left LIVE in the mutated model and is the witness that the
      deletion did not simply disable all charging; the application route
      (:894-901) cannot fire for an inbound codec error, since the application
      never receives a message that failed to decode; and every remaining
      inbound arm is explicitly no-penalty ([UnsupportedProtocols] :1307-1309,
      [Timeout | ConnectionClosed] :1310-1312, [ResponseOmission] :1313).
      [peers/manager.rs:429-443] is the sole entry into
      [AllPeers::process_penalty] (all_peers.rs:261-266) and there is no
      failure-count escalation. The same deletion refutes S2 through its
      conjunct C, and that cross pin is asserted below.
    - {!Rpc_codec_size_model.No_inbound_eof_exemption} deletes
      [ErrorKind::UnexpectedEof] from the exemption chain (consensus.rs:1284,
      one alternative of the [|] list at :1281-1286). It pins S2 through
      conjunct A: truncation falls into the catch-all and the classify
      transition ADDS a [Charge_medium] where the pristine model has none. B
      survives - the two truncation branches stay indistinguishable to V0, they
      are merely both charged now - so the refutation is the charge and not a
      collapse of the epistemics. Sibling hunt: the outbound classifier carries
      the same exemption at :1236 and is a different event; nothing else on the
      inbound path can charge an [UnexpectedEof]; the peer manager's connection
      bookkeeping does not touch score.
    - {!Rpc_codec_size_model.No_trust_exemption} deletes the trust-basis
      short-circuit in [Peer::apply_penalty] (peer.rs:218-233), so an exempt
      peer is scored like any other. It pins S1 through conjunct C from the
      opposite side of the same statement: the committee validator's refusal now
      costs it -5 too. Sibling hunt: [Peer::apply_penalty] is the only caller of
      [Score::apply_penalty] (peer.rs:232); the exemption is resolved once at
      all_peers.rs:261-263 and threaded through, and its only other consumer,
      [Peer::ensure_banned] (:244-252), forwards the same argument to the same
      function, so the deletion disables both together; the network-layer call
      sites pass a bare [(peer_id, penalty)] and know nothing about trust; and
      the ban path keys off [Reputation] alone (all_peers.rs:264-284). It leaves
      S2 standing, because scoring exempt peers cannot create a charge the
      classifier never levied in the first place.
    - {!Rpc_codec_size_model.No_compressed_length_gate} deletes
      [if compressed_len > max_compress_len { return Err(..) }]
      (codec.rs:61-67). It pins S3 through BOTH conjuncts: the inflated
      declaration now enters the read loop at :73-86, so [buffer_amplified]
      becomes reachable and [body_read_ran] becomes true on the branch S3 says
      never reads a byte. The output bounds ARE the sibling path and the model
      has them - [.take(decode_limit)] (:91-93) and the equality check
      (:96-101) still reject the mutated branch and a scored sender is still
      charged Medium, and the pristine [Plan_snappy_short] branch exercises the
      same check on a bounded buffer. They bound [decode_buffer] after the whole
      body is resident; they do not cap the accumulation. [TNCodec::new]'s
      [Vec::with_capacity] (:205-218) is an initial capacity that
      [extend_from_slice] grows past, and [compressed_buffer.clear()] (:44)
      keeps the grown capacity on the per-behaviour codec instance. This
      mutation leaves S1 and S2 standing, since it edits no penalty arm. *)

open Telcoin_epistemic

(** Build the system under a mutation or fail the test on an impossible
    [Empty_init]. *)
let with_mut mut k =
  Result.fold ~ok:k
    ~error:(fun Rpc_codec_size_model.Checker.Empty_init ->
      Alcotest.fail "make: empty init")
    (Rpc_codec_size_model.Checker.make (Rpc_codec_size_model.spec_of mut))

(** Look a statement up by name in the family. *)
let find name =
  List.filter
    (fun st ->
      Int.equal 0 (String.compare st.Rpc_codec_size_statements.name name))
    Rpc_codec_size_statements.all

(** Does the named statement prove under [mut]? Fails the test if the name is
    not in the family at all. *)
let proves_under mut name expected message () =
  match find name with
  | [] -> Alcotest.fail ("unknown statement: " ^ name)
  | st :: _ ->
      with_mut mut (fun sys ->
          Alcotest.(check bool)
            (name ^ " " ^ message)
            expected
            (Result.fold
               ~ok:(fun _ -> true)
               ~error:(fun _ -> false)
               (Rpc_codec_size_statements.prove sys st)))

(** The negative half of a pin: the statement refutes under the mutation. *)
let refuted_under mut name =
  proves_under mut name false "flips to refuted under the mutation"

(** The positive half of a pin: the statement proves on the pristine model. *)
let pristine_proves name =
  proves_under Rpc_codec_size_model.Pristine name true
    "proves on the pristine model"

(** A pristine-proves plus mutated-refutes pair for one statement. *)
let pin mut name =
  [
    Alcotest.test_case (name ^ ":pristine") `Quick (pristine_proves name);
    Alcotest.test_case (name ^ ":mutated") `Quick (refuted_under mut name);
  ]

(** A statement that must SURVIVE a mutation: the evidence that this family's
    four gate deletions are independent. *)
let survives mut name =
  [
    Alcotest.test_case (name ^ ":survives") `Quick
      (proves_under mut name true
         "still proves under the other gate's deletion");
  ]

(** S1's kebab name. *)
let s1 = "oversize-rpc-charge-is-levied-under-peer-config-ignorance"

(** S2's kebab name. *)
let s2 = "truncated-body-is-penalty-exempt-while-an-oversize-declaration-is-not"

(** S3's kebab name. *)
let s3 =
  "compressed-body-accumulation-is-bounded-by-the-declared-uncompressed-length"

let () =
  Alcotest.run "rpc_codec_size_mutation"
    [
      ( "inbound Io catch-all penalty (consensus.rs:1289-1299)",
        pin Rpc_codec_size_model.No_inbound_catchall_penalty s1
        @ [
            Alcotest.test_case (s2 ^ ":also-flips") `Quick
              (refuted_under Rpc_codec_size_model.No_inbound_catchall_penalty s2);
          ]
        @ survives Rpc_codec_size_model.No_inbound_catchall_penalty s3 );
      ( "inbound UnexpectedEof exemption (consensus.rs:1284)",
        pin Rpc_codec_size_model.No_inbound_eof_exemption s2
        @ survives Rpc_codec_size_model.No_inbound_eof_exemption s1
        @ survives Rpc_codec_size_model.No_inbound_eof_exemption s3 );
      ( "trust-basis penalty exemption (peer.rs:218-233)",
        pin Rpc_codec_size_model.No_trust_exemption s1
        @ survives Rpc_codec_size_model.No_trust_exemption s2
        @ survives Rpc_codec_size_model.No_trust_exemption s3 );
      ( "compressed-length gate (codec.rs:61-67)",
        pin Rpc_codec_size_model.No_compressed_length_gate s3
        @ survives Rpc_codec_size_model.No_compressed_length_gate s1
        @ survives Rpc_codec_size_model.No_compressed_length_gate s2 );
    ]
