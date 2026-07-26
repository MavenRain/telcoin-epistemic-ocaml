(** The ADMISSION statement family (DESIGN family ADMISSION, #4 and #7),
    encoded over the {!Admission_model} interpreted system. Both statements
    were mined from telcoin-network, adversarially verified against the code
    (grounding) and against the finite-model semantics (encodability), and are
    stated here in the form that survived both skeptics. Both share the single
    joint model and the single admission-denial mutation gate. File citations
    refer to Telcoin-Association/telcoin-network.

    Reading guide: [K (V1, _)] and [K (V2, _)] are grounded in those
    validators' local peer-manager state - a banner sees its own temp-ban
    flags, a subject sees only its bare connection. The epistemically strict
    content is that a banner-local temp-ban flag is invisible to the other
    node: after the connection drops, V1 cannot tell whether V2's ban of it has
    expired (statement #7), and V2 cannot tell whether V1 bans the phantom peer
    O (statement #4). Because bans expire, the severance in #4 is a weak-until,
    not an AG. *)

open Admission_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so no statement is certified on the
          strength of a false antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S4 - ban-is-local-enforcement-and-internode-opaque [safety]. A temp-ban is
    a purely local enforcement act with internode-opaque consequences, stated
    over the phantom NON-COMMITTEE peer O:

    (A) Local enforcement as a WEAK-UNTIL severance: once V1 bans O, no direct
    delivery to O resumes until (if ever) V1 unbans it -
    AG( banned_1(O) -> A[ ~direct_delivery(O,V1) W unbanned_1(O) ] ). The
    weak-until (not AG) is faithful because temp-bans EXPIRE on heartbeat
    ([unban_temp_banned_peers], manager.rs:596-603) and score-model bans decay
    (score.rs:115-155); after unban the admission gate readmits. Encoded per
    the kernel identity A[p W q] = ~E[ ~q U (~p /\\ ~q) ] with p =
    ~direct_delivery(O,V1) = Not Conn_v1o_up and q = unbanned_1(O) =
    Not Ban_1o_active, so ~q = Ban_1o_active: no path keeps the ban active
    until a state where delivery is up while still banned. The retry guard
    (manager.rs:396-403) keeps (Up,Banned) unreachable, so the inner [Eu] is
    unsatisfiable pristine.

    (B) Internode opacity: a ban is peer-manager-local; [PeerEvent::Banned] is
    consumed locally (consensus.rs:1623-1630) and peer-exchange carries no ban
    info, so a validator that has not itself banned O cannot know another has -
    AG( (banned_1(O) /\\ ~banned_2(O)) -> ~K_2(banned_1(O)) ). V2's view holds
    no component of the (V1 -> O) pair, so for any V2-view there is a reachable
    state with ban_1(O) cleared: [K (V2, banned_1(O))] fails. No positive
    companion AG( banned_2(O) -> K_2(banned_1(O)) ) is asserted - it is FALSE,
    the two bans being independent.

    Mutation pin: {!Admission_model.No_admission_denial} deletes the admission
    denial (manager.rs:403), so on (V1 -> O) a dial-retry reaches (Up,Banned) -
    conn(V1,O)=Up while ban_1(O)=Banned before any unban - and the inner [Eu]
    of conjunct A becomes satisfiable, refuting the severance. Conjunct B is
    untouched, so the refutation is cleanly attributable. *)
let s4 =
  let severance =
    (* A[ ~direct_delivery W unbanned ] = Not (Eu (Ban_1o_active,
       And (Conn_v1o_up, Ban_1o_active))); Ban_1o_active is [Not unbanned_1O]. *)
    Formula.Ag
      (Formula.Implies
         ( atom Ban_1o_active,
           Formula.Not
             (Formula.Eu
                ( atom Ban_1o_active,
                  Formula.And (atom Conn_v1o_up, atom Ban_1o_active) )) ))
  in
  let opacity =
    Formula.Ag
      (Formula.Implies
         ( Formula.And (atom Ban_1o_active, Formula.Not (atom Ban_2o_active)),
           Formula.Not (Formula.K (Validator.V2, atom Ban_1o_active)) ))
  in
  {
    name = "ban-is-local-enforcement-and-internode-opaque";
    bucket = Statements.Safety;
    formula = Formula.And (severance, opacity);
    antecedent = Formula.And (atom Ban_1o_active, Formula.Not (atom Ban_2o_active));
  }

(** S7 - established-connection-implies-known-remote-admission [safety], over
    the (V2 -> V1) pair with knower V1:

    (1) admission gate: V1 is admitted to V2 only when not currently banned -
    G( admitted -> ~banned_2(V1) ). The atomic seed (ban+disconnect in one
    transition, the [DisconnectWithPX] analogue) makes the in-flight window a
    non-state, so admitted reduces to conn(V2,V1)=Up; (Up,Banned) is unreachable
    pristine, so the gate holds.

    (2) knowledge of remote admission: while connected (and, vacuously, no ban
    disconnect in flight) V1 knows it is not banned -
    G( connected(V1,V2) -> K_V1(~banned_2(V1)) ). Every reachable conn(V2,V1)=Up
    state has ban_2(V1)=Unbanned, so [K (V1, ~banned_2(V1))] holds there - and
    this is grounded, not rigid: at disconnected states the knowledge fails.

    (3) temp-ban ignorance window: while V2's temp-ban of V1 is active, V1 -
    which sees only the dropped connection, never V2's banner-local flag - can
    neither confirm nor rule out the ban - G( tempban_window ->
    ~K_V1(banned_2(V1)) /\\ ~K_V1(~banned_2(V1)) ). The seed state (conn Down,
    ban active) and its post-expiry sibling (conn Down, ban cleared, sending
    NOTHING to V1) share V1's view, so both knowledge claims fail. tempban_window
    = banned_2(V1) = ban_2(V1)=Active.

    Mutation pin: {!Admission_model.No_admission_denial} makes (Up,Banned)
    reachable on (V2 -> V1) - conn(V2,V1)=Up while ban_2(V1)=Banned - so V1 is
    admitted while banned (conjunct 1 fails) and the conn-up view class gains a
    banned state (conjunct 2's [K] fails), refuting the statement. Citations:
    behavior.rs:87-134 (admission), manager.rs:396-404 / :327-353 (dial +
    apply_peer_action), manager.rs:596-603 (heartbeat expiry). *)
let s7 =
  let admission_gate =
    Formula.Ag
      (Formula.Implies (atom Conn_v2v1_up, Formula.Not (atom Ban_2v1_active)))
  in
  let known_admission =
    Formula.Ag
      (Formula.Implies
         ( atom Conn_v2v1_up,
           Formula.K (Validator.V1, Formula.Not (atom Ban_2v1_active)) ))
  in
  let ignorance_window =
    Formula.Ag
      (Formula.Implies
         ( atom Ban_2v1_active,
           Formula.And
             ( Formula.Not (Formula.K (Validator.V1, atom Ban_2v1_active)),
               Formula.Not
                 (Formula.K (Validator.V1, Formula.Not (atom Ban_2v1_active))) ) ))
  in
  {
    name = "established-connection-implies-known-remote-admission";
    bucket = Statements.Safety;
    formula =
      Formula.And (admission_gate, Formula.And (known_admission, ignorance_window));
    antecedent = atom Ban_2v1_active;
  }

(** The family's statements: #4 and #7, both safety, both pinned by the shared
    admission-denial gate. *)
let all = [ s4; s7 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

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
