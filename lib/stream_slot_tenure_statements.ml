(** The admission-slot tenure statement family over the
    {!Stream_slot_tenure_model} interpreted system: one
    [(peer, request_digest)] entry of the primary's [pending_epoch_requests]
    map, from acceptance to release. Mined from telcoin-network, every citation
    re-opened in the working tree of git HEAD 0c59c15b.

    The three statements target three DIFFERENT gates on the same entry, and
    each is pinned by the deletion of its own gate:
    - S1 the EXISTENCE of the timeout eviction (mod.rs:1453-1455): an
      abandoned reservation is released without the peer's cooperation;
    - S2 the NON-REARMING of the deadline (mod.rs:1683-1686): a repeat RPC
      replaces the entry but keeps the original [created_at], so tenure is
      measured from admission and not from activity;
    - S3 the CONSUMPTION of the reservation on stream open (mod.rs:1843-1845):
      one accepted RPC buys at most one epoch-pack transfer.

    READING GUIDE FOR THE K OPERANDS.

    S1 conjunct B is an IGNORANCE claim about V0, the responder. Its operand
    [abandoned(p)] is the frozen hidden disposition of the requester, which is
    not a component of V0's view and is written by no transition: an accepted
    [StreamEpoch] RPC looks identical whether or not the peer intends to open
    the correlated stream, and an [Req_active] peer may idle for as long as it
    likes, so the responder's uncertainty is permanent rather than merely
    delayed. The witness pair required by R3 is concrete: the two initial states
    differ only in that bit and both are reachable, and both survive into every
    phase of the first cleanup interval (see the [contingency] group of
    test/t_stream_slot_tenure.ml). The claim is scoped to a CLEAN reservation
    (held, in-window, unserved, unpenalised) precisely because the responder DOES
    learn the disposition the moment the peer acts - a serve or a refused open
    puts [service] or [charged] into V0's view and collapses the class onto the
    active branch - and a statement that ignored that would be false.

    S3 conjunct C is a POSITIVE K about V1, the requesting peer. Its operand
    [~reserved(p,d)] is the presence of the entry in the RESPONDER's map, which
    is not a component of V1's view - the cleanup notifies nobody
    (mod.rs:1450-1456) and the ack carries no map state - and it is not rigid:
    it is false at every held state, including at the very states V1 cannot
    distinguish from these before it opens the stream. What makes it KNOWN after
    a serve is the consuming lookup at mod.rs:1843-1845 and nothing else, which
    is why {!Stream_slot_tenure_model.Non_consuming_open} destroys it. R2 is
    discharged by the [requester-class-not-singleton] case in
    test/t_stream_slot_tenure.ml: at a served state where the responder's next
    loop step is NOT the cleanup tick, V1 still does not know that - the
    interval's alignment is the responder's - so V1's view class there contains
    at least two reachable states and the knowledge is not trivially true. *)

open Stream_slot_tenure_model

(** A statement over this family's atom vocabulary; [bucket] reuses the shared
    vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous] *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** The admission slot holds no entry for this [(peer, digest)]: the map key is
    absent, so the permit it carried (mod.rs:206-208) is back in the pool and a
    stream open for the digest can no longer be served. *)
let released = Formula.Not (atom Slot_reserved)

(** The weak until [A[p W q]], which is not a kernel constructor, by the kernel
    identity [A[p W q] = ~E[~q U (~p /\ ~q)]]. *)
let weak_until p q =
  Formula.Not (Formula.Eu (Formula.Not q, Formula.And (Formula.Not p, Formula.Not q)))

(** A reservation the responder has learned NOTHING about since it granted it:
    the entry is held, still inside the 30s window, never served, and its peer
    has never been penalised. This is exactly the V0 view class in which the two
    frozen requester dispositions are still superposed. *)
let clean_reservation =
  Formula.conj
    [
      atom Slot_reserved;
      Formula.Not (atom Deadline_passed);
      Formula.Not (atom Served_once);
      Formula.Not (atom Penalty_charged);
    ]

(** S1 - abandoned-admission-slot-released-without-peer-cooperation
    [liveness]. Admission reserves global serve capacity BEFORE any work is
    done - [accept_stream_request] moves an owned semaphore permit into the map
    value (mod.rs:1654-1656, :1687-1688, permit field mod.rs:206-208) - so a
    peer that requests and then walks away is holding capacity it never uses.
    The statement is that this costs the network nothing permanent, and that the
    release cannot be conditioned on knowing who the walk-away peers are.

    Conjunct A (release): AG( reserved(p,d) /\ abandoned(p) -> AF ~reserved(p,d) ).
    Every reservation held by a requester that never opens the correlated stream
    is inevitably released. The only mechanism that can do it is the periodic
    [cleanup_stale_pending_requests] (mod.rs:1450-1456), whose retain drops
    every value older than [PENDING_REQUEST_TIMEOUT] (mod.rs:64) and with it the
    permit; it is driven by the 15s interval arm of the network task's select!
    loop (mod.rs:1426, :1442-1444), a timer the peer cannot starve. The 30s / 15s
    ratio is why the model needs two ticks: the first ages the entry, the second
    evicts it.

    Conjunct B (the ignorance that makes conjunct A necessary): AG(
    clean_reservation -> ~K_V0 abandoned(p) /\ ~K_V0 ~abandoned(p) ). At a
    reservation it has learned nothing about, the responder can neither confirm
    nor rule out that the peer will ever come back for it. Nothing in the
    request-response leg carries an intention: [accept_stream_request] sees a
    peer key, a digest and a kind (mod.rs:1647-1652) and answers [ack]
    (mod.rs:1746-1747); the map value holds a kind, a timestamp and a permit
    (mod.rs:201-209). So the timeout is not a heuristic the responder could
    replace by classifying peers - it is the only thing standing between an
    accepted RPC and a permanently pinned permit.

    Mutation pin: {!Stream_slot_tenure_model.No_stale_prune} deletes the retain
    body at mod.rs:1453-1455, removing the
    [Slot_held, Age_expired] -> [Slot_empty] edge; the abandoned branch then
    holds the permit on every path and conjunct A refutes. No sibling repairs
    it: the only other removal, the consuming lookup at mod.rs:1843-1845,
    requires the peer to open the stream, which the abandoned requester never
    does - so this is not the deletion of a path the code would have taken
    anyway (R8). Conjunct B is untouched by all three mutations, as it should
    be: the hidden bit is read by no gate. *)
let s1 =
  {
    name = "abandoned-admission-slot-released-without-peer-cooperation";
    bucket = Statements.Liveness;
    formula =
      Formula.And
        ( Formula.Ag
            (Formula.Implies
               ( Formula.And (atom Slot_reserved, atom Requester_gone_silent),
                 Formula.Af released )),
          Formula.Ag
            (Formula.Implies
               ( clean_reservation,
                 Formula.And
                   ( Formula.Not
                       (Formula.K (Validator.V0, atom Requester_gone_silent)),
                     Formula.Not
                       (Formula.K
                          ( Validator.V0,
                            Formula.Not (atom Requester_gone_silent) )) ) )) );
    antecedent =
      Formula.And
        ( Formula.Ef
            (Formula.And (atom Slot_reserved, atom Requester_gone_silent)),
          Formula.Ef clean_reservation );
  }

(** S2 - re-request-never-extends-admission-slot-tenure [security]. The
    cheapest way to pin serve capacity is not to hold a stream open, it is to
    refresh the reservation: one 200-byte RPC every 29 seconds. The code
    forecloses it. [accept_stream_request] looks the key up before inserting and
    carries the ORIGINAL timestamp into the replacement - [let created_at =
    pending_map.get(&(peer, request_digest)).map(|p| p.created_at)
    .unwrap_or_else(Instant::now);] (mod.rs:1683-1686), inserted at
    mod.rs:1687-1688 - and its comment (mod.rs:1678-1682) names the attack.

    Conjunct A (the deadline is monotone while the entry lives): AG(
    reserved(p,d) /\ past_deadline(p,d) -> A[ past_deadline(p,d) W
    ~reserved(p,d) ] ). Once [now - created_at] has passed the 30s timeout, it
    stays passed for as long as the entry remains in the map: no transition puts
    a held entry back inside its window. A fresh window is only ever obtained by
    passing through the released state - i.e. by a genuinely new admission,
    which is the [get]-miss branch of the very same expression and is legitimate.
    Weak until is used, not [AU], because a peer that keeps re-requesting keeps
    the entry present, and the claim is about tenure, not about eventual
    release.

    Conjunct B (so the deadline is enforced): AG( reserved(p,d) /\
    past_deadline(p,d) -> AF ~reserved(p,d) ). An over-deadline reservation is
    released on every path, including the paths on which the peer re-requests at
    every opportunity, because the cleanup predicate reads only [created_at]
    (mod.rs:1453-1455).

    Mutation pin: {!Stream_slot_tenure_model.Rearm_created_at} deletes the
    preservation lookup at mod.rs:1683-1686, adding
    [Slot_held, Age_expired] -> [Slot_held, Age_fresh] to the re-request action.
    The one-RPC-per-interval loop then keeps the entry perpetually in-window:
    conjunct A refutes on the first re-request out of the expired state and
    conjunct B refutes on the loop. Sibling hunt: nothing else bounds tenure -
    the per-peer cap (mod.rs:1664-1667) bounds how many slots one identity can
    pin but frees none of them, the global semaphore (mod.rs:1654-1656) only
    refuses new admissions and cannot revoke a held permit, and the consuming
    lookup (mod.rs:1843-1845) needs the peer to open the stream it is
    deliberately not opening. Honest note, reported rather than hidden: conjunct
    B also refutes under {!Stream_slot_tenure_model.No_stale_prune}, because the
    eviction and the non-rearming are jointly necessary for release - that is a
    fact about the code, and conjunct A separates the two gates, holding under
    [No_stale_prune] and failing only under [Rearm_created_at]. *)
let s2 =
  {
    name = "re-request-never-extends-admission-slot-tenure";
    bucket = Statements.Security;
    formula =
      Formula.And
        ( Formula.Ag
            (Formula.Implies
               ( Formula.And (atom Slot_reserved, atom Deadline_passed),
                 weak_until (atom Deadline_passed) released )),
          Formula.Ag
            (Formula.Implies
               ( Formula.And (atom Slot_reserved, atom Deadline_passed),
                 Formula.Af released )) );
    antecedent =
      Formula.Ef (Formula.And (atom Slot_reserved, atom Deadline_passed));
  }

(** S3 - admitted-stream-request-serves-at-most-once [safety]. The inbound
    stream leg looks the reservation up with [remove], not [get]
    (mod.rs:1842-1845), so the reservation is consumed before the serve begins
    and a second stream carrying the same digest finds nothing.

    Conjunct A (at most one serve per admission): AG( ~double_served(p,d) ). One
    accepted RPC never yields two epoch-pack transfers. Note what this does NOT
    claim: a peer whose entry has been consumed may request again and be served
    again - that is the [get]-miss branch of mod.rs:1683-1686 minting a new
    reservation, and the model carries it, so the claim is per-admission and
    survives the repair path rather than depending on its absence.

    Conjunct B (a replay is accountable): AG( replayed(p,d) -> charged(p) ). An
    open of the correlated stream after the admission has been consumed finds
    [None], so [process_request_epoch_stream] returns
    [UnknownStreamRequest(request_digest)] (handler.rs:1139-1149), which maps to
    [Some(Penalty::Mild)] (error/network.rs:189-191) and is reported at
    mod.rs:1848-1856.

    Conjunct C (and the requester can rely on it): AG( served(p,d) -> K_V1
    ~reserved(p,d) ). Once it has been served, the peer KNOWS its reservation is
    gone from the responder's map - not because it observed the removal, which
    it cannot, but because the consuming lookup makes serve and removal the same
    event. This is the peer-side reading of at-most-once, and it is what lets a
    client re-request immediately rather than waiting out the 30s window. It is
    contingent knowledge, not a tautology: before it opens the stream the peer
    cannot tell a live reservation from one the cleanup already evicted, since
    the cleanup notifies nobody (mod.rs:1450-1456).

    Mutation pin: {!Stream_slot_tenure_model.Non_consuming_open} weakens
    mod.rs:1843-1845 from [remove] to [get]. The entry survives the serve, so a
    second open in the same cleanup interval is served again: conjunct A refutes
    at the double-served state, conjunct B refutes because that state carries no
    penalty, and conjunct C refutes because the served state itself is a world in
    V1's own view class in which the reservation is still held. Sibling hunt:
    the serve function has no served-flag (handler.rs:1151-1199), the inbound
    stream dispatch has no per-peer or per-digest gate (mod.rs:1507-1510), the
    cleanup bounds replays in time but not in count (mod.rs:1453-1455), and the
    un-consumed entry still counts only 1 against the cap of 2
    (mod.rs:1664-1667), so nothing re-establishes uniqueness. *)
let s3 =
  {
    name = "admitted-stream-request-serves-at-most-once";
    bucket = Statements.Safety;
    formula =
      Formula.conj
        [
          Formula.Ag (Formula.Not (atom Served_twice));
          Formula.Ag
            (Formula.Implies
               (atom Reopened_after_serve, atom Penalty_charged));
          Formula.Ag
            (Formula.Implies
               (atom Served_once, Formula.K (Validator.V1, released)));
        ];
    antecedent =
      Formula.And
        ( Formula.Ef (atom Served_once),
          Formula.Ef (atom Reopened_after_serve) );
  }

(** The family's statements. *)
let all = [ s1; s2; s3 ]

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
