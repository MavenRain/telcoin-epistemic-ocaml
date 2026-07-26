(** The EXEC-TALLY family statement, encoded over the
    {!Exec_tally_model} interpreted system. Adversarially verified against
    telcoin-network (grounding) and against the finite-model semantics
    (encodability); stated here in the refined form that survived both
    skeptics. File citations refer to Telcoin-Association/telcoin-network.

    Reading guide: K_V0 is grounded in the observer's local state - exactly
    its distinct-signer tally for the modeled consensus output. The strict
    epistemic content is that f+1 = 2 distinct signers pigeonhole at least
    one honest signer, and an honest CVV signs its ConsensusResult only
    after SAVING the output to its consensus chain and strictly BEFORE the
    asynchronous execution handoff (subscriber.rs:280-325: save :286, sign
    :298-302, handoff :317; the save "does NOT imply execution",
    subscriber.rs:151-153), so an advanced watch entails knowledge of an
    honest save/commitment - not of execution - while a lone (possibly
    fabricated) signature never does: the tally = {V3} view recurs both
    before any honest save and after it. *)

open Exec_tally_model

(** A statement over this family's atom vocabulary; [bucket] reuses the
    shared vocabulary of the frozen {!Statements} module. *)
type statement = {
  name : string;
  bucket : Statements.bucket;
  formula : atom Formula.t;
  antecedent : atom Formula.t;
      (** reachability witness required by [prove_nonvacuous]: the proof is
          refused if this never holds, so the statement is never certified
          on the strength of a false antecedent *)
}

(** Atom injection shorthand. *)
let atom a = Formula.Atom a

(** S8 - consensus-output-gossip-tally-implies-known-honest-save
    [safety]. The state-sync observer's watch over the published consensus
    output advances only at f+1 = 2 distinct verified committee signers
    (handler.rs:288-341, threshold gate handler.rs:404-425 at :410,
    consumer state-sync/consensus.rs:233-256); at most one signer is
    Byzantine, and honest CVVs self-sign their gossiped ConsensusResult
    only after SAVING it to their consensus chains - the sign at
    subscriber.rs:298-302 follows the save at :286 and precedes the
    asynchronous execution handoff at :317, which nothing awaits, and the
    signature covers only (epoch, round, number, consensus-header hash)
    (crates/types/src/primary/block.rs:116-160) - so an advanced watch
    carries KNOWLEDGE that some honest CVV saved the output, a
    consensus-chain commitment that deliberately does NOT claim execution
    (subscriber.rs:151-153): G(advance_O -> K_V0(honest-saved)). And
    under bounded-delay result gossip the knowledge is inevitable:
    all-honest-saved ~> (advance_O /\ K_V0(honest-saved)).
    The knowledge is grounded, not rigid: in the fabricate-result branch
    the observer's tally = {V3} both before any honest save and while
    honest results are in flight, so a lone signature leaves the operand
    unknowable and only the intact threshold keeps the watch honest. *)
let s8 =
  let known = Formula.K (Validator.V0, atom Honest_saved) in
  {
    name = "consensus-output-gossip-tally-implies-known-honest-save";
    bucket = Statements.Safety;
    formula =
      Formula.And
        ( Formula.Ag (Formula.Implies (atom Advance_o, known)),
          Formula.leads_to (atom All_honest_saved)
            (Formula.And (atom Advance_o, known)) );
    antecedent = Formula.And (atom Advance_o, atom All_honest_saved);
  }

(** The family's statements: exactly S8. *)
let all = [ s8 ]

(** Prove one statement on a built system, refusing vacuous antecedents. *)
let prove sys st =
  Checker.prove_nonvacuous sys ~antecedent:st.antecedent st.formula

(** Prove every family statement, pairing each with its verdict. *)
let prove_all sys = List.map (fun st -> (st, prove sys st)) all

(** Flat report rows for the cross-model aggregator: a [make] failure
    degrades to [proved = false] rows rather than an exception. *)
let reports () =
  let row proved st =
    { Report.name = st.name; bucket = st.bucket; proved }
  in
  Result.fold
    ~ok:(fun sys ->
      List.map
        (fun (st, r) ->
          row (Result.fold ~ok:(fun _ -> true) ~error:(fun _ -> false) r) st)
        (prove_all sys))
    ~error:(fun Checker.Empty_init -> List.map (row false) all)
    (make ())
