(** Uniform cross-model proof report. Per-family statement modules prove over
    their own monomorphic State/View/atom types, so their theorems have
    different types and cannot share a list; the "63 statements, all buckets"
    meta-tests consume this flat projection instead. A [proved = false] row
    means [prove_nonvacuous] did not return [Ok] on the pristine model - the
    aggregator never distinguishes refutation from vacuity, the per-family
    suites do. *)

type t = {
  name : string;  (** statement name, unique across every family *)
  bucket : Statements.bucket;
      (** the shared bucket vocabulary from {!Statements} *)
  proved : bool;
      (** [prove_nonvacuous] returned [Ok] on the family's pristine model *)
}
