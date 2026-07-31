(** The ten validators of the finite model: n = 10, f = 3, quorum = 2f+1 = 7.

    Which validators (if any) are Byzantine is a property of the {e model},
    not of the identity type; the statement modules fix that assignment.
    Keeping the type a bare finite sum gives every consumer exhaustive
    matching over the committee.

    Each isolated family model fixes its own module-local roster and
    thresholds: twenty-three of them - the earliest families and the latest
    generation alike - keep a four-member committee with f = 1 rather than
    this ten-member one, leaving [V4] .. [V9] idle and outside the family's
    roster; [all], [quorum] and [support] describe the full committee the
    {!Tn_model} abstraction runs on. *)

type t = V0 | V1 | V2 | V3 | V4 | V5 | V6 | V7 | V8 | V9

val all : t list
(** [V0; ...; V9], the committee in canonical order. *)

val compare : t -> t -> int
val equal : t -> t -> bool
val to_string : t -> string

val quorum : int
(** 2f+1 = 7: certificates and round advancement. *)

val support : int
(** f+1 = 4: the Bullshark leader-support threshold. *)
