(** The four validators of the finite model: n = 4, f = 1, quorum = 2f+1 = 3.

    Which validator (if any) is Byzantine is a property of the {e model}, not
    of the identity type; the statement modules fix that assignment. Keeping
    the type a bare finite sum gives every consumer exhaustive matching over
    the committee. *)

type t = V0 | V1 | V2 | V3

val all : t list
(** [V0; V1; V2; V3], the committee in canonical order. *)

val compare : t -> t -> int
val equal : t -> t -> bool
val to_string : t -> string

val quorum : int
(** 2f+1 = 3: certificates and round advancement. *)

val support : int
(** f+1 = 2: the Bullshark leader-support threshold. *)
