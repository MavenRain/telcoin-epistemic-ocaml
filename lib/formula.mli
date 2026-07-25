(** CTLK: branching-time temporal logic with knowledge operators, interpreted
    over finite interpreted systems (Fagin-Halpern-Moses-Vardi, "Reasoning
    About Knowledge", ch. 4).

    Atoms are a caller-supplied sum type ['a], so each statement module gets
    exhaustive matching over its own atom vocabulary instead of stringly-typed
    labels. Temporal operators quantify over paths of the transition graph
    (A = all paths, E = some path); knowledge operators quantify over reachable
    global states indistinguishable in a validator's local view.

    The linear-time surface syntax used in the statement docs maps in as the
    universal fragment: G phi = [Ag] phi, F phi = [Af] phi, p ~> q =
    [leads_to] p q = AG (p -> AF q). *)

type 'a t =
  | Atom of 'a
  | Top
  | Bot
  | Not of 'a t
  | And of 'a t * 'a t
  | Or of 'a t * 'a t
  | Implies of 'a t * 'a t
  | Ax of 'a t  (** on every successor state *)
  | Ex of 'a t  (** on some successor state *)
  | Ag of 'a t  (** on all paths, at every point: invariant *)
  | Eg of 'a t  (** on some path, at every point *)
  | Af of 'a t  (** on all paths, eventually: inevitability *)
  | Ef of 'a t  (** on some path, eventually: reachability *)
  | Au of 'a t * 'a t  (** A[p U q] *)
  | Eu of 'a t * 'a t  (** E[p U q] *)
  | K of Validator.t * 'a t
      (** [K (i, phi)]: phi holds at every reachable global state whose
          i-projection equals the current one - i's local state entails phi. *)
  | Everyone of Validator.t list * 'a t
      (** [E_G phi]: every validator in G knows phi. [Everyone ([], phi)] is
          vacuously [Top]. *)
  | Common of Validator.t list * 'a t
      (** [C_G phi]: common knowledge in G - the greatest fixpoint of
          [fun x -> Everyone (g, And (phi, x))]. *)

val leads_to : 'a t -> 'a t -> 'a t
(** [leads_to p q] = [Ag (Implies (p, Af q))], Lamport's p ~> q. *)

val conj : 'a t list -> 'a t
(** Right-nested conjunction; [conj []] = [Top]. *)

val disj : 'a t list -> 'a t
(** Right-nested disjunction; [disj []] = [Bot]. *)

val pp : atom:('a -> string) -> 'a t -> string
(** Render with the surface notation used in the statement docs
    (G, F, AX, K_v0, E_H, C_H, ->, ~, /\, \/). *)
