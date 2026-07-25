type 'a t =
  | Atom of 'a
  | Top
  | Bot
  | Not of 'a t
  | And of 'a t * 'a t
  | Or of 'a t * 'a t
  | Implies of 'a t * 'a t
  | Ax of 'a t
  | Ex of 'a t
  | Ag of 'a t
  | Eg of 'a t
  | Af of 'a t
  | Ef of 'a t
  | Au of 'a t * 'a t
  | Eu of 'a t * 'a t
  | K of Validator.t * 'a t
  | Everyone of Validator.t list * 'a t
  | Common of Validator.t list * 'a t

let leads_to p q = Ag (Implies (p, Af q))

let conj fs = List.fold_right (fun f acc -> And (f, acc)) fs Top

let disj fs = List.fold_right (fun f acc -> Or (f, acc)) fs Bot

let group_to_string g =
  String.concat "," (List.map Validator.to_string g)

let rec pp ~atom f =
  let p sub = pp ~atom sub in
  match f with
  | Atom a -> atom a
  | Top -> "true"
  | Bot -> "false"
  | Not sub -> "~(" ^ p sub ^ ")"
  | And (l, r) -> "(" ^ p l ^ " /\\ " ^ p r ^ ")"
  | Or (l, r) -> "(" ^ p l ^ " \\/ " ^ p r ^ ")"
  | Implies (l, r) -> "(" ^ p l ^ " -> " ^ p r ^ ")"
  | Ax sub -> "AX(" ^ p sub ^ ")"
  | Ex sub -> "EX(" ^ p sub ^ ")"
  | Ag sub -> "G(" ^ p sub ^ ")"
  | Eg sub -> "EG(" ^ p sub ^ ")"
  | Af sub -> "F(" ^ p sub ^ ")"
  | Ef sub -> "EF(" ^ p sub ^ ")"
  | Au (l, r) -> "A[" ^ p l ^ " U " ^ p r ^ "]"
  | Eu (l, r) -> "E[" ^ p l ^ " U " ^ p r ^ "]"
  | K (v, sub) -> "K_" ^ Validator.to_string v ^ "(" ^ p sub ^ ")"
  | Everyone (g, sub) -> "E_{" ^ group_to_string g ^ "}(" ^ p sub ^ ")"
  | Common (g, sub) -> "C_{" ^ group_to_string g ^ "}(" ^ p sub ^ ")"
