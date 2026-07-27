type t = V0 | V1 | V2 | V3 | V4 | V5 | V6 | V7 | V8 | V9

let all = [ V0; V1; V2; V3; V4; V5; V6; V7; V8; V9 ]

let index = function
  | V0 -> 0
  | V1 -> 1
  | V2 -> 2
  | V3 -> 3
  | V4 -> 4
  | V5 -> 5
  | V6 -> 6
  | V7 -> 7
  | V8 -> 8
  | V9 -> 9

let compare a b = Int.compare (index a) (index b)

let equal a b = Int.equal (index a) (index b)

let to_string = function
  | V0 -> "v0"
  | V1 -> "v1"
  | V2 -> "v2"
  | V3 -> "v3"
  | V4 -> "v4"
  | V5 -> "v5"
  | V6 -> "v6"
  | V7 -> "v7"
  | V8 -> "v8"
  | V9 -> "v9"

let quorum = 7

let support = 4
