type t = V0 | V1 | V2 | V3

let all = [ V0; V1; V2; V3 ]

let index = function V0 -> 0 | V1 -> 1 | V2 -> 2 | V3 -> 3

let compare a b = Int.compare (index a) (index b)

let equal a b = Int.equal (index a) (index b)

let to_string = function V0 -> "v0" | V1 -> "v1" | V2 -> "v2" | V3 -> "v3"

let quorum = 3

let support = 2
