(** The "63 statements" meta-suite: every statement across the original
    {!Tn_model}, the fourteen first-expansion family models and the forty-two
    second-expansion family models proves on its pristine model, names are
    unique, and the bucket distribution matches the spec exactly (security 23,
    safety 20, liveness 14, fairness 6). The per-family suites hold the
    mutation pins; this suite only guards the aggregate shape. *)

open Telcoin_epistemic

let reports = All_statements.all ()

let sixty_three () =
  Alcotest.(check int) "exactly sixty-three statements" 63 (List.length reports)

let all_proved () =
  Alcotest.(check (list string))
    "every statement proves on its pristine model" []
    (List.filter_map
       (fun r -> if r.Report.proved then None else Some r.Report.name)
       reports)

let unique_names () =
  Alcotest.(check int) "statement names are unique" 63
    (List.length
       (List.sort_uniq String.compare
          (List.map (fun r -> r.Report.name) reports)))

let bucket_count b =
  List.length
    (List.filter
       (fun r ->
         Int.equal 0
           (String.compare (Statements.bucket_to_string r.Report.bucket) b))
       reports)

let distribution () =
  Alcotest.(check (list int))
    "bucket distribution security/safety/liveness/fairness" [ 23; 20; 14; 6 ]
    (List.map bucket_count [ "security"; "safety"; "liveness"; "fairness" ])

let () =
  Alcotest.run "all_statements"
    [
      ( "meta",
        [
          Alcotest.test_case "sixty-three" `Quick sixty_three;
          Alcotest.test_case "all-proved" `Quick all_proved;
          Alcotest.test_case "unique-names" `Quick unique_names;
          Alcotest.test_case "distribution" `Quick distribution;
        ] );
    ]
