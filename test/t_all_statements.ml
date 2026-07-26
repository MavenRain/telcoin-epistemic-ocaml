(** The "21 statements" meta-suite: every statement across the original
    {!Tn_model} and the fourteen expansion family models proves on its
    pristine model, names are unique, and the bucket distribution matches the
    DESIGN spec exactly (security 7, safety 5, liveness 6, fairness 3). The
    per-family suites hold the mutation pins; this suite only guards the
    aggregate shape. *)

open Telcoin_epistemic

let reports = All_statements.all ()

let twenty_one () =
  Alcotest.(check int) "exactly twenty-one statements" 21 (List.length reports)

let all_proved () =
  Alcotest.(check (list string))
    "every statement proves on its pristine model" []
    (List.filter_map
       (fun r -> if r.Report.proved then None else Some r.Report.name)
       reports)

let unique_names () =
  Alcotest.(check int) "statement names are unique" 21
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
    "bucket distribution security/safety/liveness/fairness" [ 7; 5; 6; 3 ]
    (List.map bucket_count [ "security"; "safety"; "liveness"; "fairness" ])

let () =
  Alcotest.run "all_statements"
    [
      ( "meta",
        [
          Alcotest.test_case "twenty-one" `Quick twenty_one;
          Alcotest.test_case "all-proved" `Quick all_proved;
          Alcotest.test_case "unique-names" `Quick unique_names;
          Alcotest.test_case "distribution" `Quick distribution;
        ] );
    ]
