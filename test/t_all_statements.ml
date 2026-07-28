(** The "189 statements" meta-suite: every statement across the original
    {!Tn_model}, the fourteen first-expansion statements (over twelve isolated
    family models), the forty-two second-expansion statements (over fourteen
    more) the twenty-seven third-expansion statements (over nine more) the
    fifteen fourth-expansion statements (over five more) and the forty-two
    execution-side statements (over fourteen more) and the forty-two
    storage, archive and libp2p statements (over fourteen more)
    proves on its pristine model, names are unique, and the bucket distribution
    matches the spec exactly (security 59, safety 63, liveness 38, fairness 29).
    Sixty-nine models in all. The per-family suites hold the mutation pins;
    this suite only guards the aggregate shape. *)

open Telcoin_epistemic

let reports = All_statements.all ()

let one_hundred_and_eighty_nine () =
  Alcotest.(check int) "exactly one hundred and eighty-nine statements" 189 (List.length reports)

let all_proved () =
  Alcotest.(check (list string))
    "every statement proves on its pristine model" []
    (List.filter_map
       (fun r -> if r.Report.proved then None else Some r.Report.name)
       reports)

let unique_names () =
  Alcotest.(check int) "statement names are unique" 189
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
    "bucket distribution security/safety/liveness/fairness" [ 59; 63; 38; 29 ]
    (List.map bucket_count [ "security"; "safety"; "liveness"; "fairness" ])

let () =
  Alcotest.run "all_statements"
    [
      ( "meta",
        [
          Alcotest.test_case "one-hundred-and-eighty-nine" `Quick one_hundred_and_eighty_nine;
          Alcotest.test_case "all-proved" `Quick all_proved;
          Alcotest.test_case "unique-names" `Quick unique_names;
          Alcotest.test_case "distribution" `Quick distribution;
        ] );
    ]
