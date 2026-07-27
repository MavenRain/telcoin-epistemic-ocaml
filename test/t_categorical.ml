(** Gate 4 — categorical-law pins (DESIGN sec.6 gate 4), confirm-by-mutation:
    each law is asserted POSITIVELY on the bespoke operators and paired with a
    NEGATIVE witness (a deliberately wrong operator, or a mis-seed) that
    violates the very same law — so a regression could not pass silently.

    Small synthetic frame: states 0..3 encode two bits [(b0,b1)]; validator V0
    observes [b0], V1 observes [b1] (partial information, so [K_i] is
    non-trivial). One transition [0 → 3] makes [AF] non-degenerate for the
    μ-vs-ν seed pin. *)

open Telcoin_epistemic

module F = Frame.Make (Int) (Int)
module Bc = Basechange.Make (F)
module Fx = Fix.Make (F)
module Kn = Knows.Make (F)

let b0 s = s / 2
let b1 s = s mod 2

let view v s =
  match v with
  | Validator.V0 -> b0 s
  | Validator.V1 -> b1 s
  | Validator.V2 -> b0 s
  | Validator.V3 -> b1 s
  (* V4..V9: non-participants of this toy frame - constant blind view. *)
  | Validator.V4 | Validator.V5 | Validator.V6 | Validator.V7 | Validator.V8
  | Validator.V9 ->
      0

type atom = P

let label a s = match a with P -> Int.equal s 3

let spec : atom F.spec =
  {
    F.init = [ 0; 1; 2; 3 ];
    next = (fun s -> if Int.equal s 0 then [ 3 ] else []);
    view;
    label;
  }

let with_t k =
  Result.fold ~error:(fun F.Empty_init -> Alcotest.fail "frame init")
    ~ok:k (F.make spec)

let ss = F.State_set.of_list
let vs = F.View_set.of_list
(* A singleton group: C_group then descends to a NON-TRIVIAL fixpoint (the
   two-agent group is fully C-connected on this frame, collapsing to ∅). *)
let group = [ Validator.V0 ]

(* -- Galois adjunctions Σ_f ⊣ f* ⊣ Π_f (DESIGN sec.3, sec.6 gate 4) -------- *)

let ex_law t i a b =
  Bool.equal
    (F.View_set.subset (Bc.exists_view t i a) b)
    (F.State_set.subset a (Bc.reindex_view t i b))

(* mutation: exists that ignores its argument (always the full image). *)
let ex_law_broken t i a b =
  Bool.equal
    (F.View_set.subset (Bc.exists_view t i (F.reach t)) b)
    (F.State_set.subset a (Bc.reindex_view t i b))

let fa_law t i a b =
  Bool.equal
    (F.State_set.subset (Bc.reindex_view t i b) a)
    (F.View_set.subset b (Bc.forall_view t i a))

(* mutation: forall replaced by exists (the wrong adjoint). *)
let fa_law_broken t i a b =
  Bool.equal
    (F.State_set.subset (Bc.reindex_view t i b) a)
    (F.View_set.subset b (Bc.exists_view t i a))

let ex_pairs =
  [ (ss [ 0; 1 ], vs [ 0 ]); (ss [ 3 ], vs [ 1 ]); (ss [ 0 ], vs [ 0; 1 ]);
    (ss [ 2; 3 ], vs [ 1 ]); (ss [ 0 ], vs [ 1 ]); (ss [ 0; 1; 2; 3 ], vs [ 0; 1 ]) ]

let galois_exists () =
  with_t (fun t ->
      Alcotest.(check (pair bool bool))
        "exists_ ⊣ f* holds; the broken exists violates it"
        (true, true)
        ( List.for_all (fun (a, b) -> ex_law t Validator.V0 a b) ex_pairs,
          List.exists
            (fun (a, b) -> Bool.not (ex_law_broken t Validator.V0 a b))
            ex_pairs ))

let galois_forall () =
  with_t (fun t ->
      Alcotest.(check (pair bool bool))
        "f* ⊣ forall_ holds; the broken forall violates it"
        (true, true)
        ( List.for_all (fun (a, b) -> fa_law t Validator.V0 a b) ex_pairs,
          List.exists
            (fun (a, b) -> Bool.not (fa_law_broken t Validator.V0 a b))
            ex_pairs ))

(* -- K_i as a lex idempotent S5 comonad (DESIGN sec.3) --------------------- *)

(* The ∃-along-the-fibre "knowledge" — the wrong (non-factive) operator. *)
let k_dia t i s_set =
  F.State_set.filter
    (fun s ->
      Bool.not (F.State_set.is_empty (F.State_set.inter (F.fibre t i s) s_set)))
    (F.reach t)

let knows_is_fibre_subset () =
  with_t (fun t ->
      let direct s_set =
        F.State_set.filter
          (fun s -> F.State_set.subset (F.fibre t Validator.V0 s) s_set)
          (F.reach t)
      in
      Alcotest.(check bool) "K_i = f_i* ∘ Π_{f_i} = {s | class(s) ⊆ S}" true
        (List.for_all
           (fun s_set ->
             F.State_set.equal (Kn.knows t Validator.V0 s_set) (direct s_set))
           [ ss [ 0; 1 ]; ss [ 3 ]; ss [ 0 ]; ss [ 2; 3 ]; F.reach t ]))

let factivity () =
  with_t (fun t ->
      (* S must NOT be a union of full V0-fibres, else even the non-factive
         k_dia stays ⊆ S and a regression of [knows] to it would pass. On
         S = {0,1,3}: knows V0 S = {0,1} ⊆ S (factive, non-empty), whereas
         k_dia V0 S = {0,1,2,3} ⊄ S. *)
      let s = ss [ 0; 1; 3 ] in
      Alcotest.(check (pair bool bool))
        "K S ⊆ S (counit); the ∃-knowledge k_dia is NOT factive on the same S"
        (true, false)
        ( F.State_set.subset (Kn.knows t Validator.V0 s) s,
          F.State_set.subset (k_dia t Validator.V0 s) s ))

let idempotence () =
  with_t (fun t ->
      (* Witness chosen so [knows] is a NON-EMPTY proper subset (not the
         degenerate K∅=∅ that any operator satisfies): knows V0 {0,1,2} =
         {0,1} (fibre {0,1}⊆, {2,3}⊄), then KK = K = {0,1}. The non-empty
         guard makes a regression of [knows] to the empty set fail here. *)
      let s = ss [ 0; 1; 2 ] in
      let k = Kn.knows t Validator.V0 s in
      let kk = Kn.knows t Validator.V0 k in
      Alcotest.(check (list bool))
        "K K S = K S (idempotent), K S non-empty, and K S ⊊ S"
        [ true; true; true ]
        [
          F.State_set.equal kk k;
          Bool.not (F.State_set.is_empty k);
          Bool.not (F.State_set.equal k s);
        ])

let euclidean () =
  with_t (fun t ->
      let s = ss [ 0; 1 ] in
      let nk = F.State_set.diff (F.reach t) (Kn.knows t Validator.V0 s) in
      Alcotest.(check (pair bool bool))
        "¬K S ⊆ K(¬K S) (S5 Euclidean) with ¬K S non-empty"
        (true, true)
        ( F.State_set.subset nk (Kn.knows t Validator.V0 nk),
          Bool.not (F.State_set.is_empty nk) ))

(* -- C_G gfp convergence bound ≤ |reach| (DESIGN sec.3, sec.6 gate 4) ------- *)

let common_converges () =
  with_t (fun t ->
      let n = F.reachable_count t in
      (* Drive the REAL [Kn.common] with a non-trivial φ so the gfp performs a
         STRICTLY descending chain (reach ⊋ {0,1}) rather than sitting on an
         immediate fixpoint: C_group {0,1,2} = gfp z. E_group ({0,1,2} ∩ z) =
         {0,1}. The value assertion pins correctness; steps > 0 pins that it
         genuinely iterated; steps ≤ n pins the Knaster-Tarski bound. *)
      let phi = ss [ 0; 1; 2 ] in
      let cg = Kn.common t group phi in
      let steps =
        Fx.steps_to_fix t ~seed:(F.reach t) (fun z ->
            Kn.everyone t group (F.State_set.inter phi z))
      in
      Alcotest.(check (pair bool bool))
        ("C_group {0,1,2} = {0,1} (non-trivial fixpoint) in "
        ^ Int.to_string steps ^ " steps, 0 < steps ≤ " ^ Int.to_string n)
        (true, true)
        (F.State_set.equal cg (ss [ 0; 1 ]), steps > 0 && steps <= n))

(* -- μ-vs-ν seed correctness (DESIGN sec.6 gate 4) ------------------------- *)

let seed_discipline () =
  with_t (fun t ->
      let bset_p = F.State_set.filter (label P) (F.reach t) in
      let af_body z = F.State_set.union bset_p (Bc.pre_all t z) in
      let correct = Fx.lfp t af_body in
      (* mis-seeding the μ at ⊤ = reach collapses AF to ⊤. *)
      let misseeded = Fx.iterate t ~seed:(F.reach t) af_body in
      Alcotest.(check (list bool))
        "μ seeded ⊥ excludes world 1; mis-seeded ⊤ collapses to reach"
        [ false; true; true ]
        [
          F.State_set.mem 1 correct;
          F.State_set.mem 1 misseeded;
          F.State_set.equal misseeded (F.reach t);
        ])

(* -- the presheaf-topos functoriality certificate (comp_cat Res/Err) ------- *)

let functoriality_certified () =
  with_t (fun t ->
      Alcotest.(check bool) "Frame.certify_functorial = Ok (⊑ is a finite poset)"
        true
        (Result.fold ~ok:(fun () -> true) ~error:(fun _ -> false)
           (F.certify_functorial t)))

let () =
  Alcotest.run "categorical"
    [
      ( "topos",
        [ Alcotest.test_case "functoriality-certified" `Quick functoriality_certified ] );
      ( "galois",
        [
          Alcotest.test_case "exists-adjoint" `Quick galois_exists;
          Alcotest.test_case "forall-adjoint" `Quick galois_forall;
        ] );
      ( "knowledge-comonad",
        [
          Alcotest.test_case "k-is-fibre-subset" `Quick knows_is_fibre_subset;
          Alcotest.test_case "factivity" `Quick factivity;
          Alcotest.test_case "idempotence" `Quick idempotence;
          Alcotest.test_case "euclidean" `Quick euclidean;
        ] );
      ( "fixpoints",
        [
          Alcotest.test_case "common-converges" `Quick common_converges;
          Alcotest.test_case "seed-discipline" `Quick seed_discipline;
        ] );
    ]
