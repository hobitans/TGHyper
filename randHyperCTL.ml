open FormulaHyperCTL

(*
  Assigns randomly atomic proposition to earlier in the formul quantfied path variables.
*)

let hyperctl_rand_test = 
  "forall p1.(((G(a7_p0))&(((((forall p6.(((forall p4.(((F(a1_p0))&(a4_p0))))R(((((a1_p1)U(a9_p9)))
    R(((((forall p4.(forall p5.(G(forall p9.
    (F(forall p5.(forall p5.(F(a7_p8)))))))))|(forall p9.(a0_p6))))&(a4_p1))))))))
    &(forall p9.(F(a6_p4)))))&(forall p0.(((a5_p6)U(F(a9_p7)))))))))"
  

let verbose = ref false;;

let get_rand_from_lst lst = 
    let pos =  Random.int (List.length lst) in
    List.nth  lst pos


let rand_assign ap pvs =
    let pv = get_rand_from_lst pvs in
    Var(ap,pv)


let rec assignAPtoPV_ formula pvs = 
  let rec_ f = assignAPtoPV_ f pvs in
  match formula with
    | True -> False
    | False -> True
    | Var (ap, pv) -> rand_assign ap pvs 
    | Not f -> Not ( rec_ f )
    | Or (f, g) -> Or(rec_ f, rec_ g)
    | And (f, g) -> And(rec_ f, rec_ g)
    | Impl (f, g) -> Impl(rec_ f, rec_ g) 
    | Equiv (f, g) -> Equiv(rec_ f, rec_ g)
    | Next f -> Next (rec_ f)
    | Finally f -> Finally (rec_ f)
    | Globally f -> Globally (rec_ f)
    | Until (f, g) -> Until(rec_ f, rec_ g)
    | WeakUntil (f, g) -> WeakUntil ( rec_ f ,  rec_ g)
    | Release (f, g) -> Release(rec_ f, rec_ g)
    | Exists (id, f) -> Exists (id, (assignAPtoPV_ f (id::pvs)) )
    | Forall (id, f) -> Forall (id, (assignAPtoPV_ f (id::pvs)) )


  let assignAPstoPV formula formula_file = 
    if !verbose then (Printf.printf "Input rand formula:"; print_hyperCTL formula);
    let f = assignAPtoPV_ formula [] in
    let size = getFormulaSize f in 
    if !verbose then (Printf.printf "Output rand formula:(%d)" size; print_hyperCTL f);

    (* check valid *)
    let print =
    try
       EnfFormula.check_and_transform f;
       true
    with e -> false
    in

    if !verbose then Printf.printf  "%s\n" (hyperctl_str f);

    f



