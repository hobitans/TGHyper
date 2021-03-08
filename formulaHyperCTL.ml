(* 
Adapt formula.ml from MGHyper and EAHyper to handle hyperctl formulas, thus quantfication at arbitrary postions.
We add some functionalyt to the nnf translation for handling globally and finally operators instead of translating them
to Until or release.
*)

open Printf
open Functions



type hyperctl_formula =
    True
  | False
  | Var of string * string
  | Not of hyperctl_formula
  | Or of hyperctl_formula * hyperctl_formula
  | And of hyperctl_formula * hyperctl_formula
  | Impl of hyperctl_formula * hyperctl_formula
  | Equiv of hyperctl_formula * hyperctl_formula
  | Next of hyperctl_formula
  | Until of hyperctl_formula * hyperctl_formula
  | WeakUntil of hyperctl_formula * hyperctl_formula
  | Release of hyperctl_formula * hyperctl_formula
  | Finally of hyperctl_formula
  | Globally of hyperctl_formula
  | Exists of string * hyperctl_formula
  | Forall of string * hyperctl_formula




exception Identifier_notunique of string
exception Identifier_rebound of string
exception Identifier_unbound of string
exception Error of string




(* VARS *)
let verbose = ref true;;


(**
CHECK for valid HyperCTL formula
  - ENF form
  - all AP bound by PV in Scope
*)
let check_hyperCTL_formula = 
        (* todo check ENF *)
        True



(* get all APs from formula *)
let rec getAPs_ f = 
    match f with 
      True | False -> []
    | Var (x, _) -> [x]
    | Not f | Next f | Finally f | Globally f | Exists (_, f) | Forall (_, f) -> getAPs_ f 
    | And (f, g) | Impl (f, g) | Equiv (f, g) | Or (f, g) | Until (f, g) |  WeakUntil (f, g) | Release (f, g) ->  getAPs_ f @ getAPs_ g

let getAPs f = 
    let aps = foldr_rem_dupl ( getAPs_ f ) in 
    (* print_list aps ; *)
    aps


let rec getPVs_ f exx all =
  match f with 
    True | False | Var (_, _) -> exx , all
  | Exists (p , f) -> getPVs_ f (p::exx) all
  | Forall (p , f) -> getPVs_ f exx (p::all) 
  | Not f | Next f | Finally f | Globally f  -> getPVs_ f exx all 
  | And (f, g) | Impl (f, g) | Equiv (f, g) | Or (f, g) | Until (f, g) |  WeakUntil (f, g) | Release (f, g) -> getPVs__ f g exx all 

and getPVs__ f g exx all = 
    let (exf,alf) =  getPVs_ f [] [] in 
    let (exg,alg) =  getPVs_ g  [] [] in
    (exx@exf@exg, all@alf@alg)

    
let getPVs f = 
  let (exx, all) = getPVs_ f [] [] in 
  (*
  printf "\n";
  print_list (exx) ;
  printf "\n";
  print_list (all) ;
  printf "check for dulicates\n"; *)
  if dupl_exists (exx@all)
  then 
      begin
        raise (Error "Duplicate path variables")
      end
  else (exx, all)



    (* check if formula is purly universally quantfied --> need exists var *)
    let rec only_forall f  = 
      match f with 
        Exists(_,_) -> false
      | True | False | Var(_,_) -> true
      | Forall(_,f) |Not f | Next f | Finally f | Globally f  -> only_forall f
      | And (f, g) | Impl (f, g) | Equiv (f, g) | Or (f, g) | Until (f, g) |  WeakUntil (f, g) | Release (f, g) ->  only_forall f && only_forall g 
    



(******************************)
let replaceVarPVbyTv_  pv tv x y =
  if pv <> y 
  then (Var(x,y))
  else (Var(x,tv))



let rec replacePVbyTV pv tv f =
  match f with
      True -> True
    | False -> False
    | Var (x, y) -> replaceVarPVbyTv_ pv tv x y
    | And (f, g) -> And (replacePVbyTV pv tv f, replacePVbyTV pv tv g)
    | Or (f, g) -> Or (replacePVbyTV pv tv f, replacePVbyTV pv tv g)
    | Impl (f, g) -> Impl (replacePVbyTV pv tv f, replacePVbyTV pv tv g)
    | Equiv (f, g) -> Equiv (replacePVbyTV pv tv f, replacePVbyTV pv tv g)
    | Until (f, g) -> Until (replacePVbyTV pv tv f, replacePVbyTV pv tv g)
    | WeakUntil (f, g) -> WeakUntil (replacePVbyTV pv tv f, replacePVbyTV pv tv g)
    | Release (f, g) -> Release (replacePVbyTV pv tv f, replacePVbyTV pv tv g)
    | Not f -> Not (replacePVbyTV pv tv f)
    | Next f -> Next (replacePVbyTV pv tv f)
    | Finally f -> Finally (replacePVbyTV pv tv f)
    | Globally f -> Globally (replacePVbyTV pv tv f)
    | Exists (x, f) -> Exists (x, replacePVbyTV pv tv f)
    | Forall (x, f) -> Forall (x, replacePVbyTV pv tv f)


(* hyperCTL_str: print HyperCTL formula *)
let rec hyperctl_str_ buf f =
  let abuf = Buffer.add_string buf in
  let rec_ = hyperctl_str_ buf in
    match f with
        True -> abuf "True"
      | False -> abuf "False"
      | Var (a, x) -> abuf a; abuf "_"; abuf x
      | Not f -> abuf "~("; rec_ f; abuf ")"
      | Or (f, g) -> abuf "(("; rec_ f; abuf " )|( "; rec_ g; abuf "))"
      | And (f, g) -> abuf "(("; rec_ f; abuf ") & ("; rec_ g; abuf "))"
      | Impl (f, g) -> abuf "(("; rec_ f; abuf ") -> ("; rec_ g; abuf "))"
      | Equiv (f, g) -> abuf "(("; rec_ f; abuf ") <->( "; rec_ g; abuf "))"
      | Next f -> abuf "X("; rec_ f; abuf ")"
      | Until (f, g) -> abuf "(("; rec_ f; abuf " )U( "; rec_ g; abuf "))"
      | WeakUntil (f, g) -> abuf "(("; rec_ f; abuf " )W( "; rec_ g; abuf "))"
      | Release (f, g) -> abuf "(("; rec_ f; abuf " )R( "; rec_ g; abuf "))"
      | Finally f -> abuf "F("; rec_ f; abuf ")"
      | Globally f -> abuf "G("; rec_ f; abuf ")"
      | Exists (v, f) -> abuf "exists "; abuf v; abuf ".("; rec_ f; abuf ")"
      | Forall (v, f) -> abuf "forall "; abuf v; abuf ".("; rec_ f; abuf ")"

let hyperctl_str f =
  let buf = Buffer.create 0 in
  hyperctl_str_ buf f; let str = Buffer.contents buf in Buffer.reset buf; str


(****************************************************************)
(************ NNF transformation ********************************)
(****************************************************************)
let pvlst = ref [];; 

let rec ren_pv p str = 
  let new_pv = p^str in
  if List.mem new_pv !pvlst 
  then ren_pv new_pv str
  else (
    pvlst := new_pv::(!pvlst);
    new_pv
  )

let rec rename_sub_quant f str = 
  let rec_ f = rename_sub_quant f str in
  match f with 
      True | False | Var (_, _) -> f
      | Not f           -> Not ( rec_ f)
      | Next f          -> Next ( rec_ f)
      | Finally f       -> Finally (rec_ f )
      | Globally f      -> Globally (rec_ f  )
      | Until (f, g)    -> Until (rec_ f, rec_ g)
      | WeakUntil (f, g) -> WeakUntil (rec_ f, rec_ g)
      | Release (f, g)  -> Release (rec_ f, rec_ g)
      | Impl (f, g)     -> Impl(rec_ f, rec_ g)
      | Equiv (f, g)    -> Equiv (rec_ f, rec_ g)
      | And (f, g)      -> And ( rec_ f, rec_ g )
      | Or (f, g)       -> Or (rec_ f, rec_ g)
      | Forall (pv , f)  -> (let new_pv = ren_pv pv str in Forall (new_pv, rec_ (replacePVbyTV pv new_pv f) ) )
      | Exists (pv , f)  -> (let new_pv = ren_pv pv str in Exists (new_pv, rec_ (replacePVbyTV pv new_pv f) ) )


(* negated normal form with globally, finally -> to until *)
let rec n_nnf f = 
  match f with
      True -> False
    | False -> True
    | Var (_, _) -> Not f
    | Next f -> Next (n_nnf f ) 
    | Not f -> nnf_ f
    | Globally f -> n_nnf (Release (False, f))
    | Release (f, g) -> Until (n_nnf f, n_nnf g)
    | Finally f -> n_nnf (Until (True, f))
    | Until (f, g) -> Release (n_nnf f, n_nnf g)
    | WeakUntil (f, g) ->  (
        let r_g = rename_sub_quant g "r" in
        let r_f = rename_sub_quant f "f" in
          Until(And(nnf_ r_f, (n_nnf r_g)), (And(n_nnf f, n_nnf g))  )
          )  (**todo: check reduction !!! **)
    | Impl (f, g) -> n_nnf (Or (Not f, g))
    | Equiv (f, g) -> (
            let r_f = rename_sub_quant f "r"  in
            let r_g = rename_sub_quant g "r" in
            n_nnf (And (Impl (f, g), Impl (r_g, r_f)))
        )
    | Or (f, g) -> And (n_nnf f, n_nnf g)
    | And (f, g) -> Or (n_nnf f, n_nnf g)
    | Exists (id, f) -> Forall (id, n_nnf f)
    | Forall (id, f) -> Exists (id, n_nnf f)

and nnf_ f =
  match f with
      Var(a,pv) -> Var(a,pv)
    | False -> False
    | True -> True
    | Not f -> n_nnf f
    | Next f -> Next (nnf_ f)
    | Finally f -> nnf_ (Until (True, f)) 
    | Globally f -> nnf_ (Release (False, f)) 
    | Impl (f, g) -> nnf_ (Or (Not f, g)) 
    | Equiv (f, g) -> (
            let f = nnf_ f in
            let g = nnf_ g in
            let r_f = nnf_ (rename_sub_quant f "r" ) in
            let r_g = nnf_ (rename_sub_quant g "r" ) in
            And ((Or (Not f, g)), (Or (Not r_g, r_f)))
        )
    | And (f, g) -> And (nnf_ f, nnf_ g)
    | Or (f, g) -> Or (nnf_ f, nnf_ g)
    | Until (f, g) -> Until (nnf_ f , nnf_ g )
    | WeakUntil (f, g) ->  (
            let f = nnf_ f in
            let g = nnf_ g in
            let r_g = nnf_ (rename_sub_quant g "r" ) in
            Release (r_g, Or (f, g))       (**todo: check reduction !!! **)
          ) (**todo: check reduction !!! **)
    | Release (f, g) -> Release (nnf_ f, nnf_ g)
    | Forall (id, f) -> Forall (id, nnf_ f)
    | Exists (id, f) -> Exists (id, nnf_ f)


  
let nnf f  =
    let (exx,all) = getPVs f in
    pvlst :=  exx@all;
    nnf_ f


(* negated normal form with globally, finally -> to until *)
let rec nnf_fast_ f =
  match f with
    Var(a,pv) -> Var(a,pv)
  | True -> True
  | False -> False
  | Not f -> n_nnf_fast f 
  | Next f -> Next (nnf_fast_ f )
  | Globally f -> Globally (nnf_fast_ f  )
  | Finally f -> Finally (nnf_fast_ f )
  | Until (f, g) -> Until (nnf_fast_ f , nnf_fast_ g )
  | Release (f, g) -> Release (nnf_fast_ f , nnf_fast_ g )  
  | WeakUntil (f, g) ->  (
    let f = nnf_fast_ f in
    let g = nnf_fast_ g in
    let r_g = nnf_fast_ (rename_sub_quant g "r" ) in
    Release (r_g, Or (f, g))       (**todo: check reduction !!! **)
)
  | Impl (f, g) -> nnf_fast_ (Or (Not f, g)) 
  | Equiv (f, g) -> (
      let f = nnf_fast_ f in
      let g = nnf_fast_ g in
      let r_f = nnf_fast_ (rename_sub_quant f "r" ) in
      let r_g = nnf_fast_ (rename_sub_quant g "r" ) in
      And ((Or (Not f, g)), (Or (Not r_g, r_f)))
  )
    
  | Or (f, g) -> Or (nnf_fast_ f , nnf_fast_ g )
  | And (f, g) -> And (nnf_fast_ f , nnf_fast_ g )
  | Exists (id, f) -> Exists (id, nnf_fast_ f )
  | Forall (id, f) -> Forall (id, nnf_fast_ f )

  
and n_nnf_fast f =
    match f with
      True -> False
    | False -> True
    | Var (a, pv) -> Not (Var(a,pv))
    | Not f -> nnf_fast_ f
    | Next f -> Next (n_nnf_fast f) 
    | Globally f -> n_nnf_fast (Release (False, f))
    | Impl (f, g) -> n_nnf_fast (Or (Not f, g))
    | Finally f -> n_nnf_fast (Until (True, f))
    | Equiv (f, g) -> (
      let r_f = rename_sub_quant f "r"  in
      let r_g = rename_sub_quant g "r" in
      n_nnf_fast (And (Impl (f, g), Impl (r_g, r_f)))
   )
    | Or (f, g) -> And (n_nnf_fast f, n_nnf_fast g)
    | And (f, g) -> Or (n_nnf_fast f, n_nnf_fast g)
    | Until (f, g) -> Release (n_nnf_fast f, n_nnf_fast g)
    | WeakUntil (f, g) ->  (
      let r_g = rename_sub_quant g "r" in
      let r_f = rename_sub_quant f "f" in
        Until(And(nnf_fast_ r_f, (n_nnf_fast r_g)), (And(n_nnf_fast f, n_nnf_fast g))  )  (** todo check reduction **)
    )
    | Release (f, g) -> Until (n_nnf_fast f, n_nnf_fast g)
    | Exists (id, f) -> Forall (id, n_nnf_fast f)
    | Forall (id, f) -> Exists (id, n_nnf_fast f)

let nnf_fast f = 
  let (exx,all) = getPVs f in
  pvlst :=  exx@all;
  nnf_fast_ f



let print_hyperCTL f =
  if !verbose then
    printf "HyperCTL formula: %s\n%!" (hyperctl_str f)


 (* reduce numbers of X in nnf *)
 let rec reduceNext f = 
  match f with
      Var(a,pv) -> Var(a,pv)
    | False -> False
    | True -> True
    | Not f -> Not (reduceNext f )
    | Next f -> Next (reduceNext f)
    | Finally f -> reduceNext (Until (True, f)) 
    | Globally f -> reduceNext (Release (False, f)) 
    | Impl (f, g) -> reduceNext (Or (Not f, g)) 
    | Equiv (f, g) -> let (f, g) = reduceNext f, reduceNext g in And ((Or (Not f, g)), (Or (Not g, f)))
    | And (f, g) -> And (reduceNext f, reduceNext g)
    | Or (f, g) -> Or (reduceNext f, reduceNext g)
    | Until (f, g) -> Until (reduceNext f , reduceNext g )
    | WeakUntil (f, g) -> let (f, g) = reduceNext f, reduceNext g in Release (g, Or (f, g))  (**todo: check reduction !!! **)
    | Release (f, g) -> Release (reduceNext f, reduceNext g)
    | Forall (id, f) -> Forall (id, reduceNext f)
    | Exists (id, f) -> Exists (id, reduceNext f)




(*
    The following formulas check if a given formula in nnf is in EA, where no existensital operator is in the scope of a universally one
    only nnf
*)
  let rec check_EA_structure f = 
    match f with 
      True | False | Var (_, _) -> true
    | Not f | Next f | Finally f | Globally f  | Exists (_ , f) -> check_EA_structure f
    | And (f, g) | Or (f, g) | Until (f, g) |  WeakUntil (f, g) | Release (f, g) | Impl(f, g) | Equiv(f, g) -> (check_EA_structure f)&&(check_EA_structure g) 
    | Forall (p , f) -> no_exists_quant f

  and  no_exists_quant f =
     match f with 
        True | False | Var (_, _) -> true
      | Not f | Next f | Finally f | Globally f  -> no_exists_quant f
      | And (f, g) | Or (f, g) | Until (f, g) | Impl(f, g) | Equiv(f, g) | WeakUntil (f, g) | Release (f, g) -> (no_exists_quant f)&&(no_exists_quant g) 
      | Forall (p , f) -> no_exists_quant f
      | Exists (_ , f) -> false



let rec getFormulaSize formula =
    match formula with 
    True | False | Var (_, _) -> 1
    | Not f -> getFormulaSize f
    | Next f | Finally f | Globally f  -> (getFormulaSize f) + 1 
    | And (f, g) | Or (f, g) | Until (f, g) |  WeakUntil (f, g) | Equiv (f, g) | Impl (f, g) | Release (f, g) -> (getFormulaSize f) + (getFormulaSize g) + 1 
    | Forall (_ , f) | Exists (_ , f) -> (getFormulaSize f) + 1 

  
let  getMaxUnrollingBound formula =
    let size =  getFormulaSize formula in
    let k_max =  2.0 ** (float_of_int size)  in
    let k = (int_of_float k_max) in
    let k_max_int = if  k == 0
                    then ( Printf.printf "INTMAX reached - %f:\n probably unrolling bound larger then intmax. (Unsatisfiability can not be checked, k_max set to size of formula " k_max; size )
                    else k in
    k_max_int



    (* call only on formulas in nnf (no equiv, weak untils ,....) *)
    (* returns the quantifier depth of a formulas, max number of quantifier in different entry points *)
    let rec getQuantDepth f = 
      let rec_ =  getQuantDepth in
      match f with
        True | False | Not _ |Var (_, _) -> 0
        | Or (f, g) | And (f, g) -> max (rec_ f) (rec_ g)
        | Release (f, g) | Until (f, g) ->  max (rec_ f) (rec_ g)
        | Next f | Globally f | Finally f ->  (rec_ f)
        | Forall (x, f) | Exists (x, f) -> 1 + ( _getQuantDepth f )

    and _getQuantDepth f = 
          let rec_ =  _getQuantDepth in
          match f with
            True | False | Not _ |Var (_, _) -> 0
          | Or (f, g) | And (f, g) -> max (rec_ f) (rec_ g)
          | Release (f, g) | Until (f, g) -> max (getQuantDepth f) (getQuantDepth g)
          | Next f | Globally f | Finally f -> getQuantDepth f
          | Forall (x, f) | Exists (x, f) ->  rec_ f
  

  