
open FormulaHyperCTL
open Printf
open FormulaBool
open Functions

open GraphFactory

open TvStep


(* Constants *)
let inv = "inv"
let verbose = ref false;

module PVMap = Map.Make(String)

let pvMap = (ref PVMap.empty );;

let init_PVmaps  = 
  pvMap :=  PVMap.empty;; 

  

let add_to_PVmap pv parent step =
  let ppv = if (( compare parent "***" )  == 0)
            then ""
            else  "_"^(String.concat "" (String.split_on_char (Char.chr(95)) parent ))  in
  let tv = pv^ppv^"_"^(string_of_int step) in
  let lst = (parent,step,pv) in      (* empty tuple vor ocaml type check *)
  pvMap := PVMap.add tv lst !pvMap;
  tv


(*  
List af atomic propositions
*)
let aps = (ref [""]) ;;

let impl a b =
  BImpl(a,b)

let equiv a b =
  BEquiv(a,b)

let var a tv step =
  BVar(a,tv,step)


(* set one ap equal in two steps of two traces *)
let equalOneAP a tv1 s1 tv2 s2 =
    (* a_tv1^s1 <=> a_tv2_s2*)
    let l = BVar(a,tv1,s1) in
    let r = BVar(a,tv2,s2) in
    BEquiv(l,r)

(* set all aps equal in two steps of two traces *)
let equal tv1 s1 tv2 s2 =
    let equalAP a = equalOneAP a tv1 s1 tv2 s2 in
    let equal_list = List.map (equalAP ) !aps in
    BAndList(equal_list)

(* set ine ap on one trace equal, used in invariant building *)
let equalOneTraceOneAp tv l k a =
    equalOneAP a tv l tv k

let equalOneTrace tv l k =
  let equalAP a = equalOneTraceOneAp tv l k a in
  let equal_list = List.map (equalAP ) !aps in
  BAndList(equal_list)


(* At Least One Loop *)
let invariantAllOr tv k =
  (* create invariants INV(1)_tv to INV(k-1)_tv *)
  let invlist =  List.init (k-1) (fun i -> BVar(inv,tv,i+1) ) in
  BOrList(invlist)

(* create invariants which implies ap^l = ap^k *)
let invariantImp tv l k =  
    let l_imp = var inv tv l in
    let r_imp = equalOneTrace tv l k in
    impl l_imp r_imp

let invariantAllImp tv k =
  (* i+1 to k-1 because we 1,....,k-1 **)
    let invlist =  List.init (k-1) (fun i -> invariantImp tv (i+1) k ) in
    BAndList(invlist)


let atLeastOneLoop tv k =
  BAnd(( invariantAllImp tv k), (invariantAllOr tv k))


(* At most one loop *)
let smallerInvEx tv l =
  if l = 1
    then BFalse
    else  invariantAllOr tv l

let invariantImpSmaller tv l =
      let l_imp = smallerInvEx tv l in
      let r_imp = BNeg ( (var inv tv l) ) in
      impl l_imp r_imp


let atMostOneLoop tv k = 
    let invlist =  List.init (k-1) (fun i -> invariantImpSmaller tv (i+1) ) in
    BAndList(invlist)

(* ensure trace consist of exactly one loop *)
let loop  tv k =
  BVar("loop",tv,k)

 
let loopForm tv k =
  BAnd((atMostOneLoop tv k),(atLeastOneLoop tv k))

let loopAdd tv k lst lst_loops =
  let var = BVar("loop",tv,k) in
  let tvloop = loopForm tv k in
  let eq = equiv var tvloop in
  lst := eq::(!lst) ;
  lst_loops := var::(!lst_loops)
  

 let loopAll k =
   (* sprintf "PVMAP:\n";
    PVMap.iter (fun tv tuple -> (  let parent, step, pv = tuple in
                                    sprintf "(%s->[%s, %d, %s])" tv parent step pv) ;)   !pvMap; *)
    let lst = ref [] in
    let lst_loops = ref [] in
    PVMap.iter (fun tv tuple -> (   let parent, step, pv = tuple in
                                    loopAdd tv k lst lst_loops) )   !pvMap ;
    
    BAndList( (!lst)@(!lst_loops) )


    


(**
  anchors newTV on parentTV at step 
    -> special case for first anchor
*)
let anchor parentTV parentStep newTV step =
  if( parentTV <> "***") (* already initialized *)
  then  equal parentTV parentStep newTV step
  else BTrue


(*
functions wich update the loop invariants, if k is reached
*)
let isInfTempOp f = 
  match f with 
    |  Globally _ | Finally _ | Release (_,_) | Until (_,_) -> true
    | _ -> false

let getOverOrUnderApprox f =
  (* sprintf "Get OverUnderApprox for:" ; print_hyperCTL f; *)
  match f with 
      Globally _ -> True
    | Finally _ -> False
    | Release (_,_) -> True
    | Until (_,_) -> False
    | _ -> raise Not_found

  (* depriciated *)
let checkForTermination tvset f k =
  assert(false);
  let parent, step = tvset#getParentTuple in
  let complete = tvset#isRun parent in
  (****
  printf "Check for termination:%s %d<%d" parent step k ;
  print_hyperCTL f;
  ***)
  if ( isInfTempOp f && step == k )
  then
  (
    if (complete) 
    then(
      (getOverOrUnderApprox f), true, tvset
      )
    else
    (
      (* set termination indicator
      tvset#setRunTrue parent; *)
      f,false, tvset
    )
  )
  else
  (
    f,false, tvset
  )



  (* reset existing steps *)
  let resetAllLoops tvset  =
        let num_k = tvset#resetStepsToLoop in
        tvset, num_k
 

(***************************************)
(*** Set Loop Inv and call unrolling ***)
(***************************************)
let rec unroll_ f k tvset loop step  = 

    setLoopInvariants tvset f k loop step

and setLoopInvariants tvset f k loop step =
(* reset all loops and returns the trace newly reach bound *)
  let tvset, num_k = resetAllLoops tvset in
  if (List.length num_k) > 0
  then (introduceLoopInv tvset f k loop step num_k ) (* returns formula **)
  else (unroll__ f k tvset loop step)

  (* return f, if no invariant is reached and unroll further  *)

and introduceLoopInv tvset f k loop step num_k  =

  match num_k with
    | [] -> unroll__ f k tvset loop step
    | hd::tl -> buildInvOr tvset f k loop step hd tl 
    
and buildInvOr tvset f k loop step hd tl =
    (* List init 1 -- k-1 *)
    let inAndlst =  List.init (k-1) (fun i -> buildInvOne tvset f k loop step hd (i+1) tl ) in
    BAndList(inAndlst)
 
and buildInvOne tvset f k  loop step  tv i num_k =
    let tvset_f = Oo.copy (tvset) in
    let invVar = BVar(inv,tv,i) in
    tvset_f#setBoundAndStep tv i;
    let inv_unroll  = introduceLoopInv tvset_f f k loop step num_k in
    impl invVar inv_unroll


(**********************************)
(*********UNROLLING***RULES********)
(**********************************)
and unroll__ f k tvset loop step = 
    match f with
        True              -> BTrue
      | False             -> BFalse
      | Var (x, y)        -> unroll_var x y tvset
      | And (f, g)        -> unroll_and f g k tvset
      | Or (f, g)         -> unroll_or f g k tvset
      | Until (f, g)      -> unroll_until f g k tvset loop step
      | Release (f, g)    -> unroll_release f g k tvset loop step
      | Not f             -> unroll_not f k tvset
      | Next f            -> unroll_next f k tvset
      | Finally f         -> unroll_finally f k tvset loop step
      | Globally f        -> unroll_globally f k tvset loop step
      | Exists (pv, f)    -> unroll_exists pv f k tvset
      | Forall (pv, f)    -> unroll_forall pv f  k tvset
      | _                 -> raise (Error " hyperctl* ops not found, should not happen")


and unroll_var a tv tvset =
          (* todo assert step and tv *)
          let step = tvset#getStep tv in
          BVar(a,tv,step);
and unroll_and f g k tvset = 
          let tvset_r = Oo.copy (tvset) in
          let tvset_l = Oo.copy (tvset) in

          let le = unroll_ f k tvset_l false 0 in
          let ri = unroll_ g k tvset_r false 0 in
          BAnd(le,ri)

and unroll_or f g k tvset   = 
          let tvset_r = Oo.copy (tvset) in
          let tvset_l = Oo.copy (tvset) in

          let le = unroll_ f k tvset_l false 0 in
          let ri = unroll_ g k tvset_r false 0 in
          BOr(le,ri)
and unroll_not f k tvset    = 
          BNeg( unroll_ f k tvset false 0 )


and unroll_next f k tvset   = 
          tvset#addStepsAll 1;
          unroll_ f k tvset false 0



and unroll_finally f k tvset  loop step = 
          (* Finally current step*)
          let tvset_f = Oo.copy (tvset) in
          let cur = unroll_ f k tvset_f false 0 in
          (* Finally next step*)
          let tvset_next = Oo.copy (tvset) in
          tvset_next#addStepsAll 1;
          let nextFinally= Finally(f) in

          let next = 
            if( loop )
            then (
              if step < tvset_next#get_lcm 
              then  unroll_ nextFinally k tvset_next true (step +  1)
              else BFalse
            )
            else (
              if( tvset_next#allOnLoop ) (* lcm loop start *)
              then unroll_ nextFinally k tvset_next true 0
              else unroll_ nextFinally k tvset_next false 0
            )
            in
  
            BOr(cur,next)


and unroll_globally f k tvset loop step =
          let tvset_f = Oo.copy (tvset) in
          let tvset_next = Oo.copy (tvset) in
          let cur = unroll_ f k tvset_f false 0 in
          
          (* Globally next step*)
          tvset_next#addStepsAll 1;
          let nextGlobally = Globally(f) in     

          let next = 
          if( loop )
          then (
            if step < tvset_next#get_lcm 
            then  unroll_ nextGlobally k tvset_next true (step +  1)
            else BTrue
          )
          else (
            if( tvset_next#allOnLoop ) (* lcm loop start *)
            then unroll_ nextGlobally k tvset_next true 0
            else unroll_ nextGlobally k tvset_next false 0
          )
          in

          BAnd(cur,next)


(* Until Operator *)          
and unroll_until f g k tvset loop step = 
          let tvset_f = Oo.copy (tvset) in
          let left_f =  unroll_ f k tvset_f false 0 in
          let tvset_g = Oo.copy (tvset) in
          let right_g = unroll_ g k tvset_g false 0 in
          
          (* next until step  *)
          let tvset_next = Oo.copy (tvset) in
          tvset_next#addStepsAll 1;
          let nextUntil = Until(f,g) in

          let next = 
            if( loop )
            then (
              if step < tvset_next#get_lcm 
              then  unroll_ nextUntil k tvset_next true (step +  1)
              else BFalse
            )
            else (
              if( tvset_next#allOnLoop ) (* lcm loop start *)
              then unroll_ nextUntil k tvset_next true 0
              else unroll_ nextUntil k tvset_next false 0
            )
            in

          BOr(right_g,(BAnd(left_f,next))) 


and unroll_release f g k tvset loop step = 
        (* unroll step to k-1 *)
        let tvset_f = Oo.copy (tvset) in
        let left_f =  unroll_ f k tvset_f false 0 in
        let tvset_g = Oo.copy (tvset) in
        let right_g = unroll_ g k tvset_g false 0 in
        (* next release step *)
        let tvset_next = Oo.copy (tvset) in
        tvset_next#addStepsAll 1;
        let nextRelease = Release(f,g) in
          
        let next = 
          if( loop )
          then (
            if step < tvset_next#get_lcm 
            then  unroll_ nextRelease k tvset_next true (step +  1)
            else BTrue
          )
          else (
            if( tvset_next#allOnLoop ) (* lcm loop start *)
            then unroll_ nextRelease k tvset_next true 0
            else unroll_ nextRelease k tvset_next false 0
          )
        in

        BAnd(right_g,(BOr(left_f,next))) 


and unroll_exists pv f k tvset   =
          let parent, parentStep  = tvset#getParentTuple in
          let tv = add_to_PVmap pv parent parentStep  in
          tvset#addParent tv;
          let anchr = (anchor parent parentStep tv 0) in
          let lps = loop tv k in
          let f_r = replacePVbyTV pv tv f in
          let unr = unroll_ f_r k tvset false 0 in
          let lst = [anchr;lps;unr] in
          BAndList(lst)


and unroll_forall pv f k tvset   = 
          assert(false);
          BFalse

let printPVMap () = 
    PVMap.iter (fun tv tuple -> (  let parent, step, pv = tuple in
                                    printf "(%s->[%s, %d, %s])" tv parent step pv) ;)   !pvMap


let init () =
  pvMap :=  PVMap.empty


let rec get_PVMap_real_parent parent step =
  if ((step == 0) && (PVMap.mem parent !pvMap))
  then (
    let par_parent, par_step, pv = PVMap.find parent !pvMap in
    if( (compare par_parent "***") == 0 ) 
    then parent, step 
    else get_PVMap_real_parent par_parent par_step
  )else(
    parent, step
  )
  


let add_PVTupleToLst tv tuple lst =
  let parent, step, pv = tuple in
  (* check recursive parent *)
  let np, ns = get_PVMap_real_parent parent step in
  lst := ((tv,np,ns))::(!lst)


let pvmap_to_lst () = 
  let lst = ref [] in
  PVMap.iter (fun tv tuple -> (add_PVTupleToLst tv tuple lst)  )   !pvMap;
  !lst             


let unroll f k ap =
  init();
  (* check for empty formula, without aps -> add dummy ap **)
  let ap_notempty = 
    if (List.length ap ) == 0
    then ["dummy"]
    else ap
    in
    
  aps := ap_notempty;
  
  let tvset = new tvset !k in

  let unrollFormula = unroll__ f !k tvset false 0 in 
  let loopFormula = loopAll !k in
  (* lst of boolean formulas,  unrolled :: loop conditions :: true :: false *)
  let formula_lst = [unrollFormula;loopFormula; BTrue; BEquiv(BNeg(BTrue),BFalse)] in 
  let boolFormula = BAndList( formula_lst ) in
  let bool_form_str = limbool_str boolFormula in
  if !verbose then
  Printf.printf "Resulting Bool formula: \n %s \n" bool_form_str;
  bool_form_str, pvmap_to_lst()


