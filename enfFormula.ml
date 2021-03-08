open Printf
open FormulaHyperCTL
open Functions

(******************************
This module checks if a given HyperCTL* formula is in exist-forall normal form, 
thus no universally quantfied path variables scopes direct or indirect over an
existentially quantfied one.

For Formulas in enf, constructs an equisatifiable E*HyperCTL* formula.

Note that we consider HyperCTLs formulas, where the next operator is as outermost as possible,
and not directly under temporal operator.

***********************)

type map_hyperctl_formula =
  MTrue
| MFalse
| MVar of int * string * string
| MNot of int * map_hyperctl_formula
| MOr of int * map_hyperctl_formula * map_hyperctl_formula
| MAnd of int * map_hyperctl_formula * map_hyperctl_formula
| MImpl of int * map_hyperctl_formula * map_hyperctl_formula
| MEquiv of int * map_hyperctl_formula * map_hyperctl_formula
| MNext of int * map_hyperctl_formula
| MUntil of int * map_hyperctl_formula * map_hyperctl_formula
| MWeakUntil of int * map_hyperctl_formula * map_hyperctl_formula
| MRelease of int * map_hyperctl_formula * map_hyperctl_formula
| MFinally of int * map_hyperctl_formula
| MGlobally of int * map_hyperctl_formula
| MExists of int * string * map_hyperctl_formula
| MForall of int * string * map_hyperctl_formula
| MMap of int * string * map_hyperctl_formula
| MPathEqual of string * string


let rec map_hyperctl_formula_str_ buf f =
  let abuf = Buffer.add_string buf in
  let ibuf id = Buffer.add_string buf ("["^(string_of_int id)^"] ") in
  let rec_ = map_hyperctl_formula_str_ buf in
    match f with
        MTrue -> abuf "True"
      | MFalse -> abuf "False"
      | MVar (id,a, x) -> abuf a; abuf "_"; abuf x; ibuf id
      | MNot (id,f) -> abuf "(~ ";ibuf id; rec_ f; abuf ")"
      | MOr (id,f, g) -> abuf "(";ibuf id; rec_ f; abuf " | "; rec_ g; abuf ")"
      | MAnd (id,f, g) -> abuf "(";ibuf id; rec_ f; abuf " & "; rec_ g; abuf ")"
      | MImpl (id,f, g) -> abuf "(";ibuf id; rec_ f; abuf " -> "; rec_ g; abuf ")"
      | MEquiv (id,f, g) -> abuf "(";ibuf id; rec_ f; abuf " <-> "; rec_ g; abuf ")"
      | MNext (id,f) -> abuf "(X ";ibuf id; rec_ f; abuf ")"
      | MUntil (id,f, g) -> abuf "(";ibuf id; rec_ f; abuf " U "; rec_ g; abuf ")"
      | MWeakUntil (id,f, g) -> abuf "(";ibuf id; rec_ f; abuf " W "; rec_ g; abuf ")"
      | MRelease (id,f, g) -> abuf "(";ibuf id; rec_ f; abuf " R "; rec_ g; abuf ")"
      | MFinally (id,f) -> abuf "(F ";ibuf id; rec_ f; abuf ")"
      | MGlobally (id,f) -> abuf "(G ";ibuf id; rec_ f; abuf ")"
      | MExists (id,v, f) -> abuf "exists ";ibuf id; abuf v; abuf ".("; rec_ f; abuf ")"
      | MForall (id,v, f) -> abuf "forall ";ibuf id; abuf v; abuf ".("; rec_ f; abuf ")"
      | MMap (id,v, f) -> abuf "MAP(";ibuf id; abuf v; abuf ".("; rec_ f; abuf ")"
      | MPathEqual (pv1,pv2) ->  abuf "PEqual("; abuf pv1; abuf "="; abuf pv2; abuf ")"

let map_hyperctl_formula_str f =
  let buf = Buffer.create 0 in
  map_hyperctl_formula_str_ buf f; let str = Buffer.contents buf in Buffer.reset buf; str

let print_MaphyperCTL f =
  if false then
  printf "Map formula: %s\n%!" (map_hyperctl_formula_str f)





type enf_hyperctl_formula =
  End
| QuantCon of int * string * enf_hyperctl_formula list
| ExistsPV of string * enf_hyperctl_formula
| ForallPV of string * enf_hyperctl_formula
| TempOps  of string * enf_hyperctl_formula

  (* hyperCTL_str: print HyperCTL formula *)
  let rec enf_str_ buf f =
    let abuf = Buffer.add_string buf in
    let rec_ = enf_str_ buf in
    let lst_ lst = abuf " ";List.iter (fun f-> abuf "{";rec_ f;abuf "}"; )  lst;abuf " " in
      match f with
        | QuantCon (id,pv, lst) -> abuf ("QV(["^(string_of_int id)^"] ");abuf pv;abuf ")["; lst_ lst; abuf "]VQ\n"
        | ExistsPV (pv,f) -> abuf "E "; abuf pv; abuf ".("; rec_ f ;abuf ")"
        | ForallPV (pv,f) -> abuf "A " ; abuf pv; abuf ".("; rec_ f ;abuf ")"
        | TempOps (str,f)  ->  abuf str;abuf "( "; rec_ f ;abuf ")"
        | End -> abuf "_"
  
  let enf_str f =
    let buf = Buffer.create 0 in
    enf_str_ buf f; let str = Buffer.contents buf in Buffer.reset buf; str
  
  let print_enf f =
    let str = enf_str f in
    printf "%s" str


  (* first translate to NNF *)
  let rec enf_transform_ f qv = 
    match f with
          MTrue -> End
        | MFalse -> End
        | MVar (_,_, _) -> End
        | MNot (id,f) -> enf_transform_ f qv
        | MOr (id,f, g)   | MAnd (id,f, g)  ->  QuantCon(id, qv , ((enf_transform_list f g qv) ))
        | MNext (id,f) -> TempOps( "->" , enf_transform_ f qv )
        | MFinally (id,f) | MGlobally (id,f) ->   QuantCon(id, qv, ( ((TempOps( "->" , enf_transform_ f qv ))::(enf_transform_list_ f qv ) )))
        | MUntil (id,f, g) | MWeakUntil (id,f, g) | MRelease (id,f, g) ->   QuantCon(id, "*", (((TempOps( "->" , enf_transform_ f qv ))::(TempOps( "->" , enf_transform_ g qv ))::(enf_transform_list f g qv ))) )
        | MExists (id,pv, g) ->  QuantCon(id,qv, (ExistsPV(pv, End  )::(enf_transform_list_ g pv))  )
        | MForall (id,pv, g) ->  QuantCon(id,qv, (ForallPV(pv, End )::(enf_transform_list_ g pv)) )
        | MMap (id,pv, g)    ->  QuantCon(id,qv, (ExistsPV(pv, End  )::(enf_transform_list_ g pv))  )
        | MPathEqual (pv1,pv2) -> End (* only under and op *) 
        | _ -> (print_MaphyperCTL f; raise (Error "enf_tranform_ not match:"))


  and enf_transform_list_  f qv = 
      match f with
          | MOr (id,f, g)   | MAnd (id,f, g) -> (enf_transform_list_ f qv)@(enf_transform_list_ g  qv)
          | MExists (id,pv, f)  ->  [ ExistsPV(pv,  End )]@(enf_transform_list_ f pv )
          | MForall (id,pv, f)  ->  [ ForallPV(pv, End )]@(enf_transform_list_ f pv )
          | MMap (id,pv, g)     ->  [ ExistsPV(pv,  End )]@(enf_transform_list_ g pv )
          | MFinally (id,f) | MGlobally (id,f) -> ((TempOps( "->" , enf_transform_ f qv ))::(enf_transform_list_ f qv) )
          | MUntil (id,f, g) | MWeakUntil (id,f, g) | MRelease (id,f, g) ->  ((TempOps( "->" , enf_transform_ f qv ))::(TempOps( "->" , enf_transform_ g qv ))::(enf_transform_list f g qv ))
          | _ -> [ enf_transform_ f qv ]

  and enf_transform_list f g qv  = 
        let lst_f = enf_transform_list_  f qv in
        let lst_g = enf_transform_list_  g qv in
        let lst = lst_f@lst_g in
        lst


  let  enf_transform f = 
    try 
      enf_transform_ f "*"
      with Not_found ->  (printf "Not found error in enf_transform" ; End )

(* get all APs from formula *)
let rec getMapAPs_ f = 
  match f with 
    MTrue | MFalse  | MPathEqual (_,_)  -> []
  | MVar (_,x, _) -> [x]
  | MNot (id,f) | MNext (id,f) | MFinally (id,f) | MGlobally (id,f) | MExists (id,_, f) | MForall (id,_, f) -> getMapAPs_ f 
  | MAnd (id,f, g) | MImpl (id,f, g) | MEquiv (id,f, g) | MOr (id,f, g) | MUntil (id,f, g) | MWeakUntil (id,f, g) | MRelease (id,f, g) ->  getMapAPs_ f @ getMapAPs_ g
  | _ -> raise (Error "getMapAPs_ not found " )    

let getMapAPs f = 
  let aps = foldr_rem_dupl ( getAPs_ f ) in 
  (* print_list aps ; *)
  aps


let rec getPVs_ f exx all =
match f with 
  MTrue | MFalse | MVar (_,_, _) | MPathEqual (_,_) -> exx , all
| MExists (id,p , f) -> getPVs_ f (p::exx) all
| MForall (id,p , f) -> getPVs_ f exx (p::all) 
| MNot (id,f) | MNext (id,f) | MFinally (id,f) | MGlobally (id,f)  -> getPVs_ f exx all 
| MAnd (id,f, g) | MImpl (id,f, g) | MEquiv (id,f, g) | MOr (id,f, g) | MUntil (id,f, g) | MWeakUntil (id,f, g) | MRelease (id,f, g) -> getPVs__ f g exx all 
| MMap(id,pv, f) -> getPVs_ f exx all 


and getPVs__ f g exx all = 
  let (exf,alf) =  getPVs_ f [] [] in 
  let (exg,alg) =  getPVs_ g  [] [] in
  (exx@exf@exg, all@alf@alg)

  (************************************)
  (***   Check for indirect scope   ***)
  (************************************)
      

  let is_forall  elm =
    match elm with
       ForallPV(pv, succ)  -> true
       | _ -> false

  let is_tempOps elm = 
    match elm with
        TempOps(pv, succ)  -> true
       | _ -> false  
       
  let is_exists  elm =
        match elm with
            ExistsPV(pv, succ)  -> true
           | _ -> false    
  


  let rec exists_in_enf enf =
    match enf with
      QuantCon (id,s,lst)    -> exists_in_lst lst
    | TempOps(_,f)    -> exists_in_enf f
    | ExistsPV(_,_)   -> true
    | ForallPV(_,f)   -> exists_in_enf f
    | End             -> false
    | _ -> raise (Error "struct not found in exists_in_enf" )    

  and exists_in_lst lst  =
    (List.exists (fun elm -> exists_in_enf elm ) lst)


  let rec get_successor lst =
    (List.filter (fun elm -> is_tempOps elm) lst)
    

  let check_forall_indirect lst = 
    let succ   = get_successor lst in 
    if exists_in_lst succ 
    then (printf "indirect Scope detected\n"; false)
    else true


  let list_contains_forall lst =
    List.exists (fun elm -> is_forall elm) lst 

  let get_forall lst = 
      (List.filter (fun elm -> is_forall elm) lst)
    
   

(********)
  let rec check_enf_ enf =
    match enf with
        QuantCon(id, s,lst )   -> check_for_forall_quant lst
      | ForallPV(pv, succ)  -> check_forall_indirect ([succ])
      | ExistsPV(pv, succ)  -> check_enf_ succ
      | TempOps(pv, succ)   -> check_enf_ succ
      | End -> true
  
  and check_enf_lst lst =
    List.exists (fun elm -> check_enf_ elm) lst

  and check_for_forall_quant lst =
    if list_contains_forall lst
    then (check_forall_indirect lst)
    else check_enf_lst lst
(********)


(* check if a forall quantfier exists for the given pv*)
  let check_equal elm fpv =
    match elm with 
      QuantCon( _,_,_ ) | ExistsPV(_,_) | TempOps(_,_) | End -> false
    | ForallPV(pv, _)  -> (pv == fpv)
   

  let pv_is_in_lst lst fpv =
    List.exists (fun elm -> check_equal elm fpv ) lst

  

  let rec get_exists_pvs_lst enf_lst =
    List.concat ( List.map (fun elm -> get_exists_pvs elm ) enf_lst)


  and get_exists_pvs enf =
        match enf with 
            QuantCon(id,s,lst) -> get_exists_pvs_lst lst
          | ForallPV(_,_)   -> []
          | ExistsPV(pv, _)  -> [pv]
          | TempOps(_, succ)   -> get_exists_pvs succ
          | End -> []



  let rec get_pv_set_ enf fpv =
      match enf with 
         QuantCon(id,s,lst) -> (
                      if pv_is_in_lst  lst fpv
                      then (get_exists_pvs_lst (ExistsPV(s,End)::lst); assert(false) )
                      else get_pv_set_lst lst fpv
                  )
        | ForallPV(pv,succ) | ExistsPV(pv, succ)  -> []
        | TempOps(pv, succ)   -> get_pv_set_ succ fpv
        | End -> []

  and get_pv_set_lst lst fpv =
    List.concat ( List.map (fun elm -> get_pv_set_ elm fpv) lst)


(******************************)
let replaceVarPVbyPv_  pv tv x y id=
  if pv <> y 
  then (MVar(id,x,y))
  else (MVar(id,x,tv))


(* replace path variabpe pv by trace variable tv in formula f *)
let rec replacePVbyPV pv tv f =
  match f with
      MTrue -> MTrue
    | MFalse -> MFalse
    | MVar (id,x, y) -> replaceVarPVbyPv_ pv tv x y id
    | MAnd (id,f, g) -> MAnd (id,replacePVbyPV pv tv f, replacePVbyPV pv tv g)
    | MOr (id,f, g) -> MOr (id,replacePVbyPV pv tv f, replacePVbyPV pv tv g)
    | MImpl (id,f, g) -> MImpl (id,replacePVbyPV pv tv f, replacePVbyPV pv tv g)
    | MEquiv (id,f, g) -> MEquiv (id,replacePVbyPV pv tv f, replacePVbyPV pv tv g)
    | MUntil (id,f, g) -> MUntil (id,replacePVbyPV pv tv f, replacePVbyPV pv tv g)
    | MWeakUntil (id,f, g) -> MWeakUntil (id,replacePVbyPV pv tv f, replacePVbyPV pv tv g)
    | MRelease (id,f, g) -> MRelease (id,replacePVbyPV pv tv f, replacePVbyPV pv tv g)
    | MNot (id,f) -> MNot (id,replacePVbyPV pv tv f)
    | MNext (id,f) -> MNext (id,replacePVbyPV pv tv f)
    | MFinally (id,f) -> MFinally (id,replacePVbyPV pv tv f)
    | MGlobally (id,f) -> MGlobally (id,replacePVbyPV pv tv f)
    | MExists (id,x, f) -> MExists (id,x, replacePVbyPV pv tv f)
    | MForall (id,x, f) -> MForall (id,x, replacePVbyPV pv tv f)
    | MPathEqual (pv1,pv2) -> MPathEqual (pv1,pv2)
    | _ -> raise (Error "replacePVbyPV not found " )    


  module PV_lst    = Map.Make(String)
  
  let get_pv_set  enf pv lst = 
    let epv_lst = get_pv_set_ enf pv in

    let lst_ = PV_lst.add pv epv_lst !lst in
    lst := lst_


  let pv_lsts enf all =
    let lst = (ref PV_lst.empty) in
    List.iter (fun pv -> get_pv_set enf pv lst) all;
    lst
  


  let get_fpv_pvlst fpv f =
    let enf =  enf_transform f in
    let pvlst = get_pv_set_ enf fpv in
    let lst = foldr_rem_dupl_star pvlst in
    lst

    (****************************************************************)
    (****************************************************************)

  
  let rec get_exists_pvs_lst_noRec enf_lst =
    List.concat ( List.map (fun elm -> get_exists_pvs_noRec elm ) enf_lst)

  and get_exists_pvs_noRec enf =
        match enf with 
            QuantCon(id,s,lst) -> []
          | ForallPV(_,_)   -> []
          | ExistsPV(pv, _)  -> [pv]
          | TempOps(_, succ)   -> []
          | End -> []
          | _ -> raise (Error "error get_exists_pvs_noRec")



  (* return the id and the path variable list for a universal quantified path variable *)
  let rec get_pv_set_id_ fpv enf =
      match enf with 
         QuantCon(id,s,lst) -> (
                      if pv_is_in_lst  lst fpv
                      then (   
                              (id, (s :: (get_exists_pvs_lst_noRec lst)) ) 
                          )
                      else (  get_pv_set_lst_id lst fpv )
                  )
        | ForallPV(pv,succ) | ExistsPV(pv, succ)  -> (-1, [])
        | TempOps(pv, succ)   -> get_pv_set_id_  fpv succ
        | End -> (-1, [])
        | _ -> raise (Error "dsmfklsdfkd");

  and get_pv_set_lst_id lst fpv =
    let pairlst = List.map (fun elm ->  get_pv_set_id_  fpv elm) lst in
    (* catch case where the path variable is not in the subtree *)
    try
      List.find (fun elm -> let id,l = elm in id >= 0; ) pairlst;
    with  Not_found -> ( (-1, [])  )

    

  
    let get_fpv_pvlst_id_ fpv e_f =
      let id, pvlst = get_pv_set_id_  fpv e_f in
      let parent = List.hd pvlst in
      let childs = List.tl pvlst in
      let lst = foldr_rem_dupl_star childs in
      (id,parent,lst)

    (****************************************************************)
    (****************************************************************)



  let rec containForall f =
    match f with 
        MTrue | MFalse | MVar (_,_, _) | MPathEqual (_,_) -> false
      | MForall (_,_, _) -> true
      | MNot (id,f) | MNext (id,f) | MFinally (id,f) | MGlobally (id,f) | MMap (id,_, f) | MExists (id,_, f) -> containForall f 
      | MAnd (id,f, g) | MImpl (id,f, g) | MEquiv (id,f, g) | MOr (id,f, g) | MUntil (id,f, g) | MWeakUntil (id,f, g) | MRelease (id,f, g) ->  containForall f  || containForall g

  let rec getForallQuant_ f =
    match f with 
    MTrue | MFalse | MVar (_,_, _) | MPathEqual (_,_) -> []
  | MForall (id,pv , _) -> [pv] 
  | MNot (id,f) | MNext (id,f) | MFinally (id,f) | MGlobally (id,f) | MMap(id,_,f) | MExists (id,_, f) | MMap (id,_,f) -> getForallQuant_ f 
  | MAnd (id,f, g) | MImpl (id,f, g) | MEquiv (id,f, g) | MOr (id,f, g) | MUntil (id,f, g) | MWeakUntil (id,f, g) | MRelease (id,f, g) ->  getForallQuant_ f  @ getForallQuant_ g


  let getForallQuant f = 
    let pvlst = getForallQuant_ f in
    match pvlst with
        [] -> raise (Error "should not happen: call getForallQaunt only afte containForall")
      | hd::tl -> hd


  
      let replace_forall_exists_ fpv epv x y id =
        if fpv <> y 
        then MVar(id, x,y)
        else MVar(id,x,epv)
      
      
      let rec replace_forall_exists fpv epv f i =
        let rec_ f = replace_forall_exists fpv epv f i in
        match f with
            MTrue -> MTrue
          | MFalse -> MFalse
          | MVar (id,x, y) -> replace_forall_exists_ fpv epv x y id
          | MAnd (id,f, g) -> MAnd (id, rec_ f ,  rec_ g)
          | MOr (id,f, g) -> MOr (id, rec_ f ,  rec_ g)
          | MImpl (id,f, g) -> MImpl (id, rec_ f ,  rec_ g)
          | MEquiv (id,f, g) -> MEquiv (id, rec_ f ,  rec_ g)
          | MUntil (id,f, g) -> MUntil (id, rec_ f ,  rec_ g)
          | MWeakUntil (id,f, g) -> MWeakUntil (id, rec_ f ,  rec_ g)
          | MRelease (id,f, g) -> MRelease (id, rec_ f ,  rec_ g)
          | MNot (id,f) -> MNot (id, rec_ f )
          | MNext (id,f) -> MNext (id, rec_ f )
          | MFinally (id,f) -> MFinally (id, rec_ f )
          | MGlobally (id,f) -> MGlobally (id, rec_ f )
          | MExists (id,x, f) -> MExists (id,x,  rec_ f )
          | MMap (id,x,f) ->   raise (Error "Should not happen ")  (* TODO: MMap (x, rec_ f ); *)
          | MPathEqual (pv1,pv2) -> MPathEqual (pv1,pv2)
          | MForall (id,x, f) -> (
                          let fpv_next = x^(string_of_int i) in
                          let f_next = replacePVbyPV x fpv_next f in
                          MForall (id,fpv_next, rec_ f_next)
                          )

                  

(** enumerate the forall exists interaction for path variable pv with list pvlust in f **)
  let rec enumerate_forall_exists_ fpv pvlst f i =
    if (List.length pvlst) == 1 then  
    (
      let hd = List.hd pvlst in
      MMap(0, hd ,replace_forall_exists fpv hd f i )
    )else(
      match pvlst with
          [] -> MTrue
        | hd::tl -> MAnd(0, MMap(0, hd ,replace_forall_exists fpv hd f i), enumerate_forall_exists_ fpv tl f (i+1))
    )

  let enumerate_forall_exists fpv pvlst f =
      enumerate_forall_exists_ fpv pvlst f 0


  let comparePV pv1 pv2 =
      (compare pv1 pv2) == 0


  (* only call if at least one quant is in set  *)
  let rec unroll_fpv_pvlst fpv pvlst f =
      let rec_ f = unroll_fpv_pvlst fpv pvlst f in
        match f with 
        MTrue              ->  MTrue
      | MFalse             -> MFalse
      | MPathEqual (pv1,pv2) -> MPathEqual (pv1,pv2)
      | MVar (id,x, y)        -> MVar (id,x, y) 
      | MForall (id,pv , g)  -> ( (* unroll fpv operator *)
                              if comparePV pv fpv
                              then enumerate_forall_exists fpv pvlst g 
                              else ( MForall (id,pv ,  rec_ g) )
                              )
      | MNot  (id,g)             -> MNot (id, rec_ g)
      | MNext (id,g)            -> MNext(id, rec_ g)
      | MFinally (id,g)         -> MFinally(id, rec_ g)
      | MGlobally (id,g)        -> MGlobally(id, rec_ g)
      | MExists (id,pv, g)    -> MExists (id,pv, rec_ g)
      | MMap (id,pv, g)       -> MMap (id,pv, rec_ g)
      | MAnd (id,h, g)        -> MAnd(id, rec_ h, rec_ g)
      | MImpl (id,h, g)       -> MImpl(id, rec_ h, rec_ g)
      | MEquiv (id,h, g)      -> MEquiv(id, rec_ h, rec_ g)
      | MOr (id,h, g)         -> MOr(id, rec_ h, rec_ g)
      | MUntil (id,h, g)      -> MUntil(id, rec_ h, rec_ g)
      | MWeakUntil (id,h, g)  -> MWeakUntil(id, rec_ h, rec_ g)
      | MRelease (id,h, g)    -> MRelease(id, rec_ h, rec_ g)

  
  let equalAPs pv1 pv2 a = 
    let form = nnf_fast ( Or( And(Var(a,pv1),Var(a,pv2)) , And(Not(Var(a,pv1)),Not(Var(a,pv2)) )) ) in
    form

  let buildMPathEqual pv1 pv2 ap =
    let equiv = List.fold_left (fun form a -> And(equalAPs pv1 pv2 a ,form) ) True ap in
    Globally(equiv)


  let rec map_transBack f ap =
    match f with
        MTrue -> True
      | MFalse -> False
      | MVar (id,x, y) -> Var(x,y)
      | MAnd (id,f, g) -> And (map_transBack f ap, map_transBack  g ap)
      | MOr (id,f, g) -> Or (map_transBack f ap, map_transBack  g ap)
      | MImpl (id,f, g) -> Impl (map_transBack f ap, map_transBack  g ap)
      | MEquiv (id,f, g) -> Equiv (map_transBack f ap, map_transBack  g ap)
      | MUntil (id,f, g) -> Until (map_transBack f ap, map_transBack  g ap)
      | MWeakUntil (id,f, g) -> WeakUntil (map_transBack f ap, map_transBack  g ap)
      | MRelease (id,f, g) -> Release (map_transBack f ap, map_transBack  g ap)
      | MNot (id,f) -> Not (map_transBack f ap)
      | MNext (id,f) -> Next (map_transBack f ap)
      | MFinally (id,f) -> Finally (map_transBack f ap)
      | MGlobally (id,f) -> Globally (map_transBack f ap)
      | MExists (id,x, f) -> Exists (x,(map_transBack f ap))
      | MForall (id,x, f) -> Forall (x, (map_transBack f ap))
      | MMap (id,x, f) -> map_transBack f ap
      | MPathEqual (pv1,pv2) -> buildMPathEqual pv1 pv2 ap


  let id = ref 0 ;;

  let init_id () = id := 0

  let getInc_id () =
    let re = !id in
    id := (!id+1);
    re

  (**  transform fomrula to MAP formula with id for every node **)
  let rec map_transform_ ff =    
      match ff with
        True -> MTrue
      | False -> MFalse
      | Var (x, y)      -> let id = getInc_id() in  MVar(id ,x,y)
      | And (f, g)      -> let id = getInc_id() in  MAnd (id ,map_transform_ f, map_transform_  g)
      | Or (f, g)       -> let id = getInc_id() in  MOr (id ,map_transform_ f, map_transform_  g)
      | Impl (f, g)     -> let id = getInc_id() in  MImpl (id ,map_transform_ f, map_transform_  g)
      | Equiv (f, g)    -> let id = getInc_id() in  MEquiv (id ,map_transform_ f, map_transform_  g)
      | Until (f, g)    -> let id = getInc_id() in  MUntil (id ,map_transform_ f, map_transform_  g)
      | WeakUntil (f,g) -> let id = getInc_id() in  MWeakUntil (id ,map_transform_ f, map_transform_  g)
      | Release (f, g)  -> let id = getInc_id() in  MRelease (id ,map_transform_ f, map_transform_  g)
      | Not f           -> let id = getInc_id() in  MNot (id ,map_transform_ f)
      | Next f          -> let id = getInc_id() in  MNext (id ,map_transform_ f)
      | Finally f       -> let id = getInc_id() in  MFinally (id ,map_transform_ f)
      | Globally f      -> let id = getInc_id() in  MGlobally (id ,map_transform_ f)
      | Exists (x, f)   -> let id = getInc_id() in  MExists (id ,x, map_transform_ f )
      | Forall (x, f)   -> let id = getInc_id() in  MForall (id ,x, map_transform_ f)

  let map_transform f = 
    init_id();
    map_transform_ f


    let rec map_reset_ ff = 
      match ff with
        MTrue -> MTrue
      | MFalse -> MFalse
      | MVar (_,x, y)      -> let id = getInc_id() in  MVar(id ,x,y)
      | MAnd (_,f, g)      -> let id = getInc_id() in  MAnd (id ,map_reset_ f,map_reset_ g)
      | MOr (_,f, g)       -> let id = getInc_id() in  MOr (id ,map_reset_ f,map_reset_ g)
      | MImpl (_,f, g)     -> let id = getInc_id() in  MImpl (id ,map_reset_ f,map_reset_ g)
      | MEquiv (_,f, g)    -> let id = getInc_id() in  MEquiv (id ,map_reset_ f,map_reset_ g)
      | MUntil (_,f, g)    -> let id = getInc_id() in  MUntil (id ,map_reset_ f,map_reset_ g)
      | MWeakUntil (_,f,g) -> let id = getInc_id() in  MWeakUntil (id ,map_reset_ f,map_reset_ g)
      | MRelease (_,f, g)  -> let id = getInc_id() in  MRelease (id ,map_reset_ f,map_reset_ g)
      | MNot (_,f)           -> let id = getInc_id() in  MNot (id, map_reset_ f)
      | MNext (_,f)          -> let id = getInc_id() in  MNext (id, map_reset_ f)
      | MFinally (_,f)       -> let id = getInc_id() in  MFinally (id, map_reset_ f)
      | MGlobally (_,f)       -> let id = getInc_id() in  MGlobally (id, map_reset_ f)
      | MExists (_,x, f)   -> let id = getInc_id() in  MExists (id ,x, map_reset_ f )
      | MForall (_,x, f)   -> let id = getInc_id() in  MForall (id ,x, map_reset_ f)
      | MPathEqual (pv1,pv2) -> MPathEqual (pv1,pv2)
      | MMap (_,pv, g)       -> let id = getInc_id() in MMap(id, pv, map_reset_ g)

  let map_reset f = 
    init_id();
    map_reset_ f

    
    let buildCombPV  pv fpv =
        pv^"I"^fpv^"I"
    
    (**
    Find positon of  forall pv to enumerat forall exists preceding and not preceding path variables 
    **)
    let rec enumerate_forall_epv fpv parentPV directPVs new_epv_lst e_f = 
          let rec_ f = enumerate_forall_epv fpv parentPV directPVs new_epv_lst f in
            match e_f with 
                  MTrue                 -> MTrue
                | MFalse                -> MFalse
                | MVar (id,x, y)        -> MVar (id,x, y)
                | MForall (id,pv , g)   -> if (comparePV fpv pv)
                                            then enumerate_forall_exists pv (directPVs@new_epv_lst) g
                                            else MForall (id,pv, rec_ g)
                | MExists (id,pv, g)    -> if (List.mem (buildCombPV pv fpv) new_epv_lst)
                                           then ( (* if in indirect scope ensure same paths  *)
                                             let ap_globally = MPathEqual(pv,(buildCombPV pv fpv))      in (* MGlobally (id, MEquiv(id, MVar(id,"a",pv), MVar(id,"a",pv^"="^fpv) )) in *)
                                             MExists (id,pv, MAnd(id, ap_globally , rec_ g)) 
                                           )
                                           else MExists (id,pv,rec_ g)
                | MNot (id,g)           -> MNot (id, rec_ g)
                | MNext (id,g)          -> MNext(id, rec_ g)
                | MFinally (id,g)       -> MFinally(id, rec_ g)
                | MGlobally (id,g)      -> MGlobally(id, rec_ g)
                | MMap (id,pv, g)       -> MMap (id,pv, rec_ g)
                | MAnd (id,h, g)        -> MAnd(id,rec_ h, rec_ g)
                | MImpl (id,h, g)       -> MImpl(id,rec_ h, rec_ g)
                | MEquiv (id,h, g)      -> MEquiv(id,rec_ h, rec_ g)
                | MOr (id,h, g)         -> MOr(id,rec_ h, rec_ g)
                | MUntil (id,h, g)      -> MUntil(id,rec_ h, rec_ g )
                | MWeakUntil (id,h, g)  -> MWeakUntil(id,rec_ h, rec_ g)
                | MRelease (id,h, g)    -> MRelease (id, rec_ h ,  rec_ g)
                | MPathEqual (pv1,pv2)  -> MPathEqual (pv1,pv2)
                

    (** get direct precessors of forall quantified path variable fpv in epvlst list **)
    let rec get_directPrPV_ fpv epvlst e_f lst = 
      let rec_ f lst = get_directPrPV_ fpv epvlst f lst in
          match e_f with 
              MTrue | MFalse | MVar (_,_, _) | MPathEqual (_,_) -> []
            | MForall (id,pv , _) -> if( comparePV fpv pv )then lst else [] (* check for right fpv*)
            | MExists (id,pv, f)  -> if (List.mem pv epvlst)
                                    then rec_ f (pv::lst)
                                    else rec_ f lst
            | MNot (id,f) | MNext (id,f) | MFinally (id,f) | MGlobally (id,f) | MMap (id,_,f) -> rec_ f lst
            | MAnd (id,f, g) | MImpl (id,f, g) | MEquiv (id,f, g) | MOr (id,f, g) | MUntil (id,f, g) 
            | MWeakUntil (id,f, g) | MRelease (id,f, g) ->  (
              let lst_f = rec_ f lst in
              let lst_g = rec_ g lst in
              if( List.length lst_f  > 0)
              then (if (List.length lst_g > 0 ) 
                    then raise (Error "not both list can be non empty: duplicate path variables?")
                    else lst_f
              )else lst_g
            )

    let get_directPrPV fpv epvlst e_f =
        get_directPrPV_ fpv epvlst e_f [] 


    let get_newPV_Map_lst fpv directPVs epvlst =
       let lst = List.map (fun pv -> (if (List.mem pv directPVs) then "" else buildCombPV pv fpv )) epvlst in
       (* remove empty elements *)
       let lst = foldr_rem_dupl_star lst in
       lst

    (* introduce new exist pv for unrolling epv not scoping over fpv *)   
    let introduce_new_exist  fpv pid parentPV epvlst e_f =
      let directPVs = if (comparePV parentPV "*")
                     then get_directPrPV fpv epvlst e_f  (* if parent==*  do not add it to the set*)
                     else parentPV::(get_directPrPV fpv epvlst e_f)  in

      let new_epv_lst = get_newPV_Map_lst fpv directPVs epvlst in (* List without pv, which scopes over fpv *)
     (* print_list new_epv_lst; *)
      (* We do not need to introduce a new pv for the already in a earlier step introduce parent pv, so we just need to unroll it later *)
      let g = enumerate_forall_epv fpv parentPV directPVs new_epv_lst  e_f in
      List.fold_left (fun map epv -> MExists(-1,epv,map) ) g new_epv_lst
      

    (*
     unroll the formula at the start of the entry point 
    *)
    let rec unroll_at_parent fpv pid parentPV epvlst e_f = 
      let rec_ f =  unroll_at_parent  fpv pid parentPV epvlst f in
      let new_exist f = introduce_new_exist fpv pid parentPV epvlst f in
      match e_f with 
              MTrue                 -> MTrue
            | MFalse                -> MFalse
            | MVar (id,x, y)        -> MVar (id,x, y)
            | MForall (id,pv , g)   -> if id == pid 
                                        then new_exist e_f
                                        else MForall (id, pv, rec_ g)
            | MExists (id,pv, g)    -> if id == pid 
                                        then new_exist e_f
                                        else MExists (id,pv, rec_ g)
            | MNot (id,g)           -> if id == pid 
                                        then new_exist e_f
                                        else MNot (id, rec_ g)
            | MNext (id,g)          -> if id == pid 
                                        then new_exist e_f
                                        else MNext(id, rec_ g)
            | MFinally (id,g)       -> if id == pid 
                                        then new_exist e_f
                                        else MFinally(id, rec_ g)
            | MGlobally (id,g)      -> if id == pid 
                                        then new_exist e_f
                                        else MGlobally(id, rec_ g)
            | MMap (id,pv, g)       -> if id == pid 
                                        then new_exist e_f
                                        else MMap (id,pv, rec_ g)
            | MAnd (id,h, g)        -> if id == pid 
                                        then new_exist e_f
                                        else MAnd(id,rec_ h, rec_ g)
            | MImpl (id,h, g)       -> if id == pid 
                                        then new_exist e_f
                                        else MImpl(id,rec_ h, rec_ g)
            | MEquiv (id,h, g)      -> if id == pid 
                                        then new_exist e_f
                                        else MEquiv(id,rec_ h, rec_ g)
            | MOr (id,h, g)         -> if id == pid 
                                        then new_exist e_f
                                        else MOr(id,rec_ h, rec_ g)
            | MUntil (id,h, g)      -> if id == pid 
                                        then new_exist e_f
                                        else MUntil(id,rec_ h, rec_ g )
            | MWeakUntil (id,h, g)  -> if id == pid 
                                        then new_exist e_f
                                        else MWeakUntil(id,rec_ h, rec_ g)
            | MRelease (id,h, g)    -> if id == pid 
                                        then new_exist e_f
                                        else MRelease(id,rec_ h, rec_ g)
            | MPathEqual (pv1,pv2) -> MPathEqual (pv1,pv2)




    let rec unroll_forall fpv pid parentPV epvlst f = 
      unroll_at_parent fpv pid parentPV epvlst f

    let enumerate_exists_forall nnf_f = 
      let ap = getAPs nnf_f in
      
      let m_f = ref (map_transform nnf_f) in
      let e_f = ref (enf_transform !m_f) in

        while (containForall !m_f) do
          (** get forall node to unroll **)
          let fpv = getForallQuant !m_f in

          (** get list of interacting pv **)
          e_f := enf_transform !m_f;

          let id, parent, pvlst = get_fpv_pvlst_id_ fpv !e_f in
          (** unroll interaction **)
          m_f := unroll_forall fpv id parent pvlst !m_f;

          (** next qunat *)
          m_f := map_reset !m_f;

        done;
        map_transBack !m_f ap

        

    (** check formula for enf form**)
    let check_indirect_scope nnf_f = 
        let m_f = map_transform nnf_f in
        let enf = enf_transform m_f in 
        check_enf_ enf
    
    
    let notfast = ref false ;;
        

    (* 
    Check a formula for enf and return equisatifiable EHyperCTL formula
    *)
    let check_and_transform f =
      (* check for fast trans *)
      let nnf_f = if !notfast then  nnf f  else nnf_fast f in
      (* check direct scope *)
      let direct_scope = check_EA_structure nnf_f in
      (* indirect scope *)
      let indirect_scope = check_indirect_scope nnf_f  in

      let nnf_f = if (only_forall nnf_f)
              then Exists("prnt",nnf_f)
              else nnf_f 
              in

      if( direct_scope && indirect_scope ) then (
      let e_f = enumerate_exists_forall nnf_f in

      e_f 
      )else raise (Error "Formula not in ENF-Fragment: universall quantifier in (in)direct scope of existentially one")

