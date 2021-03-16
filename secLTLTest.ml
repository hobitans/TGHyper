(*********************************

Construct the different test cases of SecLTL

**********************************)


open FormulaHyperCTL
open Functions 

let equalAP_ pv1 pv2 a = 
  let form =  ( Equiv(Var(a,pv1), Var(a,pv2)) ) in
  form

let notEqualAP_ pv1 pv2 a = 
  let form =  ( Not(Equiv(Var(a,pv1), Var(a,pv2)) )) in
  form


let equalAps p pv lst = 
  let hd = List.hd lst in
  let tl = List.tl lst in
  let frst =  equalAP_ p pv hd  in
  let f = List.fold_left (fun acc a  -> And(acc, (equalAP_ p pv a ) ) ) frst tl in
  f
  

let notEqualAps p pv lst = 
  let hd = List.hd lst in
  let tl = List.tl lst in
  let frst =  notEqualAP_ p pv hd  in
  let f = List.fold_left (fun acc a  -> Or(acc, (notEqualAP_ p pv a ) ) ) frst tl in
  f

let hideOp_ p pv h l o f = 
  let hideIn =  equalAps p pv l in
  let sameO =   equalAps p pv o in
  let notSameIn =  notEqualAps p pv (h@l) in
  Forall(pv, Next(And( hideIn , Next( WeakUntil( sameO, Or( notSameIn , f )) ) ) ))
  
let buildVar ap p = 
  let (b,a) = ap in
  if b then Var(a,p) else Not(Var(a,p)) 

let buildNode p lst =
    let frst  =  buildVar (List.hd lst ) p in
    let tl = List.tl lst in
    List.fold_left (fun acc ap -> (
                          let var = buildVar ap p in
                          And( acc , var ) 
                    ) ) frst tl 

let buildTrace p lstoflst = 
      let last =  True in
      let f = List.fold_right (fun lst nxt  -> And( (buildNode p lst) , Next( nxt ) ) ) lstoflst last in
      f

  let hideOp p pv f = 
    let h = ["h0";"h1"] in
    let l = ["l0";"l1"] in
    let o = ["o"] in
    hideOp_  p pv h l o f 

(* Non Interference *)    
  let ni1 () = 
      let p = "p" in
      let pv = "pv" in
      let h = ["h"] in
      let l = ["l"] in
      let o = ["o"] in
      let f = False in
      Forall( p , Globally( hideOp_  p pv h l o f ) )
  let ni2 () =  
    let p = "p" in
    let pv = "pv" in
    let h = ["h0";"h1"] in
    let l = ["l0";"l1"] in
    let o = ["o";"o1"] in
    let f = False in
    Forall( p , Globally( hideOp_  p pv h l o f ) )


    (*** Temporal paper
    Forexample,considertheprogram(l:=0 􏰀 l:=0) 􏰀 (l:=1 􏰀 l:=1).A low-observer can infer which branch of the center-most nondeterministic choice is taken, but not which branch is taken next. This is expressed by HyperCTL∗ formula ∀π. X ∀π′. X (lπ ↔ lπ′ ). There is no equivalent HyperLTL formula.
    *)
    let nonDetChoice p pv = 
      Forall( p, Next(Forall(pv,Equiv(Var("l",p),Var("l",pv)))) )


(** conference Managment System ***)
let conMS () =  
  let p = "p" in
  let pv = "pv" in
  let h = ["acc";"rej"] in
  let l = ["sub";"upt";"rvw";"rel";"cls"] in
  let o = ["con";"sry"] in
  let f = Var("rel", p) in
  let hide = hideOp_  p pv h l o f in
  let conMS = Exists(p, Globally( Impl( Next( Var("cls",p) ) , hide ) ) ) in
  conMS 

let conMSystemValid1 () = 
  let p = "p" in
  let p1 = "p1" in
  let p2 = "p2" in
  let pv = "pv" in
  let h = ["acc";"rej"] in
  let l = ["sub";"upt";"rvw";"rel";"cls"] in
  let o = ["con";"sry"] in
  let f = Var("rel", p) in
  let hide = hideOp_  p pv h l o f in
  let conMS =  Globally( Impl( Next( Var("cls",p) ) , hide ) )  in
  let trc1 = [  [(true,"sub");(false,"upt");(false,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
                [(false,"sub");(true,"upt");(false,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
                [(false,"sub");(false,"upt");(true,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
                [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(false,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                [(false,"sub");(false,"upt");(false,"rvw");(true,"cls") ;(false,"rel");(false,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(true,"rel") ;(false,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(true,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(true,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
              ] in
  let trc2 = [  [(true,"sub");(false,"upt");(false,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
              [(false,"sub");(true,"upt");(false,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
              [(false,"sub");(false,"upt");(true,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
              [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(false,"con");(false,"acc");(true,"rej") ;(false,"sry")] ; 
              [(false,"sub");(false,"upt");(false,"rvw");(true,"cls") ;(false,"rel");(false,"con");(false,"acc");(true,"rej") ;(false,"sry")] ; 
              [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(true,"rel") ;(false,"con");(false,"acc");(true,"rej") ;(false,"sry")] ; 
              [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(false,"con");(false,"acc");(true,"rej") ;(true,"sry")] ; 
              [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(false,"con");(false,"acc");(true,"rej") ;(true,"sry")] ; 
            ] in
  let sys1 =  buildTrace p1 trc1 in
  let sys2 =  buildTrace p2 trc2 in
  Exists( p1 ,  Exists( p2 , Forall (p, (And(And(sys1, sys2), conMS ) ) ) )) 


  (** Unsat but to large to proof **)
  let conMSystemFalse () = 
    let p = "p" in
    let p1 = "p1" in
    let p2 = "p2" in
    let pv = "pv" in
    let h = ["acc";"rej"] in
    let l = ["sub";"upt";"rvw";"rel";"cls"] in
    let o = ["con";"sry"] in
    let f = Var("rel", p) in
    let hide = hideOp_  p pv h l o f in
    let trc1 = [  [(true,"sub");(false,"upt");(false,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
                  [(false,"sub");(true,"upt");(false,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
                  [(false,"sub");(false,"upt");(true,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
                  [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(false,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                  [(false,"sub");(false,"upt");(false,"rvw");(true,"cls") ;(false,"rel");(false,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                  [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(true,"rel") ;(false,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                  [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(true,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                ] in
    let trc2 = [ [(true,"sub");(false,"upt");(false,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
                [(false,"sub"); (true,"upt");(false,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(false,"sry")] ; 
                [(false,"sub");(false,"upt");(true,"rvw"); (false,"cls");(false,"rel");(false,"con");(false,"acc");(false,"rej");(true,"sry")] ; 
                [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(false,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                [(false,"sub");(false,"upt");(false,"rvw");(true,"cls") ;(false,"rel");(false,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(true,"rel") ;(false,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
                [(false,"sub");(false,"upt");(false,"rvw");(false,"cls");(false,"rel");(true,"con");(true,"acc");(false,"rej") ;(false,"sry")] ; 
              ] in
    let sys1 =  buildTrace p1 trc1 in
    let sys2 =  buildTrace p2 trc2 in
    Exists( p1 ,  Exists( p2 , And(And(sys1, sys2), Forall (p, hide ) ) ) ) 
  
    
let conMS2 () =  
    let p = "p" in
    let pv = "pv" in
    let h = ["acc";"rej"] in
    let l = ["sub";"upt";"rvw";"rel";"cls"] in
    let o = ["con";"sry"] in
    let f = False in
    let hide = hideOp_  p pv h l o f in
    let conMS = Exists(p, Globally( Impl( Next( Not( Var("cls",p) )) , hide ) ) ) in
    conMS 


    (* not in EA *)
 let confImpl () = 
    let p = "p" in
    let pv = "pvr" in
    let h = ["acc";"rej"] in
    let l = ["sub";"upt";"rvw";"rel";"cls"] in
    let o = ["con";"sry"] in
    let f_r = False in
    let hide_r = hideOp_  p pv h l o f_r in
    let right = Globally( Impl( Next( Not( Var("cls",p) )) , hide_r ) ) in
    let pv = "pvl" in
    let f_l = Var("rel", p) in
    let hide_l = hideOp_  p pv h l o f_l in
    let left = Globally( Impl( Next( Var("cls",p) ) , hide_l ) )  in
    Exists(p, Impl(left,right))


(**  combination of path properties *) 
let comPP () =  
  let p = "p" in
  let pv = "pv" in
  let h = ["s1";"s2"] in
  let l = ["i1";"i2";"i3";"rh";"wl"] in
  let o = ["o1";"2"] in
  let f = False in
  let hide = hideOp_  p pv h l o f in
  let compp = Exists(p, Impl( WeakUntil( Not( Var("rh",p)) , Var("wl",p) ) , hide ))  in
  compp 


let auction () = 
  let p = "p" in
  let pv = "pv" in
  let h = ["b1";"b2";"b3"] in
  let l = ["cA"] in
  let o = ["wA"] in
  let f = Var("wA", p)in
  let hide = hideOp_  p pv h l o f in
  let auc =  Forall(p, Until( hide , Var("cA",p) )) in
  auc 


  let auctionSys () = 
    let p = "p" in
    let p1 = "p1" in
    let p2 = "p2" in
    let pv = "pv" in
    let h = ["b1";"b2";"b3"] in
    let l = ["cA"] in
    let o = ["wA"] in
    let f = Var("wA", p)in
    let hide = hideOp_  p pv h l o f in
    let auc =   Until( hide , Var("cA",p) ) in
    let trc1 = [   
                  [(false,"b1");(false,"b2");(false,"b3"); (false,"wA");(false,"cA")] ; 
                  [(false,"b1");(false,"b2");(true,"b3"); (false,"wA");(false,"cA")] ; 
                  [(false,"b1");(true,"b2");(false,"b3"); (false,"wA");(false,"cA")] ; 
                  [(false,"b1");(false,"b2");(false,"b3"); (false,"wA");(true,"cA")] ; 
                  [(false,"b1");(false,"b2");(false,"b3"); (true,"wA");(true,"cA")] ; 
                  [(false,"b1");(false,"b2");(false,"b3"); (true,"wA");(true,"cA")] ; 
                ] in
    let trc2 = [   
                [(false,"b1");(false,"b2");(false,"b3"); (false,"wA");(false,"cA")] ; 
                [(true,"b1");(true,"b2");(false,"b3"); (false,"wA"); (false,"cA")] ; 
                [(false,"b1");(false,"b2");(true,"b3"); (false,"wA"); (false,"cA")] ; 
                [(false,"b1");(false,"b2");(false,"b3"); (false,"wA"); (true,"cA")] ; 
                [(false,"b1");(false,"b2");(false,"b3"); (true,"wA"); (true,"cA")] ; 
                [(false,"b1");(false,"b2");(false,"b3"); (true,"wA"); (true,"cA")] ; 
              ] in
    let sys1 =  buildTrace p1 trc1 in
    let sys2 =  buildTrace p2 trc2 in
    Exists( p1 ,  Exists( p2 ,  Forall (p, And(And(sys1, sys2), auc ) ) )) 


let keyRet () = 
  let p = "p" in
  let pv0 = "pv"^(string_of_int 0) in
  let pv1 = "pv"^(string_of_int 1) in
  let pv2 = "pv"^(string_of_int 2) in
  let h_l = ["k"] in
  let h_r = ["k"] in
  let l = ["l"] in
  let o = ["o"] in
  let f = False in
  let key1   = hideOp_  p pv0 h_l l o f in
  let hide_l = hideOp_  p pv1 h_l l o f in
  let hide_r = hideOp_  p pv2 h_r l o f in
  let key2 =   Or(hide_l,hide_r) in
  let keyret = Exists(p, And(key1,Not(key2)) )  in
  keyret

 
let keyRet1 () = 
  let p = "prnt" in
  let pv0 = "pv"^(string_of_int 0) in
  let h_l = ["k"] in
  let l = ["l"] in
  let o = ["o"] in
  let f = False in
  hideOp_  p pv0 h_l l o f

  let keyRet11 () = 
    let p = "prnt" in
    let pv0 = "pv"^(string_of_int 1) in
    let h_l = ["k"] in
    let l = ["l"] in
    let o = ["o"] in
    let f = False in
    let nnf = hideOp_  p pv0 h_l l o f in
    nnf_fast (Not(nnf))

  let keyRet2 () = 
    let p = "prnt" in
    let pv1 = "pv"^(string_of_int 1) in
    let pv2 = "pv"^(string_of_int 2) in
    let h_l = ["k"] in
    let h_r = ["k"] in
    let l = ["l"] in
    let o = ["o"] in
    let f = False in
    let hide_l = hideOp_  p pv1 h_l l o f in
    let hide_r = hideOp_  p pv2 h_r l o f in
    Or(hide_l,hide_r) 

    let keyRet_ i =
      let p = "ip" in
      let pv0 = "pv"^(string_of_int i) in
      let h_l = ["k"] in
      let l = ["l"] in
      let o = ["o"] in
      let f = False in
      hideOp_  p pv0 h_l l o f

    let keyRet i =
      let p = "ip" in
      let pv j = "pv"^(string_of_int i)^"i"^(string_of_int j) in
      let lst = List.init (i) (fun j -> "s"^(string_of_int (i - j )) ) in
      let l i = (List.filter (fun elm -> (compare elm ("s"^(string_of_int i))) <> 0) ) lst in
      let liste = ["l"]@(l i) in

      let o = ["o"] in

      let lst = List.init (i) (fun j -> (i - j - 1 ) ) in
      List.iter (fun i -> Printf.printf "%d" i) lst ;
      let keysOr = List.fold_left (fun acc i -> Or((hideOp_ p (pv i) ["s"^(string_of_int i)] liste o False),acc )) False lst in
      keysOr

      



let nesting nests pv = 
  let p = "p" in
  let pv i = pv^(string_of_int i) in
  let l = ["l"] in
  let o = ["o"] in
  let lst = List.init (nests) (fun i -> (nests - i - 1 ) ) in
  List.iter (fun i -> Printf.printf "%d" i) lst ;
  let nestings = List.fold_left (fun acc i -> hideOp_ p (pv i) ["k"^(string_of_int i)] l o acc ) False lst in
  nestings

  let nestsImp  i  j = 
    Exists("p", Impl( Next(nesting i "pl") , Next(nesting j "pr") ) )



let testhide () = 
    let f  = keyRet 10 in
    print_hyperCTL f; 


  