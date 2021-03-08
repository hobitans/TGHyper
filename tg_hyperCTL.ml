(* Based on incremantion loop sat checking of MGhyper, add funktionality for overall timeout *)
open EnfFormula
open Printf
open FormulaHyperCTL
open Functions

(*######*)
(* Vars *)

let verbose = ref false
let timeout = ref 0.0


let check_sat_E_hyperCTL_ f k qd_max aps  =
  printf "check_sat_E_hyperCTL_ call(%s):\n bound %d  %d qd %d \n" (hyperctl_str f) !k !qd_max;
  let boolFormula, pvmap_lst = Unrolling.unroll f k aps in
  let sat = InvokeSatSolver.invoke_SATSolver boolFormula pvmap_lst !k in
  sat



let check_sat_E_hyperCTL f =
    let aps = getAPs f in
    let sat = ref false in 
    (* return the max alternation of quantifier and temp ops *)
    let k = ref 3 in      
    let k_max =  getMaxUnrollingBound f in (* 2^|f| * |f| *)
    let qd_max = ref (getQuantDepth f) in 
    let next = ref true in
    let start = Unix.gettimeofday () in
    while !next do
      if !verbose then (
      printf "----->%d-%d-%B\n" k_max !k !sat;
      print_newline (); );
      sat := check_sat_E_hyperCTL_ f k qd_max aps;
      if ( !sat || !k >= k_max)
         then next := false
         else (k := !k+1 );
      (** timeout **)
      let stop = Unix.gettimeofday () in 
      if(( !timeout >  0.0 ) && (  ( stop -. start ) > !timeout ) )
      then (
         printf "*****timeout******";
         printf "-timeout(%fs)--%fs->%d-%B\n" !timeout ( stop -. start ) !k !sat;
         next := false
      )else(
        if !verbose then printf "time<(%fs)-%fs->%d-%B\n" !timeout ( stop -. start ) !k !sat;
      ) 

    done;
    !sat



let check_sat_EA_hyperCTL f =
  (* Transform ENF-Hyperformula *)
  if !verbose 
  then  printf "ENF-HyperCTL formula:\n %s\n%!" (hyperctl_str f) ;
  let e_f = check_and_transform f in
  
  if !verbose 
  then  printf "Transform formula to E-HyperCTL:\n %s\n%!" (hyperctl_str e_f) ;
  let sat = check_sat_E_hyperCTL e_f in
  sat


