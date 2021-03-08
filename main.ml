(**
`main.ml`` is adapted from MGHyper/EAHyper. We adapted the mode handling procedures and reused most of the flags from MGHyper/EAHyper, 
            so that users/scripts familiar with those tools can easily adapt. We reuse the file and string input handling methods of MGHyper/EAHyper.
            We add, among other things, the following functionality/flags:
    - ``-r`` randomly assign path variables ``pv`` to atomic propositions ``ap``, where the ``pv`` scopes over ``ap``.
    - ``--graph`` If the formula is satisfiable, a graph representation of the assignment is shown.
    - ``--notfast`` Replace G F operators by U R and do not use the smaller reduction (default false).
    - ``--secLTL`` Print a SecLTL formula from our test set to adapt the formula adapt file ``secLTLTest.ml``.
**)

(* Hyper Tools *)
open Tg_hyperCTL
(**Formulas**)
open FormulaHyperCTL
open Functions
(**Extern**)
open Printf

(* Parse formula*)
let formula_of_string s =
  Parser.parse_hyperctl_formula Lexer.lex (Lexing.from_string s)

let formula_of_file file =
  let ic = open_in file in
  let f = Parser.parse_hyperctl_formula Lexer.lex (Lexing.from_channel ic) in
  close_in ic; f



(********* VARS - set by flags ************)
let formula_string = ref ""
let formula_string2 = ref ""
let formula_file = ref ""
let formula_file2 = ref ""
let from_file = ref true
let from_file2 = ref true
let verbose = ref false
let graph = ref false
let timeout = ref 0.0
let size = ref false
(* Vars Multimode*)
let randomfix = ref false
let notfast = ref false
let secLTL = ref false

(*set vars in TGHyperCTL*)
let set_vars_in_tg_hyperCTL () =
  Tg_hyperCTL.verbose := !verbose;
  Tg_hyperCTL.timeout := !timeout;
  InvokeSatSolver.graph := !graph;
  InvokeSatSolver.verbose := !verbose;
  RandHyperCTL.verbose := !verbose;
  Unrolling.verbose := !verbose;
  EnfFormula.notfast := !notfast;
  if !verbose then printf "set vars in submodules\n"


(*####################################################*
 *#   CALL CENTER - Handeling the different Modes    #*
 *####################################################*)
let hyperctl_default_mode () = 
        let f =
                if !from_file then formula_of_file !formula_file
                else formula_of_string !formula_string
        in
        let f = 
          if !randomfix 
          then (
            RandHyperCTL.assignAPstoPV f !formula_file
          )
          else f 
        in
        if !size then (printf "size of formula:%d " (getFormulaSize (EnfFormula.check_and_transform f)) )
        else(
        let sat = check_sat_EA_hyperCTL f in
        if !verbose then
           if sat  then printf "%s\nFormula is satisfiable.\n" (hyperctl_str f)
           else  printf "%s\nFormula is not satisfiable.\n" (hyperctl_str f)
        else print_endline (bool2sat_str sat)
        )



(* mode handler*)
let default_mode () =
        hyperctl_default_mode()


let time_mode () =
      Functions.getExecutionTimeofInstance (hyperctl_default_mode )

let removePrntTrace f = 
  (* remove prnt variable introduce for sat of single formulas **)
  match f with
    | Exists (x, g)   -> (
      if ((compare x "prnt") == 0) then  g else f 
    )
    | _ -> f

let buildcheck_implication f g =
  (* remove parent trace *)
 let f =  removePrntTrace f in
 let g =  removePrntTrace g in
  let impl = Exists( "ip",(And( f, Not(g))) ) in
  (* only print sizse of the formula size*)
  if !size then (printf "size of formula:%d \n implications is not checked!!!" (getFormulaSize (EnfFormula.check_and_transform impl));  true)
  else (
    (*check implication *)
  if !verbose then 
    print_hyperCTL impl;
  let sat = check_sat_EA_hyperCTL impl in 
  not(sat)
  )

let hyperctl_impl_mode () =
  (* get formulas *)
  let f =
    if !from_file then formula_of_file !formula_file
    else formula_of_string !formula_string in
  let g =
      if !from_file2 then formula_of_file !formula_file2
      else formula_of_string !formula_string2 in
  let sat = buildcheck_implication f g in
  if sat then printf "\n implication does hold" else printf "\n implication does not hold"
  


let impl_mode () =
  printf "\n Implication mode\n";
  hyperctl_impl_mode()


let equiv_mode () =
  (* get files *)
  let f =
    if !from_file then formula_of_file !formula_file
    else formula_of_string !formula_string in
  let g =
      if !from_file2 then formula_of_file !formula_file2
      else formula_of_string !formula_string2 in
  if !verbose then printf "check e -> es ... \n";
  let sat_left = buildcheck_implication f g in 
  if sat_left then  (
  if !verbose then printf "check e <- es ...\n";
  let sat_right = buildcheck_implication g f in
  if sat_right then printf "equivalenz  holds" else printf "equiv does not hold"
  )
  else
  printf "equivalenz does not hold"


(*multi mode*)
let get_lines file =
  let lines = ref [] in
  let chan = open_in !formula_file in
  try 
     while true do 
        lines := input_line chan :: !lines done; []
  with End_of_file -> close_in chan; List.rev !lines


let multi_mode ()  =
 let multi_mode_ref = default_mode in
  from_file := false;
  let i = ref 0 in
  let t = ref 0 in
  let runtime = ref 0.0 in
  let handle_line line =
  if !verbose then printf "line=%d i=%i  t=%d\n" (!i + !t) (!i) (!t);
    match line with
      "" -> ()
    | _ -> ( if !verbose then printf "formula(%d):" (!i + !t);
                let start = Unix.gettimeofday () in
                formula_string := line;
                multi_mode_ref ();
                let stop = Unix.gettimeofday () in 
                let single_runtime = (stop -. start) in
                if  ( (!timeout > 0.0) && ( single_runtime > !timeout))
                then (
                    t := !t+1; 
                  ) else ( 
                    runtime := !runtime +. single_runtime;
                    i := !i + 1; 
                  );
                if !verbose then printf "runtime: %fs\n%!" single_runtime;
    )
  in
  List.iter handle_line (get_lines !formula_file);
  if !verbose then printf "solved:%d, timeoute%d, time:%fs, avg:%fs\n" !i !t !runtime (!runtime /. (float_of_int !i))
(**********)

let print_secLTL () = 
    SecLTLTest.testhide ()



(* ############################# END - CALL CENTER ############################# *)

let show_help = ref false

let mode_ref = ref default_mode

let spec_list =
  [
  "--help", Arg.Set show_help , "Show help message";
  "-f",
   Arg.String
     (fun f -> formula_file := f; from_file := true; show_help := false),
   "File with the formula to check.";
   "-fs", Arg.String (fun f -> formula_string := f; from_file := false; show_help := false),
   "String representation of formula to check example:\"exists p.G(a_p)\".";
   "-v", Arg.Set verbose, "verbose output";
   "-s", Arg.Set size, "Return only size of formula";
   "--graph", Arg.Set graph, "If the formula is satisfiable, a graph representation of the assignment is shown. (Requirements Dot Graphviz and OcamlGraph ) ";
   "-r", Arg.Set randomfix, "Randomly assigna atomic propositions to path variables.";
   "--notfast", Arg.Set notfast, "Replace G F operators by U R and do not use the smaller reduction (default false)";
   "--secLTL", Arg.Unit (fun _ -> mode_ref :=  print_secLTL ), "Print SecLTL test formulas";
   "-m",
   Arg.String
     (fun f -> formula_file := f; mode_ref := multi_mode; show_help := false),
   "File with multiple formulas to check.";
   "-t", Arg.Float (fun t -> timeout := t),
   "Timeout in float for one instance( not strict:does not stop longer execution of SAT-solver)";
   "-i", Arg.String (fun i -> formula_file2 := i; mode_ref := impl_mode),
   "File to imply.  \"ip\" is the shared path variable";
   "-is",
   Arg.String
     (fun i ->
        formula_string2 := i; from_file2 := false; mode_ref := impl_mode),
   "Formula to imply.";
   "-e", Arg.String (fun e -> formula_file2 := e; mode_ref := equiv_mode),
   "File to equal. \"ip\" is the shared path variable";
   "-es",
   Arg.String
     (fun e ->
        formula_string2 := e; from_file2 := false; mode_ref := equiv_mode),
   "Formula to equal.";
   ]

let arg_failure arg = raise (Arg.Bad ("Bad argument: " ^ arg))
let usage_msg =
  "./main.native \n check satisfiability of ENFHyperCTL formulas, where the next operators are as outermost as possible and not directly under temporal operatos\nList of flags"

let main =
  Arg.parse spec_list arg_failure usage_msg;
  if !show_help 
  then Arg.usage spec_list usage_msg 
  else (set_vars_in_tg_hyperCTL(); !mode_ref ())
  

