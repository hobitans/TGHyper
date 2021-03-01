open Functions

let graph = ref false
let verbose = ref false

let is_SAT_OUTPUT o =  
  str_contains o "% SATISFIABLE"

let invoke_SATSolver bool_form_str pvmap_lst k =

(*create file*)
let file = "./files/unr_form.in" in
let oc_file = open_out file in
Printf.fprintf oc_file "%s\n" bool_form_str;
close_out oc_file;

(*
  The follwoing Code use limbool for generating CNF formulas
  By adatping these lines, it is possible to use SAT-Solver, that can handle CNF formulas

  invoke limbool for generating CNF DIMAC files
  let pfile = "./files/punr_form.in" in
  let limboolcall =  "./solvers/limbooleOSX  -d "^file ^" > "^pfile in
  let ( icp, ocp ) = Unix.open_process limboolcall in
  close_out ocp;

  *)
let limboolcall =  "./solvers/limbooleOSX "^file^" -s " in
let (ic, oc) = Unix.open_process limboolcall
in 
(* output_string oc file;*)
close_out oc;

(* read output *)
let buf = Buffer.create 16 in
(try while true do (Buffer.add_channel buf ic 1 )done with End_of_file -> ());
let _ = Unix.close_process (ic, oc) in
let output = Buffer.contents buf in

if (is_SAT_OUTPUT output && !graph ) then
GraphFactory.call_graph_factory output pvmap_lst k;

if !verbose then 
Printf.printf "Output:\n %s \n" output;

is_SAT_OUTPUT output


