
 open Functions
 open Graph


let compare_v v1 v2 =
   let (pv1, s1,_) = v1 in
   let (pv2, s2,_) = v2 in
   let cmp = compare pv1 pv2 in
   if cmp == 0 then compare s1 s2 else cmp

(* struct of Graph **)
 module V = struct
   type t = string * int * string list
   type label = string
   let compare = compare_v
   let hash = Hashtbl.hash
   let equal = (=)
end

module E = struct
   type t = int
   let compare = Pervasives.compare
   let equal = (=)
   let default = 0
end

(* Graph *)
module G =  Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(V)(E)

(* Dot module for printing  *)
let vertex_to_string v = 
   let (pv,step,lst) = v in 
   let nodeid = Printf.sprintf "%s-%d" pv step in
   "\""^nodeid^"["^(lst_to_string_ lst)^"]\""

(* Dot module for printing ap only *)
let vertex_to_ap v = 
   let (pv,step,lst) = v in 
   let nodeid = Printf.sprintf "%s-%d" pv step in
   (lst_to_string_ lst)

module Dot = Graph.Graphviz.Dot(
   struct
      include G
      let edge_attributes ( _,_,_ ) = [`Color 42]
      let default_edge_attributes _ = []
      let get_subgraph _ = None
      let vertex_name v = vertex_to_string v
      let default_vertex_attributes _ = []
      let vertex_attributes v = [`Label (vertex_to_ap v); `Shape `Box] 
      let graph_attributes _ = []
   end
      )

(** struct for stroring tree **)
module Steps = 
struct 
   type t = string * int
   let compare = Pervasives.compare
end

module Traces = Map.Make(Steps)

(** Graph struc **)
let g = (ref G.empty);;
let special_edges = (ref [] );;
(** Fill tree from Limbool SatSolver output **)
let tree = (ref Traces.empty );;

let print_tree () = 
            Printf.printf "Tree \n";
            Traces.iter (
               fun key value -> ( let (pv,step) = key in
                                  Printf.printf "%s-%d" pv step;
                                  print_lst value
                                 )
               ) !tree;
            print_newline ()

let add_node pv step aps =
   tree := Traces.add (pv,step) aps !tree


let get_node pv step = 
try
   Traces.find (pv,step) !tree
with Not_found -> []

let add_to_tree pv step ap =
   let n =  get_node pv step in
   add_node pv step (ap::n)


let get_aps_from_tree_ pv steps =
   try
   Traces.find (pv,steps) !tree
   with Not_found -> []

let find_vertex v g =
   if G.mem_vertex g v 
   then 
   (
      let (pv,steps,_) = v in
      let aps = get_aps_from_tree_ pv steps in
      G.V.create(pv,steps,aps)
   )
   else v 

let add_invariant_edge pv k v= 
   let step = k-1 in
   let aps =  get_aps_from_tree_ pv step in
  (* let aps = foldr_rem_dupl_inv aps_i in *)
   let v_k = G.V.create (pv, step , aps) in
   special_edges := (v_k , v)::(!special_edges)


let rec create_vertex pv k step =
   let aps_i =  get_aps_from_tree_ pv step in
   if List.mem "inv" aps_i
   then ((* invariant found add to special edges *)
      let aps = foldr_rem_dupl_inv aps_i in
      let v = G.V.create (pv,step, aps) in
      add_invariant_edge pv k v;
      v
   )
   else 
      G.V.create (pv,step, aps_i)


let add_traces_to_graph k elm = 
   let (pv,parent,step) = elm in 
   print_newline();
   Printf.printf "(%s %s %d)\n" pv parent step; 
   (** todo shorten list k+1-> k *)

   let vertex_lst = List.init (k) (create_vertex pv k ) in

   (* check for first trace *)
   if( compare parent "***" <> 0) then (
      (* skip first entry, because it is already as parent in graph :todo for testing remove*)
      let v_lst = List.tl vertex_lst in
      (* create parent and start , add to special edges*)
      let prt = create_vertex parent k step in
      let start = List.nth  v_lst 0 in
      special_edges := (prt , start)::(!special_edges);

      (* add vertex to Graph*)
      List.iter (fun v -> g := G.add_vertex !g v ) v_lst;
      (* add edges *)
      for i=0 to ((List.length v_lst) - 2 ) do
         let cur = List.nth  v_lst i in
         let next = List.nth v_lst  (i+1) in
         g := G.add_edge !g cur next
      done
      )else(

         List.iter (fun v -> Printf.printf "%s" (vertex_to_string v) ) vertex_lst;

         (* add vertex *)
         List.iter (fun v -> g := G.add_vertex !g v ) vertex_lst;
         (* add edges *)
         for i=0 to ((List.length vertex_lst) - 2 ) do
            let cur = List.nth  vertex_lst i in
            let next = List.nth vertex_lst  (i+1) in
            g := G.add_edge !g cur next
         done

      )




(****************************************************************)


let build_graph pvmap_lst k = 
   g := G.empty;
   special_edges := [];

   (** pvmap iter  **)
   Printf.printf "PVMAP in Graphfactory\n";
   List.iter (add_traces_to_graph k) pvmap_lst;
   (* add special edges *)
   List.iter (fun elm  -> (let (v1,v2) = elm in g := G.add_edge !g v1 v2;) ) !special_edges;

   let dotfile = "./files/out.dot" in
   let file = open_out_bin dotfile in                                                               
   Dot.output_graph file !g;
   
   let pdffile = "./files/out.pdf" in
   (* build graph  from dot *)
   let dotcall =  " dot -Tpdf "^dotfile^"  -o "^pdffile^"; open "^pdffile^";" in
   let (_,_) = Unix.open_process dotcall in
   Printf.printf "Open Graph ... "



(** build vertex Map **)
let print_lst lst  = Printf.printf "[\n"; List.iter (Printf.printf "%s \n")  lst; Printf.printf "\n]"

let eq = Char.chr(61);;

let linefeed = Char.chr(10);;

let at = Char.chr(64);;

let brace_o = Char.chr(91);;

let brace_c = Char.chr(93);;


let add_line_to_Map__ in_lst =
   let ap = List.nth in_lst 0 in
   let right = List.nth in_lst 1 in
   let lst =  String.split_on_char brace_o right in
   let pv = List.nth lst 0 in
   let step = int_of_string (List.nth (String.split_on_char brace_c (List.nth lst 1) ) 0)  in
   Printf.sprintf "%s -> %s -> %d\n" pv ap step;
   add_to_tree pv step ap
   
   
 
 
 let add_line_to_Map_ line_lst = 
   if str_contains (List.nth line_lst 1) "1"
   then
     (
       let left = List.nth line_lst 0 in
       let lst =  String.split_on_char at  left in
       if  (List.length lst) > 1
       then add_line_to_Map__ lst
     )
 
 
 let add_line_to_Map line = 
   if( str_contains line "="  ) 
   then 
     begin
     let lst =  String.split_on_char eq  line in
     add_line_to_Map_ lst
     end
 
 let assignment_to_Tree output =
   let lst =  String.split_on_char linefeed  output in
   List.iter (add_line_to_Map ) lst
 
 

let call_graph_factory output pvmap_lst k =
   assignment_to_Tree output;
   build_graph pvmap_lst k

   
   
 