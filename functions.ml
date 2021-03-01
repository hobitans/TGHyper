(**
Collection of functions, needed at different points.
Some of the function are from MGHyper, respectivly EAHyper, and where modify for handeling  TGHyper/HyperCTL* specificication.
**)


open Printf

(* Print f *)
let print_list lst  = printf "[";List.iter (printf "%s,")  lst;printf "]"

let print_lst lst  = Printf.printf "[\n"; List.iter (Printf.printf "%s \n")  lst; Printf.printf "\n]"

let rec lst_to_string_ lst =
  match lst with
  [] -> ""
  | hd::tl -> hd^" "^(lst_to_string_ tl)
              
  let getExecutionTimeofInstance fun_  = 
    let startTime =  Unix.gettimeofday () in
    let sat = fun_ () in
    let time = Unix.gettimeofday () -. startTime in
    printf "Execution time of Instance: %f\n" time;
    sat

(* 
The following functions are based on MGHyper/EAHyper
*)
let bool2sat_str sat = if sat then "sat" else "unsat"

(* list operations *)
let remove_duplicate xs x = 
    if List.mem x xs
      then xs 
      else x :: xs

let foldr_rem_dupl xs = List.fold_left remove_duplicate [] xs

let remove_duplicate_star xs x = 
  if List.mem x xs || ((compare x "*") == 0) || ((compare x "") == 0)
    then xs 
    else x :: xs

let remove_duplicate_inv xs x = 
      if List.mem x xs || ((compare x "inv") == 0) || ((compare x "") == 0)
      then xs
      else  x :: xs
  
let foldr_rem_dupl_inv xs = 
        List.fold_left remove_duplicate_inv [] xs 

let foldr_rem_dupl_star xs = 
    List.fold_left remove_duplicate_star [] xs 
    

let  dupl_exists  xs = 
  let len_rem = List.length (foldr_rem_dupl xs) in
  let len_org = List.length xs in
  (len_org <> len_rem)
  

let str_contains s1 s2 =
  let re = Str.regexp_string s2 in
  try ignore (Str.search_forward re s1 0); true with Not_found -> false

