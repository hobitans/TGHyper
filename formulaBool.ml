
open Functions

let verbose = ref true 

type boolformula = 
    BTrue
  | BFalse
  | BVar of string * string * int
  | BNeg of boolformula
  | BAnd of boolformula * boolformula
  | BAndList of boolformula list
  | BOr of boolformula * boolformula
  | BOrList of boolformula list
  | BEquiv of boolformula * boolformula
  | BImpl of boolformula * boolformula


(* Adapted from DQBF Formulas in MGHyper **)



  let rec str_ buf f =
    let adstr = Buffer.add_string buf in
      match f with
          | BTrue  -> adstr "True"
          | BFalse -> adstr "False"
          | BVar ( x , y, z )   -> add_var_ x y z buf
          | BNeg g -> adstr "!"; str_ buf g; adstr ""
          | BAnd (g, h) -> adstr "("; str_ buf g; adstr "&"; str_ buf h; adstr ")"
          | BOr (g, h)  -> adstr "("; str_ buf g; adstr "|"; str_ buf h; adstr ")"
          | BImpl (g, h) ->  adstr "(("; str_ buf g; adstr " )->("; str_ buf h; adstr "))"
          | BEquiv (g,h) ->  adstr "(("; str_ buf g; adstr ")<->("; str_ buf h; adstr "))"
          | BAndList (g_list) -> adstr "(";  add_BAndList g_list buf ;adstr ")"; 
          | BOrList (g_list)  -> adstr "(";  add_BOrList g_list buf ;adstr ")"; 

  and add_BAndList lst buf =
      add_BList lst " & " buf

  and add_BOrList lst buf =
      add_BList lst " | " buf

  and add_BList lst op buf =
      let length = (List.length lst)-1 in
      List.mapi (fun i elm -> ( (Buffer.add_string buf "(");
                                str_ buf elm ; 
                                (Buffer.add_string buf ")");
                                if length >  i then (Buffer.add_string buf op)
                              ))   lst 
      

  and add_var_ x y z buf =  
      let adstr = Buffer.add_string buf in
      adstr x; adstr "@";adstr y;adstr "[";adstr (string_of_int z);adstr "] "


let str f = 
    let buf = Buffer.create 0 in
    str_ buf f; 
    let str = Buffer.contents buf in 
    Buffer.reset buf ;
    str

let limbool_str formula = 
    str formula

let print_BForm f = 
    let s = str f in
    Printf.printf "%s" s





