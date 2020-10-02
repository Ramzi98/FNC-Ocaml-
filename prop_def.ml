exception EndSession;;
exception LexError;;
exception EOF;;
type proposition = 
Vrai
  |Faux
  |Var of string 
  | ET of proposition * proposition
  | NEG of proposition 
  | OU of proposition * proposition
  |IMPLIQ of proposition * proposition
  |EQUIV of proposition * proposition
;;

type 'a arbre = 
Bin of ('a arbre *'a*'a arbre) 
|Vide;;


let lines = ref 0;;
let words = ref 0;;


let rec print_term  term =

match term with

(Var x) ->  print_string x
|Vrai ->      print_string "vrai";
|Faux  ->     print_string "faux";
|OU(x,y) ->   (
             print_string "(";
             print_term x;
             print_string "#";
             print_term y;
             print_string ")"; )
             
|ET(x,y)      ->  
             (
             print_string "("; 
             print_term x;
             print_string "&";
             print_term y;
             print_string ")"; )
             
|IMPLIQ(x,y) -> 
               (
             print_string "("; 
             print_term x;
             print_string "->";
             print_term y;
             print_string ")";
                )
|EQUIV(x,y) ->  (
             print_string "("; 
             print_term x;
             print_string "<=>";
             print_term y;
             print_string ")";
                )
             
|NEG x   -> (print_string "~"; print_term x)
;;


let print_list f lst =
  let rec print_elements = function
    | [] -> ()
    | h::t ->f h;print_string ";"; print_elements t
  in
  print_string "[";
  print_elements lst;
  print_string "]";;

let rec print_list_list l = match l with
|[] -> ()
|x::r->print_string "[";
      print_list print_string x;
      print_string ";";
      print_string "]";
      print_list_list r;;


let rec effacer x l = match l with
|[] -> []
|a::r ->if (a=x) then effacer x r else a::(effacer x r);;

let effacer_double a l = match l with
|[[]] -> []
|[x::r] -> effacer x r ;;


let fct l = match l with
|[[]] -> []
|[[x]] -> [x];;

let rec quine p = match p with
|Var x -> [[x]]
|OU(x,y) -> [fct (quine x)@fct (quine y)@[]]
|ET(x,y) -> (quine x)@(quine y);;

let rec remplacer_top l = match l with
|[]->failwith"erreur 2"
|x::r -> "Vrai"::[] ;;

let remplacer_bottom a l = match l with
|[] -> failwith"vide"
|x::r -> "Faux"::[];;


let rec first = function
    | [] -> failwith "too bad"
    | [e] -> e
    | e::r -> e;;

let rec quine1 a l = match l with
|[]->[]
|x::r ->if(List.mem a x) then remplacer_top x::(quine1 a r)
        else x::quine1 a r ;;


let rec simp l = match l with
|[] -> true
|x::r -> match x with 
          |"Vrai"::t -> true && (simp r)
          |"Faux"::f -> false && (simp r);; 





(*
let print_quine p = match p with
|OU(x,y) -> [x;y] ;

 in print_list print_term (print_quine p);;


let print_p p = match p with
(Var x) ->  print_string x

|ET(x,y)-> (print_string "[";
          print_string "["; 
          print_term x;
          print_string "]";
          print_string ";";
          print_string "["; 
          print_term y;
          print_string "]";
        print_string "]";) 
|OU(x,y)-> (print_string "["; 
          print_term x;
          print_string ";";
          print_term y;
        print_string "]"; )
;;


let fct p = let f = if(p=ET(x,y)) then [[x];[y]] 
            else [x;y];;


let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []


 *)




