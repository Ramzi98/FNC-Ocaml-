open Prop_def;;
open List;;
open Prop_lexer;;



let rec fnc p = match p with
|Var x -> Var x ;

|Vrai->Vrai;
|Faux->Faux;
|NEG Vrai->Faux;
|NEG Faux->Vrai;


|EQUIV(x,y)->fnc (ET(IMPLIQ(x,y),IMPLIQ(y,x)));
|NEG EQUIV(x,y)->fnc (NEG (ET(IMPLIQ(x,y),IMPLIQ(y,x))));

|IMPLIQ(x,ET(y,z))->fnc (OU(NEG x,ET(y,z)));
|IMPLIQ(ET(x,y),z)->fnc (OU(NEG x,OU(NEG y,z)));
|IMPLIQ(x,OU(y,z))->fnc (OU(NEG x,OU(y,z)));
|IMPLIQ(OU(x,y),z)->fnc (ET(OU(NEG x,z),OU(NEG y,z)));
|NEG OU(IMPLIQ(x,y),z)->fnc (ET(OU(x,z),OU(NEG y,z)));

|NEG NEG x -> fnc x;
|NEG ET(x,y) -> fnc (OU(NEG x,NEG y));
|NEG OU(x,y) -> fnc (ET(NEG x,NEG y));
|NEG IMPLIQ(x,y)-> fnc (ET(x,NEG y));


|OU(ET(x,y),z)-> fnc (ET(OU(x,z),OU(y,z)));
|OU(x,ET(y,z))-> fnc (ET(OU(x,y),OU(x,z)));
|OU(z,NEG IMPLIQ (x,y)) ->fnc(ET(OU(z,x),OU(z,NEG y)));
|OU(NEG IMPLIQ(x,y),z) -> fnc (ET(OU(x,z),OU(NEG y,z)));
|OU(NEG OU(x,y),z)->fnc (ET(OU(NEG x,z),OU(NEG y,z)));
|OU(x,NEG OU(y,z))->fnc (ET(OU(NEG x,z),OU(NEG y,z)));

|IMPLIQ(x,y)-> fnc(OU(fnc(NEG x), fnc y));
|OU(x,y) -> if (x=y) then fnc (NEG(NEG x))
			else (OU(fnc x,fnc y));			 
|ET(x,y) -> if (x=y) then fnc (NEG(NEG x))
			else ET(fnc x,fnc y);             
|NEG x   -> NEG(fnc  x);;


let rec choiserLiterel formule_prop :proposition = match formule_prop with
	|Var x -> Var x 
	|Vrai ->  Vrai 
	|Faux  ->  Faux 
	|NEG NEG x -> choiserLiterel (x)
	|NEG IMPLIQ (x,y) -> choiserLiterel (ET(x,NEG y)) 
	|NEG OU (x,y) -> choiserLiterel (ET(NEG x,NEG y)) 
	|NEG ET (x,y) -> choiserLiterel (OU(NEG x,NEG y)) 
	|OU(ET(x,y),c) -> choiserLiterel (ET(OU(x,c),OU(y,c)))	             	
	|OU(x,ET(y,c)) -> choiserLiterel (ET(OU(x,y),OU(x,c)))	             	
	|OU(Var x,y) -> Var x 
	|OU(x,y) ->   if((choiserLiterel x = Vrai) || (choiserLiterel x = Faux)) then choiserLiterel y else choiserLiterel x
	|ET(x,y)      ->  if((choiserLiterel x = Vrai) || (choiserLiterel x = Faux)) then choiserLiterel y else choiserLiterel x
	|IMPLIQ(x,y) -> choiserLiterel (OU(NEG x,y))
	|EQUIV(x,y) -> choiserLiterel (ET(IMPLIQ(x,y),IMPLIQ(y,x)))
	|NEG x  ->  (choiserLiterel x) 
	;;

let rec subt f element boolien = match f with
	| Var x  when Var(x) = element ->  boolien 
	| ET(x,Vrai) -> x
	| ET(Vrai,x) -> x
	| ET(x,Faux) -> Faux
	| ET(Faux,x) -> Faux
	| OU(_,Vrai) -> Vrai
	| OU(Vrai,_) -> Vrai
	| OU(x,Faux) -> x
	| OU(Faux,x) -> x
	| ET(x,y)  -> ET((subt x element boolien),(subt y element boolien))
	| OU(x,y)  -> OU((subt x element boolien),(subt y element boolien))
	| NEG Vrai -> Faux
	| NEG Faux -> Vrai
	| NEG x -> NEG (subt x element boolien)
	|_ -> f
	;; 


let rec tautologie l = match l with
	| [] -> true
	| Vrai::l -> tautologie l
	| _::x -> false
	;;

let rec contradiction l = match l with
	| [] -> true
	| Faux::l -> contradiction l
	| _::x -> false
	;;

let find (l) = match l with
	| l when (tautologie l) -> print_string "Cette formule est :Tautologie"
	| l when (contradiction l) -> print_string "cette formule est :Contradiction"
	| _ -> print_string "Cette formule est :Satisfaisable"
	;;

let rec df f = 
	let formule_prop = fnc f in 
		if formule_prop = Vrai then [Vrai]
		else if f = Faux then [Faux]
		else
			begin
				let p = choiserLiterel formule_prop in
				let ft =(subt (formule_prop) (p) (Vrai)) in
				let fs =(subt (	formule_prop) (p) (Faux)) in
				(df ft)@(df fs) 
			end
;;		


let boucle in_channel =
let lexbuffer = Lexing.from_channel in_channel in
let lire_prop_expr () =
  Prop_parser.programme Prop_lexer.token lexbuffer in
 
	let p = lire_prop_expr () in print_string"\nfnc : "; print_term (fnc p); print_string"\n\n"; find (df p); print_string"\n";;


boucle stdin;;



