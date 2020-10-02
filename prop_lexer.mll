{
open Prop_def
open Prop_parser
}
rule token = parse
	 [' ' '\t']		          { token lexbuf}
	| '\n'			          { incr lines;EOF} 
        | "->"			          { incr words;IMPLIQ} 
        | "<=>"					  {incr words;EQUIV}	
	| "#"		                  { incr words;OU}
	| "&"		                  { incr words;ET}
	| "~"			          { incr words; NEG}
       
       	| "("                             {incr words; LPAR}
	| "Quit."		          { incr words;QUIT}
        | "TT"                             { incr words; Vrai}
        | "FF"                             {incr words ; Faux}
        | ")"                             {incr words; RPAR} 
	| ['a'-'f''h'-'z' 'A'-'F''H'-'Z''/']* '\''*{ let nom = Lexing.lexeme lexbuf in
				                                        incr words;
				                                      VAR nom}
	| "(*"			          { comment lexbuf}
 
	| _			          { raise LexError  }

and comment = parse
	  "*)"			          { token lexbuf}
	| '\n'			          { incr words;EOF}
	| _			          { comment lexbuf}
