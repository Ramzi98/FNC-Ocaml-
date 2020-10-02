%{
open Prop_def;;
%}


%token ET OU IMPLIQ EQUIV NEG  LPAR RPAR  QUIT Vrai Faux
%token <string> VAR
%token EOF
%right IMPLIQ
%right EQUIV
%left ET
%left OU
%nonassoc NEG
%start programme
%type <Prop_def.proposition> programme 
%%

programme   : proplog      EOF                    {$1};

proplog:
       	 VAR					{Var ($1)}
         | Vrai                                  {Vrai}
         | Faux                                 { Faux}
	| NEG proplog				{(NEG ($2))}
	| LPAR NEG proplog RPAR			{(NEG ($3))}
	| proplog IMPLIQ proplog    		{(IMPLIQ ($1,$3))}
	| LPAR proplog IMPLIQ  proplog RPAR   	{(IMPLIQ ($2,$4))}

	| proplog EQUIV proplog				{(EQUIV($1,$3) )}
	| LPAR proplog EQUIV  proplog RPAR   	{(EQUIV ($2,$4) )}

	| proplog ET proplog      		{(ET ($1,$3))}
	| LPAR proplog ET proplog RPAR   	{(ET ($2,$4))}
	| proplog OU proplog 			{(OU ($1,$3))}
	| LPAR proplog OU proplog RPAR 		{(OU ($2,$4))}

;
