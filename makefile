.SUFFIXES : .mli .cmi .ml .cmo
CAMLC=ocamlc
CAMLLEX=ocamllex
CAMLYACC=ocamlyacc -v

all: propnt

propnt : prop_def.cmo  prop_parser.cmo prop_lexer.cmo main.cmo
	$(CAMLC) -o am prop_def.cmo   prop_lexer.cmo prop_parser.cmo main.cmo

prop_parser.ml prop_parser.mli: prop_parser.mly
	$(CAMLYACC) prop_parser.mly

prop_lexer.ml: prop_lexer.mll
	$(CAMLLEX) prop_lexer.mll

prop_def.cmo prop_def.cmi: prop_def.ml
	$(CAMLC) -c  prop_def.ml

 

prop_lexer.cmo: prop_lexer.ml prop_parser.cmi prop_def.cmi
	$(CAMLC) -c prop_lexer.ml

prop_parser.cmo: prop_parser.ml prop_parser.cmi prop_def.cmi
	$(CAMLC) -c prop_parser.ml

prop_parser.cmi: prop_parser.mli prop_def.cmi
	$(CAMLC) -c prop_parser.mli

main.cmo: main.ml prop_lexer.cmi prop_parser.cmi prop_def.cmi  
	$(CAMLC) -c main.ml

clean:
	rm -f prop_parser.mli
	rm -f prop_parser1.ml
	rm -f lexerLI.ml
	rm -f fl
	rm -f *.cmo
	rm -f *.cmi
