OCAMLBUILD=ocamlbuild
OCAMLBUILD_OPTS=-use-menhir -use-ocamlfind -menhir "menhir --explain" -pkg unix -pkg str -pkg ocamlgraph
TEST_DIR=tests
TEST_SCRIPT=run.sh
DOC_DIR=main.docdir

TARGET=main

.PHONY: all clean


all: 
	$(OCAMLBUILD) $(OCAMLBUILD_OPTS) $(TARGET).native

clean:
	rm -f $(TARGET).native *~ \#* *.dot *.png
	$(OCAMLBUILD) -clean
