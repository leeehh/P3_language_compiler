DIRS = driver util validator lib parser extraction

INCLUDES = $(patsubst %,-I %, $(DIRS))

COQC = coqc -q $(INCLUDES)
COQTOP = coqtop $(INCLUDES) -batch -load-vernac-source

OCAMLBUILD = ocamlbuild
OCAMLBUILD_OPTIONS = \
  -j 2 \
  -libs unix,str \
  $(INCLUDES)

all:
	$(MAKE) validator
	$(MAKE) library
	$(MAKE) parser
	$(MAKE) extraction
	$(MAKE) compiler

fast:
	$(MAKE) parser
	$(MAKE) extraction
	$(MAKE) compiler

.PHONY: validator library parser extraction compiler

validator:
	coqc -I validator validator/Alphabet.v
	coqc -I validator validator/Tuples.v
	coqc -I validator validator/Grammar.v
	coqc -I validator validator/Automaton.v
	coqc -I validator validator/Validator_safe.v
	coqc -I validator validator/Validator_complete.v
	coqc -I validator validator/Interpreter.v
	coqc -I validator validator/Interpreter_correct.v
	coqc -I validator validator/Interpreter_complete.v
	coqc -I validator validator/Interpreter_safe.v
	coqc -I validator validator/Main.v

library:
	coqc -I lib lib/Coqlib.v
	coqc -I lib lib/Integers.v

parser:
	ocamllex parser/Lexer.mll
	menhir --coq parser/Parser.vy
	$(COQC) parser/Tree.v
	$(COQC) parser/Parser.v
	$(COQC) parser/Tokenizer.v

extraction:
	$(COQTOP) extraction/Extraction.v
	mv parser/Lexer.ml extraction

Version.ml:
	@echo "let version_info = \"\\" > $@
	@echo "P3C: P3 Language to Configuration Compiler." >> $@
	@echo "Made by: Shengyuan Wang, Huanghua Li, Ling Li." >> $@
	@echo "Built on: `date +'%Y%m%d %H:%M:%S %z'`." >> $@
	@echo "Built by: `id -un`@`hostname`." >> $@
	@echo "" >> $@
	@echo "\";;" >> $@
	@echo "" >> $@


compiler: Version.ml
	$(OCAMLBUILD) $(OCAMLBUILD_OPTIONS) Driver.native
	rm -f Driver.native
	cp _build/driver/Driver.native p3c

clean:
	rm -f lib/*.vo lib/*.glob
	rm -f parser/*.vo parser/*.glob
	rm -f parser/Lexer.ml parser/Parser.v parser/Parser.conflicts
	rm -f validator/*.vo validator/*.glob
	rm -f extraction/*.ml extraction/*.mli
	rm -rf _build/
	rm -f Driver.native p3c