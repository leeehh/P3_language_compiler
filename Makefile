# Makefile of L2C Compiler

MAJOR_VERSION=0
MINOR_VERSION=9

FLOCQDIR = compcert/flocq

DIRS=compcert/lib compcert/common compcert/ia32 compcert driver util \
  $(FLOCQDIR)/Core $(FLOCQDIR)/Prop $(FLOCQDIR)/Calc $(FLOCQDIR)/Appli parser validator translator typing


INCLUDES=$(patsubst %,-I %, $(DIRS))

COQC=coqc -q $(INCLUDES)
COQDEP=coqdep $(INCLUDES)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source
COQCHK=coqchk $(INCLUDES)

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -libs unix,str \
  -I extraction $(INCLUDES)

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq
FLOCQ_CORE=Fcore_float_prop.v Fcore_Zaux.v Fcore_rnd_ne.v Fcore_FTZ.v \
  Fcore_FLT.v Fcore_defs.v Fcore_Raux.v Fcore_ulp.v Fcore_rnd.v Fcore_FLX.v \
  Fcore_FIX.v Fcore_digits.v Fcore_generic_fmt.v Fcore.v
FLOCQ_PROP=Fprop_Sterbenz.v Fprop_mult_error.v Fprop_relative.v \
  Fprop_div_sqrt_error.v Fprop_plus_error.v
FLOCQ_CALC=Fcalc_ops.v Fcalc_bracket.v Fcalc_sqrt.v Fcalc_div.v Fcalc_round.v \
  Fcalc_digits.v
FLOCQ_APPLI=Fappli_rnd_odd.v Fappli_IEEE_bits.v Fappli_IEEE.v
FLOCQ=$(FLOCQ_CORE) $(FLOCQ_PROP) $(FLOCQ_CALC) $(FLOCQ_APPLI)

LIB=Axioms.v Coqlib.v Intv.v Maps.v Integers.v Floats.v Fappli_IEEE_extra.v

COMMON=Errors.v AST.v Events.v Globalenvs.v Memdata.v Memtype.v Memory.v Values.v Smallstep.v

ARCH=Archi.v

EXTRACTION=Extraction.v

PARSERVALID= Alphabet.v Tuples.v Grammar.v Automaton.v Validator_safe.v Validator_complete.v \
  Interpreter.v Interpreter_correct.v Interpreter_complete.v Interpreter_safe.v Main.v

DRIVER=Tree.v

TRANSLATOR=Asm.v AsmGen.v Extractor.v TransUtil.v TransProtoInfo.v TransLayerBlock.v TransPin.v \
	TransLayerStatement.v TransExpression.v TransCellAlpha.v TransCellZero.v TransCellOne.v TransBranchInfo.v TransProtoStatement.v

TYPECHECKER=Types.v Typetest.v Typing.v

FILES=$(LIB) $(COMMON) $(ARCH) $(PARSERVALID) $(DRIVER) $(FLOCQ) $(TRANSLATOR) $(TYPECHECKER)

OUTPUT=p3c

all:
	$(MAKE) pre
	$(MAKE) depend
	$(MAKE) proof
	$(MAKE) coqparser
	$(MAKE) extraction
	$(MAKE) afterwork
	$(MAKE) compiler

.PHONY: pre coqparser proof extraction compiler test install uninstall clean clean-all

documentation: doc/coq2html $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

doc/coq2html: doc/coq2html.ml
	ocamlopt -w +a-29 -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex -q doc/coq2html.mll

pre:
	@rm -rf Version.ml

proof: $(FILES:.v=.vo)

.SUFFIXES: .v .vo

.v.vo:
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

depend: $(FILES)
	@$(COQDEP) $^ > .depend

-include .depend

coqparser:
	menhir --coq parser/Parser.vy
	$(COQC) parser/Parser.v
	$(COQC) parser/Tokenizer.v
	ocamllex parser/Lexer.mll

extraction:
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/Extraction.v

afterwork:
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
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.native \
	&& rm -f $(OUTPUT) && cp _build/driver/Driver.native $(OUTPUT)

compiler-byte: Version.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.d.native \
	&& rm -f $(OUTPUT).byte && cp _build/driver/Driver.d.native $(OUTPUT).byte

clean: lclean
	rm -fr driver/*.vo driver/*.glob
	rm -rf doc/html doc/*.glob
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o
	rm -f parser/*.vo parser/*.glob parser/Parser.v parser/Parser.conflicts
	rm -f validator/*.vo validator/*.glob
	rm -f translator/*.vo translator/*.glob

lclean:
	rm -f *.cmi *.cmo *.out *.luss *.lusst *.lusm *.c $(OUTPUT) Driver.native
	rm -f *.glob *.vo Version.ml
	rm -Rf extraction/*.ml extraction/*.mli _build

clean-all: clean
	rm -f compcert/*.vo compcert/*.glob
	rm -f compcert/common/*.vo compcert/common/*.glob
	rm -f compcert/lib/*.vo compcert/lib/*.glob compcert/ia32/*.vo 
	rm -f compcert/flocq/Appli/*.vo compcert/flocq/Calc/*.vo compcert/flocq/Core/*.vo compcert/flocq/Prop/*.vo
	rm -f .depend

# Install l2c to ~/bin
install: all
	@sh ./util/install.sh

uninstall:
	echo "uninstall ~/bin/l2c"
	rm -rf ~/bin/l2c

# Source Code Statistic
summary:
	@sh ./util/stat.sh
	@sh ./util/checkin.sh
