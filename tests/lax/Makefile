# Makefile,v
# Copyright (c) INRIA 2007-2017

WD=$(shell pwd)
TOP=../..
include $(TOP)/config/Makefile

DESTDIR=
RM=rm

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
MKCAMLP5=$(LAUNCH) mkcamlp5
PACKAGES := $(PACKAGES),ounit2,fmt,pcre,rresult,compiler-libs.common,sexplib,uint,pa_ppx.utils,ocamlgraph
PACKAGES := $(PACKAGES),pa_ppx_ag,pa_ppx_ag.runtime,pa_ppx_migrate,pa_ppx_hashcons,pa_ppx_unique
SYNTAX := camlp5o
OCAMLCFLAGS += -ppopt -pa_passthru-debug 
IMPORT_OCAMLCFLAGS = -ppopt -pa_import-package -ppopt camlp5
IMPORT_OCAMLCFLAGS += -ppopt -pa_import-I -ppopt .

TESTS= \

ML=\
	lax_ast.ml # lax_variants.ml lax_migrate.ml lax_pa.ml lax_ag.ml lax_tests.ml


CMO := $(ML:.ml=.cmo)
CMI := $(ML:.ml=.cmi)
CMX := $(ML:.ml=.cmx)
CMT := $(ML:.ml=.cmt)
CMTI := $(MLI:.mli=.cmti)

all test: $(TESTS)  $(TESTS:.byte=)

% : %.opt
	mkdir -p _build && ./$<

lax_tests.byte: lax_ast.cmo lax_variants.cmo lax_migrate.cmo lax_pa.cmo lax_ag.cmo lax_tests.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

lax_tests.opt: lax_ast.cmx lax_variants.cmx lax_migrate.cmx lax_pa.cmx lax_ag.cmx lax_tests.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

clean::
	rm -f  *.ppo.*

EXTERNAL := $(shell $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)

depend::
	echo "$(CMO) $(CMI) $(CMX): $(EXTERNAL)" > .depend.NEW
	$(OCAMLFIND) ocamldep $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5o \
	lax_ast.ml lax_variants.ml lax_migrate.ml lax_ag.ml \
	>> .depend.NEW
	$(OCAMLFIND) ocamldep $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r \
	lax_pa.ml \
	>> .depend.NEW
	mv .depend.NEW .depend

-include .depend

lax_pa.cmo: lax_pa.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

lax_pa.cmx: lax_pa.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

.ml.cmo:
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -ppopt -sep -ppopt ";;\n" -package $(PACKAGES),pa_ppx.import,camlp5.pr_o -syntax $(SYNTAX) $< > $*_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $*_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $<

.ml.cmx:
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $<
