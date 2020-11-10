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
	test1.byte test2.byte \

ML=\
	test1_ast.ml test1_variants.ml test1_migrate.ml test1_pa.ml test1_ag.ml test1.ml \
	test2_ag.ml test2_pa.ml test2_migrate.ml test2.ml


CMO := $(ML:.ml=.cmo)
CMI := $(ML:.ml=.cmi)
CMX := $(ML:.ml=.cmx)
CMT := $(ML:.ml=.cmt)
CMTI := $(MLI:.mli=.cmti)

all test: $(TESTS)  $(TESTS:.byte=)

% : %.opt
	mkdir -p _build && ./$<

test1.byte: test1_ast.cmo test1_variants.cmo test1_migrate.cmo test1_pa.cmo test1_ag.cmo test1.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

test1.opt: test1_ast.cmx test1_variants.cmx test1_migrate.cmx test1_pa.cmx test1_ag.cmx test1.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

test2.byte: test2_ag.cmo test2_migrate.cmo test2_pa.cmo test2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

test2.opt: test2_ag.cmx test2_migrate.cmx test2_pa.cmx test2.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

clean::
	rm -f  *.ppo.*

EXTERNAL := $(shell $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)
$(CMO): $(EXTERNAL)

depend::
	echo "$(CMO): $(EXTERNAL)" > .depend.NEW
	$(OCAMLFIND) ocamldep $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5o \
	test1_ast.ml test1_variants.ml test1_migrate.ml test1_ag.ml test1.ml \
	>> .depend.NEW
	$(OCAMLFIND) ocamldep $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r \
	test1_pa.ml \
	>> .depend.NEW
	mv .depend.NEW .depend

-include .depend

test1_pa.cmo: test1_pa.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

test1_pa.cmx: test1_pa.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

test2_pa.cmo: test2_pa.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

test2_pa.cmx: test2_pa.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

.ml.cmo:
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -ppopt -sep -ppopt ";;\n" -package $(PACKAGES),pa_ppx.import,camlp5.pr_o -syntax $(SYNTAX) $< > $*_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $*_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $<

.ml.cmx:
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $<
