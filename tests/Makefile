# Makefile,v
# Copyright (c) INRIA 2007-2017

WD=$(shell pwd)
TOP=..
include $(TOP)/config/Makefile

DESTDIR=
RM=rm

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
MKCAMLP5=$(LAUNCH) mkcamlp5
PACKAGES := $(PACKAGES),ounit2,fmt,pcre,rresult,compiler-libs.common,sexplib,uint,pa_ppx.utils
PACKAGES := $(PACKAGES),pa_ppx_ag,pa_ppx_ag.runtime,pa_ppx_migrate,pa_ppx_hashcons,pa_ppx_unique
SYNTAX := camlp5o
OCAMLCFLAGS += -ppopt -pa_passthru-debug 
IMPORT_OCAMLCFLAGS = -ppopt -pa_import-package -ppopt camlp5
IMPORT_OCAMLCFLAGS += -ppopt -pa_import-I -ppopt .

TESTS= \
	test1_ag.byte \

ML=\
	test1_ast.ml test1_variants.ml test1_migrate.ml test1_pa.ml test1_ag.ml


CMO := $(ML:.ml=.cmo)
CMI := $(ML:.ml=.cmi)
CMX := $(ML:.ml=.cmx)
CMT := $(ML:.ml=.cmt)
CMTI := $(MLI:.mli=.cmti)

all: $(TESTS)

test: $(TESTS:.byte=)

% : %.opt
	mkdir -p _build && ./$<

test1_ag.byte: test1_ast.cmo test1_variants.cmo test1_migrate.cmo test1_pa.cmo test1_ag.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) -package $(PACKAGES) \
	-linkpkg -syntax camlp5o $^ -o $@

test1_ag.opt: test1_ast.cmx test1_variants.cmx test1_migrate.cmx test1_pa.cmx test1_ag.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) -package $(PACKAGES) \
	-linkpkg -syntax camlp5o $^ -o $@

clean::
	rm -f  *.ppo.*

EXTERNAL := $(shell $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)
$(CMO): $(EXTERNAL)

depend::
	echo "$(CMO): $(EXTERNAL)" > .depend.NEW
	$(OCAMLFIND) ocamldep $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5o \
	*.ml \
	>> .depend.NEW
	mv .depend.NEW .depend

-include .depend

test1_pa.cmo: test1_pa.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend -syntax camlp5r -c $<

test1_pa.cmx: test1_pa.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.extend -syntax camlp5r -c $<

.ml.cmo:
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -ppopt -sep -ppopt ";;\n" -package $(PACKAGES),pa_ppx.import,camlp5.pr_o -syntax $(SYNTAX) $< > $@.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $@.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $<

.ml.cmx:
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $<
