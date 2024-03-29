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
IMPORT_PACKAGES := $(PACKAGES),pa_ppx.deriving,pa_ppx.deriving_plugins.std,pa_ppx.base,pa_ppx.unmatched_vala
PACKAGES := $(IMPORT_PACKAGES),pa_ppx_migrate.link,pa_ppx.deriving_plugins.params,pa_ppx.base,pa_ppx_unique.link,ocamlgraph,vec

ML=\
	imperativeTopological.ml camlp5_migrate.ml ag_types.ml ag_tsort.ml ag_ordered.ml \
	pa_deriving_attributed.ml pa_deriving_ag.ml pa_ag.ml pa_ppx_ag_runtime.ml

CMO := $(ML:.ml=.cmo)
CMI := $(ML:.ml=.cmi)
CMX := $(ML:.ml=.cmx)
CMT := $(ML:.ml=.cmt)
CMTI := $(MLI:.mli=.cmti)

all: $(CMO) $(CMX) local-install

doc: $(CMT) $(CMTI)

KITS=$(CMO)

META: META.pl
	./META.pl > META

install::
	mkdir -p $(DESTDIR)/lib
	./META.pl $(DESTDIR)/lib > META
	$(NOT_OCAMLFIND) reinstall-if-diff pa_ppx_ag -destdir $(DESTDIR)/lib META $(CMO) $(CMI) $(CMX) $(MLI:.mli=.cmi) $(KITS:.cmo=.o) $(wildcard *.cmt*)
	$(RM) -f META

local-install::
	$(MAKE) DESTDIR=$(WD)/$(TOP)/local-install/ install

clean::
	rm -rf META

IMPORT_OCAMLCFLAGS += -ppopt -pa_import-package -ppopt camlp5
camlp5_migrate.cmo: camlp5_migrate.ml
#	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(IMPORT_PACKAGES),pa_ppx.import,pa_ppx_migrate,camlp5.pr_o -syntax camlp5o $< > $@.ppo.ml
#	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(IMPORT_PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $@.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(IMPORT_PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

camlp5_migrate.cmx: camlp5_migrate.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(IMPORT_PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<


pa_ag.cmo: pa_ag.ml
#	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.deriving_plugins.std,camlp5.extend,camlp5.parser_quotations,$(PRPACKAGE) -syntax $(SYNTAX) $< > $*_ppo.ml
#	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.deriving_plugins.std,camlp5.extend,camlp5.parser_quotations -syntax $(SYNTAX) -c $*_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.deriving_plugins.std,camlp5.extend,camlp5.parser_quotations -syntax $(SYNTAX) -c $<

pa_ag.cmx: pa_ag.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.deriving_plugins.std,camlp5.extend,camlp5.parser_quotations -syntax $(SYNTAX) -c $<


EXTERNAL := $(shell $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)

depend::
	echo "$(CMO) $(CMI) $(CMX): $(EXTERNAL)" > .depend.NEW
	$(OCAMLFIND) ocamldep -package $(PACKAGES),camlp5.extend,pa_ppx.deriving_plugins.std -syntax camlp5r ag_*.ml pa_deriving_ag.ml pa_deriving_attributed.ml pa_ag.ml  >> .depend.NEW
	$(OCAMLFIND) ocamldep -package $(IMPORT_PACKAGES) -syntax camlp5o camlp5_migrate.ml  >> .depend.NEW
	mv .depend.NEW .depend

-include .depend
