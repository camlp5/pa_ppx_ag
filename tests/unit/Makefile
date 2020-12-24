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
PACKAGES := $(PACKAGES),bos,oUnit,fmt,pcre,rresult,compiler-libs.common,sexplib0,uint,pa_ppx.utils,pa_ppx.testutils
PACKAGES := $(PACKAGES),camlp5.pa_r.link,camlp5.pr_r.link
PACKAGES := $(PACKAGES),pa_ppx_ag.parser.link,camlp5.parser_quotations,pa_ppx.deriving.link
PACKAGES := $(PACKAGES),pa_ppx.deriving_plugins.std
R_PACKAGES := $(PACKAGES)

TESTS= \
	pa_ag_test.byte \

ML=\
	pa_ag_test.ml


CMO := $(ML:.ml=.cmo)
CMI := $(ML:.ml=.cmi)
CMX := $(ML:.ml=.cmx)
CMT := $(ML:.ml=.cmt)
CMTI := $(MLI:.mli=.cmti)

all test: $(TESTS)  $(TESTS:.byte=)

% : %.opt
	mkdir -p _build && ./$<

pa_ag_test.byte: pa_ag_test.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) -package $(PACKAGES) \
	-linkpkg -linkall -syntax camlp5r $^ -o $@

pa_ag_test.opt: pa_ag_test.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) -package $(PACKAGES) \
	-linkpkg -linkall -syntax camlp5r $^ -o $@

clean::
	rm -f  *.ppo.*

EXTERNAL := $(shell $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)

depend::
	echo "$(CMO) $(CMI) $(CMX): $(EXTERNAL)" > .depend.NEW
	$(OCAMLFIND) ocamldep $(OCAMLCFLAGS) $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5r \
	pa_ag_test.ml \
	>> .depend.NEW
	mv .depend.NEW .depend

-include .depend
