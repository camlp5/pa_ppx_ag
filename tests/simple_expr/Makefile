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
PACKAGES := $(PACKAGES),oUnit,fmt,pcre,rresult,compiler-libs.common,sexplib0,uint,pa_ppx.utils,ocamlgraph
PACKAGES := $(PACKAGES),pa_ppx_ag,pa_ppx_ag.runtime,pa_ppx_migrate,pa_ppx_hashcons,pa_ppx_unique,pa_ppx.deriving_plugins.std,pa_ppx.testutils
R_PACKAGES := $(PACKAGES)
SYNTAX := camlp5o
OCAMLCFLAGS += -ppopt -pa_passthru-debug 
IMPORT_OCAMLCFLAGS = -ppopt -pa_import-package -ppopt camlp5
IMPORT_OCAMLCFLAGS += -ppopt -pa_import-I -ppopt .

TESTS= \
	test1.byte \
	test2.byte \
	kastens116.byte \
	test3.byte \
	test4.byte \
	vogt_thesis_page7.byte \
	simple1.byte \
	simple_hoag.byte \
	silver_dc.byte \
	silver_lambda_firstorder.byte \
#	simple_hoag0.byte \

ML=\
	test1_ast.ml test1_variants.ml test1_ag.ml test1_migrate.ml test1_pa.ml test1.ml \
	test2_ag.ml test2_pa.ml test2_migrate.ml test2.ml


CMO := $(ML:.ml=.cmo)
CMI := $(ML:.ml=.cmi)
CMX := $(ML:.ml=.cmx)
CMT := $(ML:.ml=.cmt)
CMTI := $(MLI:.mli=.cmti)

all test: $(TESTS)  $(TESTS:.byte=)

% : %.opt
	mkdir -p _build && ./$<

test1.byte: test1_ast.cmo test1_variants.cmo test1_ag.cmo test1_migrate.cmo test1_pa.cmo test1.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

test1.opt: test1_ast.cmx test1_variants.cmx test1_ag.cmx test1_migrate.cmx test1_pa.cmx test1.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

test2.byte: test2_ag.cmo test2_migrate.cmo test2_pa.cmo test2.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

test2.opt: test2_ag.cmx test2_migrate.cmx test2_pa.cmx test2.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) -package $(PACKAGES),camlp5.pa_o.link \
	-linkpkg -linkall -syntax camlp5o $^ -o $@

clean::
	rm -f  *ppo.*

EXTERNAL := $(shell $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)

depend::
	echo "$(CMO) $(CMI) $(CMX): $(EXTERNAL)" > .depend.NEW
	$(OCAMLFIND) ocamldep $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax camlp5o \
	test1_ast.ml test1_variants.ml test1_migrate.ml test1_ag.ml test1.ml \
	test2_ag.ml test2_migrate.ml test2.ml \
	>> .depend.NEW
	$(OCAMLFIND) ocamldep $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r \
	test1_pa.ml \
	test2_pa.ml \
	>> .depend.NEW
	mv .depend.NEW .depend

-include .depend

test1_pa.cmo: test1_pa.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

test1_pa.cmx: test1_pa.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

test2_pa.cmo: test2_pa.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

test2_pa.cmx: test2_pa.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf -syntax camlp5r -c $<

vogt_thesis_page7.byte: vogt_thesis_page7.ag
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser,camlp5.pr_r -syntax camlp5r -ppopt -impl $< > vogt_thesis_page7_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c vogt_thesis_page7_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c -ppopt -impl -impl $<
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

vogt_thesis_page7.opt: vogt_thesis_page7.ag
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@


simple_hoag.byte: simple_hoag.ag
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser,camlp5.pr_r -syntax camlp5r -ppopt -impl $< > simple_hoag_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c simple_hoag_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c -ppopt -impl -impl $<
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

simple_hoag.opt: simple_hoag.ag
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

simple_hoag0.byte: simple_hoag0.ml
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser,camlp5.pr_r -syntax camlp5o -ppopt -impl $< > simple_hoag0_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c simple_hoag0_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5o -c -ppopt -impl -impl $<
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5o -ppopt -impl -impl $< -o $@

simple_hoag0.opt: simple_hoag0.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5o -ppopt -impl -impl $< -o $@

simple1.byte: simple1.ag
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser,camlp5.pr_r -syntax camlp5r -ppopt -impl $< > simple1_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c simple1_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c -ppopt -impl -impl $<
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

simple1.opt: simple1.ag
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

kastens116.byte: kastens116.ag
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser,camlp5.pr_r -syntax camlp5r -ppopt -impl $< > kastens116_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c kastens116_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c -ppopt -impl -impl $<
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

kastens116.opt: kastens116.ag
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

test3.byte: test3.ag
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser,camlp5.pr_r -syntax camlp5r -ppopt -impl $< > test3_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c test3_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c -ppopt -impl -impl $<
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

test3.opt: test3.ag
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

test4.byte: test4.ag
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser,camlp5.pr_r -syntax camlp5r -ppopt -impl $< > test4_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c test4_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c -ppopt -impl -impl $<
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

test4.opt: test4.ag
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

silver_dc.byte: silver_dc.ag
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser,camlp5.pr_r -syntax camlp5r -ppopt -impl $< > silver_dc_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c silver_dc_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c -ppopt -impl -impl $<
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

silver_dc.opt: silver_dc.ag
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

silver_lambda_firstorder.byte: silver_lambda_firstorder.ag
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser,camlp5.pr_r -syntax camlp5r -ppopt -impl $< > silver_lambda_firstorder_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c silver_lambda_firstorder_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -syntax camlp5r -c -ppopt -impl -impl $<
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

silver_lambda_firstorder.opt: silver_lambda_firstorder.ag
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) -package $(R_PACKAGES),camlp5.extend,camlp5.extprint,camlp5.pprintf,pa_ppx_ag.parser -linkpkg -linkall -syntax camlp5r -ppopt -impl -impl $< -o $@

.ml.cmo:
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -ppopt -sep -ppopt ";;\n" -package $(PACKAGES),pa_ppx.import,camlp5.pr_o -syntax $(SYNTAX) $< > $*_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $*_ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $<

.ml.cmx:
	$(OCAMLFIND) ocamlopt $(DEBUG) $(WARNERR) $(OCAMLCFLAGS) $(IMPORT_OCAMLCFLAGS) -package $(PACKAGES),pa_ppx.import -syntax $(SYNTAX) -c $<
