#!/usr/bin/env perl

use strict ;
BEGIN { push (@INC, "..") }
use Version ;

our $destdir = shift @ARGV ;

print <<"EOF";
# Specifications for the "pa_ppx_ag" preprocessor:
version = "$Version::version"
description = "pa_ppx_ag deriver"

  package "runtime" (
    archive(byte) = "pa_ppx_ag_runtime.cmo"
    archive(native) = "pa_ppx_ag_runtime.cmx"
  )

  package "parser" (
  version = "$Version::version"
  description = "syntax extension for writing AGs"

  requires(toploop) = "camlp5,pa_ppx,pa_ppx_ag"
  archive(toploop)      = "pa_ag.cmo"

  requires(syntax,preprocessor) = "camlp5,pa_ppx,pa_ppx_ag"
  archive(syntax,preprocessor,-native) = "pa_ag.cmo"
  archive(syntax,preprocessor,native) = "pa_ag.cmx"
  requires = "camlp5"

  package "link" (
    requires = "camlp5,pa_ppx.base.link,pa_ppx_ag.link"
    archive(byte) = "pa_ag.cmo"
    archive(native) = "pa_ag.cmx"
  )
  )

  package "parser_debug" (
  version = "$Version::version"
  description = "syntax extension for writing AGs"

  requires(toploop) = "camlp5,pa_ppx,ocamlgraph,vec"
  archive(toploop)      = "camlp5_migrate.cmo ag_types.cmo pa_ag.cmo"

  requires(syntax,preprocessor) = "camlp5,pa_ppx,ocamlgraph,vec"
  archive(syntax,preprocessor,-native) = "camlp5_migrate.cmo ag_types.cmo pa_ag.cmo"
  archive(syntax,preprocessor,native) = "camlp5_migrate.cmx ag_types.cmx pa_ag.cmx"
  requires = "camlp5"

  package "link" (
    requires = "camlp5,pa_ppx.base.link,ocamlgraph,vec"
    archive(byte) = "camlp5_migrate.cmo ag_types.cmo pa_ag.cmo"
    archive(native) = "camlp5_migrate.cmx ag_types.cmx pa_ag.cmx"
  )
  )

  requires(toploop) = "camlp5,pa_ppx.deriving_plugins.show,pa_ppx.params_runtime,pa_ppx_unique,pa_ppx_migrate,ocamlgraph,vec"
  archive(toploop) = "camlp5_migrate.cmo ag_types.cmo ag_tsort.cmo ag_ordered.cmo pa_deriving_attributed.cmo pa_deriving_ag.cmo"

    requires(syntax,preprocessor) = "camlp5,pa_ppx.deriving_plugins.show,pa_ppx.params_runtime,pa_ppx_unique,pa_ppx_migrate,ocamlgraph,vec"
    archive(syntax,preprocessor,-native) = "camlp5_migrate.cmo ag_types.cmo ag_tsort.cmo ag_ordered.cmo pa_deriving_attributed.cmo pa_deriving_ag.cmo"
    archive(syntax,preprocessor,native) = "camlp5_migrate.cmx ag_types.cmx ag_tsort.cmx ag_ordered.cmx pa_deriving_attributed.cmx pa_deriving_ag.cmx"

  package "link" (
  requires = "camlp5,pa_ppx.deriving_plugins.show.link,pa_ppx.params_runtime,pa_ppx_unique.link,pa_ppx_migrate.link,ocamlgraph,vec"
  archive(byte) = "camlp5_migrate.cmo ag_types.cmo ag_tsort.cmo ag_ordered.cmo pa_deriving_attributed.cmo pa_deriving_ag.cmo"
  archive(native) = "camlp5_migrate.cmx ag_types.cmx ag_tsort.cmx ag_ordered.cmx pa_deriving_attributed.cmx pa_deriving_ag.cmx"
  )

EOF
