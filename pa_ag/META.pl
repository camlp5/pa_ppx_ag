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

  requires(toploop) = "camlp5,pa_ppx.deriving_plugins.show,pa_ppx.params_runtime"
  archive(toploop) = "camlp5_migrate.cmo ag_types.cmo ag_tsort.cmo pa_deriving_ag.cmo"

    requires(syntax,preprocessor) = "camlp5,pa_ppx.deriving_plugins.show,pa_ppx.params_runtime"
    archive(syntax,preprocessor,-native) = "camlp5_migrate.cmo ag_types.cmo ag_tsort.cmo pa_deriving_ag.cmo"
    archive(syntax,preprocessor,native) = "camlp5_migrate.cmx ag_types.cmx ag_tsort.cmx pa_deriving_ag.cmx"

  package "link" (
  requires(byte) = "camlp5,pa_ppx.deriving_plugins.show.link,pa_ppx.params_runtime"
  archive(byte) = "camlp5_migrate.cmo ag_types.cmo ag_tsort.cmo pa_deriving_ag.cmo"
  )

EOF
