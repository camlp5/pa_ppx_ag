A PPX Rewriter that Generates Attribute Grammar Evaulators

### Version

This is ``pa_ppx_ag`` (alpha) version 0.07.

# Overview

Does what it says on the tin.

Initially, only ordered AGs, but eventually other strategies.

Initially, only simple productions and simple attributes (no
aggregates) but eventually, more fancy stuff.

# Installation

For now, I'll just list commands to allow installation from Github,
until all of this code is released via opam.  The following commands
assume that camlp5 and the pa_ppx* packages are *not* installed.

```
opam pin remove camlp5 pa_ppx
opam pin remove pa_ppx_{migrate,hashcons,unique,q_ast}
opam pin -y -n add camlp5 https://github.com/camlp5/camlp5.git
opam pin -y -n add pa_ppx https://github.com/camlp5/pa_ppx.git
opam pin -y -n add pa_ppx_migrate https://github.com/camlp5/pa_ppx_migrate.git
opam pin -y -n add pa_ppx_hashcons https://github.com/camlp5/pa_ppx_hashcons.git
opam pin -y -n add pa_ppx_unique https://github.com/camlp5/pa_ppx_unique.git
opam pin -y -n add pa_ppx_q_ast https://github.com/camlp5/pa_ppx_q_ast.git
opam pin -y -n add pa_ppx_ag https://github.com/camlp5/pa_ppx_ag.git
opam install -y -t pa_ppx_ag
```
