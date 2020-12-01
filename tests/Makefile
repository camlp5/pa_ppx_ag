# Makefile,v
# Copyright (c) INRIA 2007-2017

TESTDIRS = simple_expr unit lax

all test:
	set -e; for i in $(TESTDIRS); do cd $$i; $(MAKE) test; cd ..; done

clean:
	set -e; for i in $(TESTDIRS); do cd $$i; $(MAKE) clean; cd ..; done

depend:
	set -e; for i in $(TESTDIRS); do cd $$i; $(MAKE) depend; cd ..; done
