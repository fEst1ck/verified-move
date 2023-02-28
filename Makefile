MODULES := utility name type value memory instr resources
VS := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . Resources $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq