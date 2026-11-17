# Keep the generated dependency graph out of version control.
.DEFAULT_GOAL := all
.PHONY: all clean check check-sources assumptions

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -docroot Accumulation -o Makefile.coq

all: Makefile.coq
	+$(MAKE) -f Makefile.coq all

check: all check-sources
	coqchk -silent -Q . Accumulation -Q RegLang RegLang Accumulation.audit Accumulation.examples Accumulation.certification_examples Accumulation.copying_examples Accumulation.residual_certification_examples Accumulation.accumulation_examples

check-sources:
	python3 check_sources.py

assumptions: all
	coqc -Q . Accumulation -Q RegLang RegLang audit.v

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq clean
