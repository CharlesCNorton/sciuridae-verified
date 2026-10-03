# Build:      make            (compiles every theory listed in _CoqProject)
# Regenerate: make generate   (rebuild theories/Data/*.v from data/)
# CI check:   make check      (data in sync + build + axiom audit)
COQMF := Makefile.coq

all: $(COQMF)
	+$(MAKE) -f $(COQMF) all

$(COQMF): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMF)

generate:
	python3 tools/gen_coq.py

check-generated:
	python3 tools/gen_coq.py --check

check: check-generated all
	coqc -R theories Sciuridae theories/Assumptions.v

clean:
	if [ -f $(COQMF) ]; then $(MAKE) -f $(COQMF) cleanall; fi
	rm -f $(COQMF) $(COQMF).conf

.PHONY: all generate check-generated check clean
