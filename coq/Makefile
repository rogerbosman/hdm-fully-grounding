COQPROJECT_EXISTS=$(wildcard _CoqProject)

ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

vos: vos-Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

vos-Makefile.coq: _CoqProject
	coq_makefile -arg -vos -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq

.PHONY: default clean
