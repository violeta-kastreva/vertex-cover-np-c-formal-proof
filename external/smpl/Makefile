.PHONY: all clean 
COQMAKEFILE := Makefile.coq
ifneq "$(COQBIN)" ""
  COQBIN := $(COQBIN)/
endif

all: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) $@

clean:
	-$(MAKE) -f $(COQMAKEFILE) clean
	rm -f $(COQMAKEFILE)

$(COQMAKEFILE): Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

%:
	-$(MAKE) -f $(COQMAKEFILE) $@
