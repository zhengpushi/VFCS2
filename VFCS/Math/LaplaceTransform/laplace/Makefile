# ===================================================================
# Copyright 2024 Zhengpu Shi
#  This file is part of VFCS. It is distributed under the MIT
#  "expat license". You should have recieved a LICENSE file with it.
# ===================================================================

COQMAKEFILE ?= Makefile.coq

all: $(COQMAKEFILE)
	$(MAKE) -f $^ $@

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall

cleanall: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall
	$(RM) $^ $^.conf

.PHONY: all clean cleanall

