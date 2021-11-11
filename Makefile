SHELL      := bash
COQC       := coqc
COQDEP     := coqdep
COQ_FLAGS  := $(shell cat _CoqProject)
COQ_SRC    := $(sort $(shell find src -iname '*.v'))

.PHONY: all
all: proofs

.PHONY: proofs
proofs: $(COQ_SRC:.v=.vo)
	if fgrep -inH 'admit' $(COQ_SRC); then exit 1; fi

.PHONY: clean
clean:
	$(RM) $(COQ_DEPFILES)
	$(RM) $(COQ_SRC:.v=.vo)
	$(RM) $(COQ_SRC:.v=.vos)
	$(RM) $(COQ_SRC:.v=.vok)
	$(RM) $(COQ_SRC:.v=.glob)
	$(RM) .lia.cache

COQ_DEPFILES = $(COQ_SRC:.v=.d)
include $(COQ_DEPFILES)
$(COQ_DEPFILES): %.d: %.v _CoqProject
	$(COQDEP) $(COQ_FLAGS) $< >'$@.tmp'
	mv '$@.tmp' '$@'

$(COQ_SRC:.v=.vo): %.vo: %.v _CoqProject
	$(COQC) $(COQ_FLAGS) $<
