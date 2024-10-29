COQDOCJS_DIR ?= coqdocjs
EXTRA_DIR = $(COQDOCJS_DIR)/extra
COQDOCFLAGS ?= \
  --toc --toc-depth 4 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE ?= Makefile.coq
COQDOCJS_LN ?= false

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

coqdoc: $(COQMAKEFILE)
	$(MAKE) -f $^ html

ifeq ($(COQDOCJS_LN),true)
	ln -sf ../$(EXTRA_DIR)/resources html
else
	cp -R $(EXTRA_DIR)/resources html
endif

.PHONY: coqdoc
