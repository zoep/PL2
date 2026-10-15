ROCQDOCJS_DIR ?= ../../rocqdocjs
EXTRA_DIR = $(ROCQDOCJS_DIR)/extra

COQDOCEXTRAFLAGS ?= \
  --table-of-contents --toc-depth 4 \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(abspath $(EXTRA_DIR)/header.html) \
  --with-footer $(abspath $(EXTRA_DIR)/footer.html)
export COQDOCEXTRAFLAGS

ROCQMAKEFILE ?= RocqMakefile
ROCQDOCJS_LN ?= false

.DEFAULT_GOAL := invoke-coqmakefile

clean: $(ROCQMAKEFILE)
	@+$(MAKE) -f $(ROCQMAKEFILE) cleanall
	@rm -f $(ROCQMAKEFILE) $(ROCQMAKEFILE).conf

$(ROCQMAKEFILE): _RocqProject
	rocq makefile -f _RocqProject -o $(ROCQMAKEFILE)

invoke-coqmakefile: $(ROCQMAKEFILE)
	$(MAKE) -f $^

coqdoc: $(ROCQMAKEFILE)
	$(MAKE) -f $^ html
	@rm -rf html/resources
ifeq ($(ROCQDOCJS_LN),true)
	ln -s "$(abspath $(EXTRA_DIR)/resources)" html/resources
else
	cp -R $(EXTRA_DIR)/resources html/
endif

.PHONY: invoke-coqmakefile coqdoc clean
