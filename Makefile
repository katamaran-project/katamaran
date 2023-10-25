# Always run with nproc jobs by default. Can be overridden by the user.
MAKEFLAGS := --jobs=$(shell nproc)

# Comment out the below line if you want to be quiet by default.
VERBOSE ?= 1
ifeq ($(V),1)
E=@true
Q=
else
E=@echo
Q=@
MAKEFLAGS += -s
endif

SRCS := $(shell egrep "^.*\.v$$" _CoqProject)
AUXS := $(join $(dir $(SRCS)), $(addprefix ., $(notdir $(SRCS:.v=.aux))))

.PHONY: coq clean summaxlen install uninstall pretty-timed make-pretty-timed-before make-pretty-timed-after print-pretty-timed-diff

coq: Makefile.coq
	$(E) "MAKE Makefile.coq"
	$(Q)$(MAKE) -f Makefile.coq

patch:
	$(Q) patch -p1 -N -r - < case_study/patches/RiscvPmp/duplicate_add.patch || true
	$(Q) patch -p1 -N -r - < case_study/patches/MinimalCaps/duplicate_add.patch || true

unpatch:
	$(Q) patch -p1 -NR -r - < case_study/patches/RiscvPmp/duplicate_add.patch || true
	$(Q) patch -p1 -NR -r - < case_study/patches/MinimalCaps/duplicate_add.patch || true

Makefile.coq: _CoqProject Makefile $(SRCS)
	$(E) "COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq clean
	$(Q)rm -f $(AUXS)
	$(Q)rm -f Makefile.coq *.bak *.d *.glob *~ result*

install uninstall pretty-timed make-pretty-timed-before make-pretty-timed-after print-pretty-timed-diff: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq $@

summaxlen: Makefile.coq
	$(Q)rm -f test/SumMaxLen.vo*
	$(Q)$(MAKE) -f Makefile.coq test/SumMaxLen.vo

linkedlist: Makefile.coq
	$(Q)rm -f test/LinkedList.vo*
	$(Q)$(MAKE) -f Makefile.coq test/LinkedList.vo

timings: Makefile.coq
	$(Q)rm -f case_study/MinimalCaps/Contracts.vo*
	$(Q)rm -f test/SumMaxLen.vo*
	$(Q)rm -f test/LinkedList.vo*
	$(Q)$(MAKE) -f Makefile.coq test/LinkedList.vo test/SumMaxLen.vo case_study/MinimalCaps/Contracts.vo | ts '%.s' | scripts/timing.sh

Makefile2.coq: _CoqProject Makefile $(SRCS) case_study/MinimalCaps/Shallow.v
	$(E) "COQ_MAKEFILE Makefile2.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile2.coq case_study/MinimalCaps/Shallow.v

minimalcaps: Makefile2.coq
	$(Q)rm -f case_study/MinimalCaps/Contracts.vo*
	$(Q)$(MAKE) -f Makefile.coq case_study/MinimalCaps/Contracts.vo
	$(Q)rm -f case_study/MinimalCaps/Shallow.vo*
	$(Q)$(MAKE) -f Makefile2.coq case_study/MinimalCaps/Shallow.vo | tr -s '[:space:]' '[\n*]' | scripts/shallow.sh

assumptions: Makefile.coq
	$(Q)rm -f case_study/Assumptions.vo*
	$(Q)$(MAKE) -f Makefile.coq case_study/Assumptions.vo

count-loc:
	$(Q)./scripts/count-loc.sh
