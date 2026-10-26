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

SRCS := $(shell egrep '^.*\.v$$' _CoqProject | grep -v '^#')
AUXS := $(join $(dir $(SRCS)), $(addprefix ., $(notdir $(SRCS:.v=.aux))))

.PHONY: coq clean vcstats FORCE summaxlen install uninstall pretty-timed make-pretty-timed-before make-pretty-timed-after print-pretty-timed-diff

coq: Makefile.coq
	$(E) "MAKE Makefile.coq"
	$(Q)$(MAKE) -f Makefile.coq

patch:
	$(Q) patch -p1 -N -r - < case_study/patches/RiscvPmp/duplicate_add.patch || true
	$(Q) patch -p1 -N -r - < case_study/patches/RiscvPmpBoundedInts/duplicate_add.patch || true
	$(Q) patch -p1 -N -r - < case_study/patches/MinimalCaps/duplicate_add.patch || true

unpatch:
	$(Q) patch -p1 -NR -r - < case_study/patches/RiscvPmp/duplicate_add.patch || true
	$(Q) patch -p1 -NR -r - < case_study/patches/RiscvPmpBoundedInts/duplicate_add.patch || true
	$(Q) patch -p1 -NR -r - < case_study/patches/MinimalCaps/duplicate_add.patch || true

Makefile.coq: _CoqProject Makefile $(SRCS)
	$(E) "COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq clean
	$(Q)rm -f $(AUXS)
	$(Q)rm -f Makefile.coq *.bak *.d *.glob *~ result*
	$(Q)rm -f case_study/Stats/.*.aux \
	  $(addprefix case_study/Stats/*,.csv .log .vo .vok .vos .glob)

install uninstall pretty-timed make-pretty-timed-before make-pretty-timed-after print-pretty-timed-diff: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq $@

summaxlen: Makefile.coq
	$(Q)rm -f test/SumMaxLen.vo*
	$(Q)$(MAKE) -f Makefile.coq test/SumMaxLen.vo

linkedlist: Makefile.coq
	$(Q)rm -f test/LinkedList.vo*
	$(Q)$(MAKE) -f Makefile.coq test/LinkedList.vo

timings: Makefile.coq
	$(Q)rm -f case_study/MinimalCaps/Contracts/Verification.vo*
	$(Q)rm -f test/SumMaxLen.vo*
	$(Q)rm -f test/LinkedList.vo*
	$(Q)$(MAKE) -f Makefile.coq test/LinkedList.vo test/SumMaxLen.vo case_study/MinimalCaps/Contracts/Verification.vo | ts '%.s' | scripts/timing.sh

Makefile2.coq: _CoqProject Makefile $(SRCS) case_study/MinimalCaps/Shallow.v
	$(E) "COQ_MAKEFILE Makefile2.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile2.coq case_study/MinimalCaps/Shallow.v

minimalcaps: Makefile2.coq
	$(Q)rm -f case_study/MinimalCaps/Contracts/Statistics.vo*
	$(Q)$(MAKE) -f Makefile.coq case_study/MinimalCaps/Contracts/Statistics.vo
	$(Q)rm -f case_study/MinimalCaps/Shallow.vo*
	$(Q)echo "Getting the statistics for the shallow executor. This takes 5-10min on a modern desktop and uses ~12GB of RAM."
	$(Q)$(MAKE) -f Makefile2.coq case_study/MinimalCaps/Shallow.vo | tr -s '[:space:]' '[\n*]' | scripts/shallow.sh

# VC size statistics. The files in case_study/Stats are not in _CoqProject.
# Each is compiled on its own, one at a time for clean timings, into a .log
# next to it, from which a .csv is made.
STATS      := $(wildcard case_study/Stats/*.v)
STATS_LIBS := $(shell grep -E '^-[QR] ' _CoqProject) -Q case_study/Stats Katamaran.Stats
STATS_ARGS := $(shell sed -n 's/^-arg "\(.*\)"$$/\1/p' _CoqProject)
# The stats files only use the framework and these two case studies.
STATS_DEPS :=$(filter theories/% case_study/RiscvPmp/% case_study/MinimalCaps/%,$(SRCS:.v=.vo))

# Always ask Makefile.coq, which knows how to bring these up to date.
$(STATS_DEPS) &: Makefile.coq FORCE
	$(Q)$(MAKE) -f Makefile.coq $(STATS_DEPS)

case_study/Stats/%.log: case_study/Stats/%.v $(STATS_DEPS)
	$(E) "ROCQ STATS $<"
	$(Q)rocq c $(STATS_LIBS) $(STATS_ARGS) $< > $@.tmp 2>&1 || { cat $@.tmp; exit 1; }
	$(Q)mv $@.tmp $@

case_study/Stats/%.csv: case_study/Stats/%.log scripts/vcstats.py
	$(E) "VCSTATS $@"
	$(Q)scripts/vcstats.py $< > $@.tmp
	$(Q)mv $@.tmp $@

.NOTPARALLEL: vcstats
vcstats: $(STATS:.v=.csv)

FORCE:
