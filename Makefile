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

.PHONY: coq clean summaxlen

coq: Makefile.coq
	$(E) "MAKE Makefile.coq"
	$(Q)$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject Makefile $(SRCS)
	$(E) "COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq clean
	$(Q)rm -f $(AUXS)
	$(Q)rm -f Makefile.coq *.bak *.d *.glob *~ result*

install: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq uninstall

summaxlen: Makefile.coq
	$(Q)rm -f test/SumMaxLen.vo*
	$(Q)$(MAKE) -f Makefile.coq test/SumMaxLen.vo

linkedlist: Makefile.coq
	$(Q)rm -f test/LinkedList.vo*
	$(Q)$(MAKE) -f Makefile.coq test/LinkedList.vo
