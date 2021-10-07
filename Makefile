# Comment out the below line if you want to be quiet by default.
VERBOSE ?= 1
ifeq ($(V),1)
E=@true
Q=
MFLAGS=
else
E=@echo
Q=@
MFLAGS=-s
endif

SRCS := $(shell egrep "^.*\.v$$" _CoqProject)
AUXS := $(join $(dir $(SRCS)), $(addprefix ., $(notdir $(SRCS:.v=.aux))))

.PHONY: coq clean

coq: Makefile.coq
	$(E) "MAKE Makefile.coq"
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq

Makefile.coq: _CoqProject Makefile $(SRCS)
	$(E) "COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq clean
	$(Q)rm -f $(AUXS)
	$(Q)rm -f Makefile.coq *.bak *.d *.glob *~ result*

install: Makefile.coq
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq install

uninstall: Makefile.coq
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq uninstall
