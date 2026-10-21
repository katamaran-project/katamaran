.PHONY: all csim sail test prelude

THIS_MAKEFILES_LOCATION=$(dir $(realpath $(lastword $(MAKEFILE_LIST))))
CASE_STUDY_DIR := $(abspath $(THIS_MAKEFILES_LOCATION))

# The cheriot-sail checkout to translate. It has no default and must be passed,
# e.g. make sail CHERIOT_SAIL_DIR=/path/to/cheriot-sail.  A relative path is
# resolved against this directory, not the one make was started from.
ifndef CHERIOT_SAIL_DIR
$(error CHERIOT_SAIL_DIR is not set. Pass the path to a cheriot-sail checkout, e.g. make sail CHERIOT_SAIL_DIR=/path/to/cheriot-sail)
endif
override CHERIOT_SAIL_DIR := $(abspath $(CHERIOT_SAIL_DIR))

# The directory sail runs in, and so where its output goes: the instantiated
# templates, sail_smt_cache and z3_problems.  Give each parallel run its own,
# e.g. make sail OUT_DIR=/tmp/cheriot-run1.  A relative OUT_DIR is resolved
# against the directory make was started from, which PWD still holds after
# make -C changed directory (CURDIR is the one that changes).
#
# WARNING: make does not check PWD; it trusts the environment.  Shells keep PWD
# correct, but a program that is not a shell and starts make in another
# directory usually passes on its own, stale PWD.  Examples are Python's
# subprocess.run(..., cwd=...) without shell=True and Node's child_process with
# cwd.  A relative OUT_DIR then silently resolves against the wrong directory,
# and parallel runs may end up sharing one.  Scripts and tools should
# therefore always pass an absolute OUT_DIR.
OUT_DIR ?= $(CASE_STUDY_DIR)
# Take absolute path as-is. Prefix relative path with PWD. Absolutify the result.
override OUT_DIR := $(abspath $(if $(filter /%,$(OUT_DIR)),$(OUT_DIR),$(or $(PWD),$(CURDIR))/$(OUT_DIR)))

# The configuration refers to the templates by relative path, so outside the
# case study directory, OUT_DIR gets copies of them.
SAIL_INPUTS := $(CASE_STUDY_DIR)/configuration.lisp $(wildcard $(CASE_STUDY_DIR)/*.template.v)
ifeq ($(OUT_DIR),$(CASE_STUDY_DIR))
ENTER_OUT_DIR := true
else
ENTER_OUT_DIR := mkdir -p $(OUT_DIR) && cd $(OUT_DIR) && cp $(SAIL_INPUTS) .
endif

# The sail binary, used here and passed on to CHERIOT_SAIL_DIR's Makefile.
# To use the katamaran plugin of a sail-backend checkout (built with
# dune build, not installed), set it to that checkout's bin/sail-local.
SAIL ?= sail
# The sub-makes run in CHERIOT_SAIL_DIR, so a relative path would not resolve there.
override SAIL := $(if $(findstring /,$(SAIL)),$(abspath $(SAIL)),$(SAIL))

# Our SAIL_SRCS are the SAIL_SRCS variable from CHERIOT_SAIL_DIR's Makefile,
# turned  into absolute paths, and with main.sail added.
SAIL_SRCS := $(shell $(MAKE) -sC $(CHERIOT_SAIL_DIR) -f $(THIS_MAKEFILES_LOCATION)/printvar.mak -f Makefile SAIL=$(SAIL) print-SAIL_SRCS | sed -E 's#(^| +)# $(CHERIOT_SAIL_DIR)/#g') $(CHERIOT_SAIL_DIR)/sail-riscv/model/main.sail

sail:
	# Enter the output directory if necessary.
	$(ENTER_OUT_DIR) && $(SAIL) --katamaran --katamaran-config configuration.lisp $(SAIL_SRCS)

test:
	# Enter the output directory if necessary.
	$(ENTER_OUT_DIR) && $(SAIL) --katamaran --katamaran-config configuration.lisp $(CHERIOT_SAIL_DIR)/sail-riscv/model/prelude.sail
