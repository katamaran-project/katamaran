.PHONY: all

CHERIOT_SAIL_DIR=~/src/cheriot-sail/

SAIL_SRCS := $(shell make -sC $(CHERIOT_SAIL_DIR) print-SAIL_SRCS | sed -E 's#(^| )# $(CHERIOT_SAIL_DIR)#g') $(CHERIOT_SAIL_DIR)/sail-riscv/model/main.sail

all:
	make -C $(CHERIOT_SAIL_DIR) csim
	sail --katamaran --katamaran-config configuration.lisp $(SAIL_SRCS)

test:
	sail --katamaran --katamaran-config configuration.lisp $(CHERIOT_SAIL_DIR)/sail-riscv/model/prelude.sail
