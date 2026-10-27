# PLAN-rsa.md Phase 2: call picolibc's memcpy once, then leave the program
# at its fall-through end (_etext, defined by the linker).
	.text
	.globl	_start
_start:
	call	memcpy
	j	_etext
