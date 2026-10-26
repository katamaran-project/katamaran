# PLAN-rsa.md Phase 1, spike S1a: call br_i31_sub once, then leave the
# program at its fall-through end (_etext, defined by the linker).
	.text
	.globl	_start
_start:
	call	br_i31_sub
	j	_etext
