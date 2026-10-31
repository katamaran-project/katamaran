# PLAN-rsa.md Phase 1, spike S1b: call rsa_spike_sub2 (sub2.c) once, then
# leave the program at its fall-through end (_etext, defined by the linker).
	.text
	.globl	_start
_start:
	call	rsa_spike_sub2
	j	_etext
