	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_ninv31.c"
	.globl	br_i31_ninv31                   # -- Begin function br_i31_ninv31
	.p2align	2
	.type	br_i31_ninv31,@function
br_i31_ninv31:                          # @br_i31_ninv31
# %bb.0:
	li	a1, 2
	sub	a2, a1, a0
	mul	a3, a2, a0
	sub	a3, a1, a3
	mul	a2, a3, a2
	mul	a3, a2, a0
	sub	a3, a1, a3
	mul	a2, a3, a2
	mul	a3, a2, a0
	sub	a1, a1, a3
	mul	a1, a1, a2
	mul	a2, a1, a0
	lui	a3, 524288
	addi	a3, a3, -2
	add	a2, a2, a3
	mul	a1, a2, a1
	slli	a0, a0, 31
	srai	a0, a0, 31
	addi	a3, a3, 1
	and	a0, a0, a3
	and	a0, a0, a1
	ret
.Lfunc_end0:
	.size	br_i31_ninv31, .Lfunc_end0-br_i31_ninv31
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
