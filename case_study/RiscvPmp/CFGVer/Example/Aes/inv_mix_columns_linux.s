	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"inv_mix_columns_linux.c"
	.globl	inv_mix_columns                 # -- Begin function inv_mix_columns
	.p2align	2
	.type	inv_mix_columns,@function
inv_mix_columns:                        # @inv_mix_columns
# %bb.0:
	slli	a1, a0, 2
	lui	a2, 1036240
	addi	a2, a2, -772
	and	a1, a1, a2
	srli	a2, a0, 7
	lui	a3, 4112
	addi	a3, a3, 257
	and	a2, a2, a3
	li	a4, 54
	mul	a2, a2, a4
	xor	a1, a2, a1
	srli	a2, a0, 6
	and	a2, a2, a3
	li	a4, 27
	mul	a2, a2, a4
	xor	a1, a1, a2
	srli	a2, a1, 16
	slli	a5, a1, 16
	or	a2, a5, a2
	xor	a0, a0, a1
	xor	a0, a2, a0
	slli	a1, a0, 1
	lui	a2, 1044464
	addi	a2, a2, -258
	and	a1, a1, a2
	srli	a2, a0, 7
	and	a2, a2, a3
	mul	a2, a2, a4
	srli	a3, a0, 16
	slli	a4, a0, 16
	or	a3, a4, a3
	xor	a1, a1, a3
	xor	a1, a1, a2
	xor	a0, a1, a0
	srli	a2, a0, 8
	slli	a0, a0, 24
	or	a0, a0, a2
	xor	a0, a0, a1
	ret
.Lfunc_end0:
	.size	inv_mix_columns, .Lfunc_end0-inv_mix_columns
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
