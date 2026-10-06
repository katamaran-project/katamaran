	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"inv_mix_columns_alg7.c"
	.globl	inv_mix_columns                 # -- Begin function inv_mix_columns
	.p2align	2
	.type	inv_mix_columns,@function
inv_mix_columns:                        # @inv_mix_columns
# %bb.0:
	slli	a1, a0, 2
	lui	a2, 1036240
	addi	a2, a2, -772
	and	a3, a1, a2
	srli	a2, a0, 7
	lui	a1, 16
	addi	a1, a1, 257
	and	a4, a2, a1
	lui	a2, 4096
	or	a4, a4, a2
	#APP
	#NO_APP
	srli	a5, a0, 31
	#APP
	#NO_APP
	li	a6, 54
	mul	a4, a4, a6
	#APP
	#NO_APP
	mul	a5, a5, a6
	#APP
	#NO_APP
	slli	a5, a5, 24
	lui	a6, 827392
	add	a5, a5, a6
	add	a4, a4, a5
	xor	a3, a4, a3
	srli	a4, a0, 6
	and	a4, a4, a1
	or	a4, a4, a2
	#APP
	#NO_APP
	slli	a5, a0, 1
	srli	a5, a5, 31
	#APP
	#NO_APP
	li	a6, 27
	mul	a4, a4, a6
	#APP
	#NO_APP
	mul	a5, a5, a6
	#APP
	#NO_APP
	slli	a5, a5, 24
	lui	a7, 937984
	add	a5, a5, a7
	add	a4, a4, a5
	xor	a3, a3, a4
	srli	a4, a3, 16
	slli	a5, a3, 16
	or	a4, a5, a4
	xor	a0, a0, a3
	xor	a0, a4, a0
	slli	a3, a0, 1
	lui	a4, 1044464
	addi	a4, a4, -258
	and	a3, a3, a4
	srli	a4, a0, 7
	and	a1, a4, a1
	or	a1, a1, a2
	#APP
	#NO_APP
	srli	a2, a0, 31
	#APP
	#NO_APP
	mul	a1, a1, a6
	#APP
	#NO_APP
	mul	a2, a2, a6
	#APP
	#NO_APP
	slli	a2, a2, 24
	add	a2, a2, a7
	add	a1, a1, a2
	srli	a2, a0, 16
	slli	a4, a0, 16
	or	a2, a4, a2
	xor	a2, a2, a3
	xor	a1, a2, a1
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
