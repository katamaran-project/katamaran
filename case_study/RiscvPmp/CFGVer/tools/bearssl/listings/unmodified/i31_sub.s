	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_sub.c"
	.globl	br_i31_sub                      # -- Begin function br_i31_sub
	.p2align	2
	.type	br_i31_sub,@function
br_i31_sub:                             # @br_i31_sub
# %bb.0:
	lw	a3, 0(a0)
	addi	a4, a3, 63
	li	a3, 64
	bltu	a4, a3, .LBB0_4
# %bb.1:
	li	a3, 0
	srli	a5, a4, 5
	neg	a2, a2
	addi	a4, a1, 4
	addi	a0, a0, 4
	slli	a5, a5, 2
	add	a1, a1, a5
.LBB0_2:                                # =>This Inner Loop Header: Depth=1
	lw	a6, 0(a0)
	lw	a5, 0(a4)
	add	a3, a6, a3
	sub	a5, a3, a5
	srai	a3, a5, 31
	slli	a7, a5, 1
	srli	a7, a7, 1
	xor	a7, a7, a6
	and	a7, a7, a2
	xor	a6, a7, a6
	sw	a6, 0(a0)
	addi	a4, a4, 4
	addi	a0, a0, 4
	bne	a4, a1, .LBB0_2
# %bb.3:
	srli	a0, a5, 31
	ret
.LBB0_4:
	li	a0, 0
	ret
.Lfunc_end0:
	.size	br_i31_sub, .Lfunc_end0-br_i31_sub
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
