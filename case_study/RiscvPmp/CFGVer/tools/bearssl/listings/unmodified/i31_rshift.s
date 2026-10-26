	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_rshift.c"
	.globl	br_i31_rshift                   # -- Begin function br_i31_rshift
	.p2align	2
	.type	br_i31_rshift,@function
br_i31_rshift:                          # @br_i31_rshift
# %bb.0:
	lw	a4, 0(a0)
	addi	a4, a4, 31
	srli	a2, a4, 5
	beqz	a2, .LBB0_5
# %bb.1:
	lw	a3, 4(a0)
	srl	a3, a3, a1
	li	a5, 64
	slli	a2, a2, 2
	bltu	a4, a5, .LBB0_4
# %bb.2:
	li	a4, 31
	sub	a4, a4, a1
	addi	a5, a0, 8
	add	a6, a2, a0
	addi	a6, a6, 4
.LBB0_3:                                # =>This Inner Loop Header: Depth=1
	lw	a7, 0(a5)
	sll	t0, a7, a4
	or	a3, t0, a3
	slli	a3, a3, 1
	srli	a3, a3, 1
	sw	a3, -4(a5)
	addi	a5, a5, 4
	srl	a3, a7, a1
	bne	a5, a6, .LBB0_3
.LBB0_4:
	add	a0, a0, a2
	sw	a3, 0(a0)
.LBB0_5:
	ret
.Lfunc_end0:
	.size	br_i31_rshift, .Lfunc_end0-br_i31_rshift
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
