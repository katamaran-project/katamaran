	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_add.c"
	.globl	br_i31_add                      # -- Begin function br_i31_add
	.p2align	2
	.type	br_i31_add,@function
br_i31_add:                             # @br_i31_add
# %bb.0:
	mv	a3, a0
	lw	a0, 0(a0)
	addi	a4, a0, 63
	li	a0, 64
	bltu	a4, a0, .LBB0_4
# %bb.1:
	li	a0, 0
	srli	a5, a4, 5
	neg	a2, a2
	addi	a4, a1, 4
	addi	a3, a3, 4
	slli	a5, a5, 2
	add	a1, a1, a5
.LBB0_2:                                # =>This Inner Loop Header: Depth=1
	lw	a5, 0(a3)
	lw	a6, 0(a4)
	add	a0, a5, a0
	add	a6, a0, a6
	srli	a0, a6, 31
	slli	a6, a6, 1
	srli	a6, a6, 1
	xor	a6, a6, a5
	and	a6, a6, a2
	xor	a5, a6, a5
	sw	a5, 0(a3)
	addi	a4, a4, 4
	addi	a3, a3, 4
	bne	a4, a1, .LBB0_2
# %bb.3:
	ret
.LBB0_4:
	li	a0, 0
	ret
.Lfunc_end0:
	.size	br_i31_add, .Lfunc_end0-br_i31_add
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
