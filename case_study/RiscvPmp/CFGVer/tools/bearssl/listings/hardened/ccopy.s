	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"ccopy.c"
	.globl	br_ccopy                        # -- Begin function br_ccopy
	.p2align	2
	.type	br_ccopy,@function
br_ccopy:                               # @br_ccopy
# %bb.0:
	beqz	a3, .LBB0_3
# %bb.1:
	neg	a0, a0
	add	a3, a2, a3
.LBB0_2:                                # =>This Inner Loop Header: Depth=1
	lbu	a4, 0(a2)
	lbu	a5, 0(a1)
	addi	a6, a2, 1
	xor	a4, a5, a4
	and	a4, a4, a0
	xor	a4, a4, a5
	sb	a4, 0(a1)
	addi	a1, a1, 1
	mv	a2, a6
	bne	a6, a3, .LBB0_2
.LBB0_3:
	ret
.Lfunc_end0:
	.size	br_ccopy, .Lfunc_end0-br_ccopy
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
