	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_encode.c"
	.globl	br_i31_encode                   # -- Begin function br_i31_encode
	.p2align	2
	.type	br_i31_encode,@function
br_i31_encode:                          # @br_i31_encode
# %bb.0:
	lw	a3, 0(a2)
	addi	a3, a3, 31
	srli	a4, a3, 5
	mv	a3, a1
	beqz	a4, .LBB0_10
# %bb.1:
	beqz	a3, .LBB0_16
# %bb.2:
	li	a1, 0
	li	t0, 0
	add	a0, a0, a3
	addi	a2, a2, 4
	li	a5, 1
	li	a6, 4
	j	.LBB0_5
.LBB0_3:                                #   in Loop: Header=BB0_5 Depth=1
	li	a1, 31
.LBB0_4:                                #   in Loop: Header=BB0_5 Depth=1
	addi	a2, a2, 4
	addi	a5, a5, 1
	mv	t0, a7
	beqz	a3, .LBB0_16
.LBB0_5:                                # =>This Inner Loop Header: Depth=1
	bgeu	a4, a5, .LBB0_7
# %bb.6:                                #   in Loop: Header=BB0_5 Depth=1
	li	a7, 0
	bnez	a1, .LBB0_8
	j	.LBB0_3
.LBB0_7:                                #   in Loop: Header=BB0_5 Depth=1
	lw	a7, 0(a2)
	beqz	a1, .LBB0_3
.LBB0_8:                                #   in Loop: Header=BB0_5 Depth=1
	sll	t1, a7, a1
	or	t0, t1, t0
	bltu	a3, a6, .LBB0_11
# %bb.9:                                #   in Loop: Header=BB0_5 Depth=1
	neg	t1, a1
	srl	a7, a7, t1
	addi	a1, a1, -1
	srli	t1, t0, 24
	sb	t1, -4(a0)
	srli	t1, t0, 16
	sb	t1, -3(a0)
	srli	t1, t0, 8
	sb	t1, -2(a0)
	sb	t0, -1(a0)
	addi	a0, a0, -4
	addi	a3, a3, -4
	j	.LBB0_4
.LBB0_10:
	li	a1, 0
	mv	a2, a3
	tail	memset
.LBB0_11:
	li	a1, 1
	beq	a3, a1, .LBB0_15
# %bb.12:
	li	a1, 2
	beq	a3, a1, .LBB0_14
# %bb.13:
	srli	a1, t0, 16
	sb	a1, -3(a0)
.LBB0_14:
	srli	a1, t0, 8
	sb	a1, -2(a0)
.LBB0_15:
	sb	t0, -1(a0)
.LBB0_16:
	ret
.Lfunc_end0:
	.size	br_i31_encode, .Lfunc_end0-br_i31_encode
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
