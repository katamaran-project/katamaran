	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i32_div32.c"
	.globl	br_divrem                       # -- Begin function br_divrem
	.p2align	2
	.type	br_divrem,@function
br_divrem:                              # @br_divrem
# %bb.0:
	li	a4, 0
	xor	a5, a0, a2
	seqz	a5, a5
	addi	a5, a5, -1
	and	a0, a5, a0
	li	a5, 32
	li	a6, 1
	li	a7, 1
.LBB0_1:                                # =>This Inner Loop Header: Depth=1
	addi	a5, a5, -1
	sll	t0, a0, a7
	srl	t1, a1, a5
	or	t0, t0, t1
	sub	t1, t0, a2
	xor	t0, t0, a2
	xor	t2, t1, a2
	and	t0, t2, t0
	xor	t0, t0, t1
	not	t0, t0
	srli	t0, t0, 31
	srl	t2, a0, a5
	or	t0, t2, t0
	srl	t1, t1, a7
	sll	t2, a2, a5
	sub	t2, a1, t2
	neg	t3, t0
	xor	t1, t1, a0
	and	t1, t1, t3
	xor	a0, t1, a0
	xor	t1, t2, a1
	and	t1, t1, t3
	xor	a1, t1, a1
	sll	t0, t0, a5
	or	a4, t0, a4
	addi	a7, a7, 1
	bltu	a6, a5, .LBB0_1
# %bb.2:
	sub	a5, a1, a2
	xor	a6, a1, a2
	xor	a2, a5, a2
	and	a2, a2, a6
	xor	a2, a2, a5
	not	a2, a2
	srli	a2, a2, 31
	or	a2, a0, a2
	or	a0, a2, a4
	neg	a2, a2
	xor	a5, a5, a1
	and	a2, a5, a2
	xor	a1, a2, a1
	sw	a1, 0(a3)
	ret
.Lfunc_end0:
	.size	br_divrem, .Lfunc_end0-br_divrem
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
