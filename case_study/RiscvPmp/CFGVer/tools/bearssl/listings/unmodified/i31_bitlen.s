	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_bitlen.c"
	.globl	br_i31_bit_length               # -- Begin function br_i31_bit_length
	.p2align	2
	.type	br_i31_bit_length,@function
br_i31_bit_length:                      # @br_i31_bit_length
# %bb.0:
	beqz	a1, .LBB0_4
# %bb.1:
	li	a2, 0
	li	a3, 0
	addi	a4, a1, -1
	slli	a1, a1, 2
	add	a0, a1, a0
	addi	a0, a0, -4
	li	a1, -1
.LBB0_2:                                # =>This Inner Loop Header: Depth=1
	lw	a5, 0(a0)
	snez	a6, a2
	addi	a6, a6, -1
	xor	a5, a5, a2
	and	a5, a5, a6
	xor	a2, a5, a2
	xor	a5, a4, a3
	and	a5, a5, a6
	xor	a3, a5, a3
	addi	a4, a4, -1
	addi	a0, a0, -4
	bne	a4, a1, .LBB0_2
# %bb.3:
	slli	a0, a3, 5
	j	.LBB0_5
.LBB0_4:
	li	a0, 0
	li	a2, 0
.LBB0_5:
	snez	a1, a2
	lui	a3, 16
	addi	a3, a3, -1
	sub	a3, a3, a2
	lui	a4, 1048560
	add	a4, a2, a4
	and	a4, a4, a2
	xor	a3, a4, a3
	srli	a3, a3, 27
	andi	a3, a3, 16
	srl	a2, a2, a3
	li	a4, 255
	sub	a4, a4, a2
	addi	a5, a2, -256
	and	a5, a5, a2
	xor	a4, a5, a4
	srli	a4, a4, 28
	andi	a4, a4, 8
	srl	a2, a2, a4
	li	a5, 15
	sub	a5, a5, a2
	addi	a6, a2, -16
	and	a6, a6, a2
	xor	a5, a6, a5
	srli	a5, a5, 29
	andi	a5, a5, 4
	srl	a2, a2, a5
	li	a6, 3
	sub	a6, a6, a2
	addi	a7, a2, -4
	and	a7, a7, a2
	xor	a6, a7, a6
	srli	a6, a6, 30
	andi	a6, a6, 2
	srl	a2, a2, a6
	li	a7, 1
	sub	a7, a7, a2
	addi	t0, a2, -2
	and	a2, t0, a2
	xor	a2, a2, a7
	srli	a2, a2, 31
	or	a0, a0, a1
	or	a0, a0, a3
	or	a0, a0, a4
	or	a0, a0, a5
	or	a0, a0, a6
	add	a0, a0, a2
	ret
.Lfunc_end0:
	.size	br_i31_bit_length, .Lfunc_end0-br_i31_bit_length
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
