	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_decode.c"
	.globl	br_i31_decode                   # -- Begin function br_i31_decode
	.p2align	2
	.type	br_i31_decode,@function
br_i31_decode:                          # @br_i31_decode
# %bb.0:
	addi	sp, sp, -16
	sw	ra, 12(sp)                      # 4-byte Folded Spill
	sw	s0, 8(sp)                       # 4-byte Folded Spill
	mv	s0, a0
	beqz	a2, .LBB0_7
# %bb.1:
	li	a3, 0
	li	a4, 0
	addi	a0, a1, -1
	li	a1, 1
	li	a5, 23
	j	.LBB0_3
.LBB0_2:                                #   in Loop: Header=BB0_3 Depth=1
	slli	a4, a4, 1
	srli	a4, a4, 1
	slli	a7, a1, 2
	addi	a1, a1, 1
	add	a7, s0, a7
	sw	a4, 0(a7)
	not	a4, a3
	addi	a3, a3, -23
	srl	a4, a6, a4
	addi	a2, a2, -1
	beqz	a2, .LBB0_5
.LBB0_3:                                # =>This Inner Loop Header: Depth=1
	add	a6, a0, a2
	lbu	a6, 0(a6)
	sll	a7, a6, a3
	or	a4, a7, a4
	bge	a3, a5, .LBB0_2
# %bb.4:                                #   in Loop: Header=BB0_3 Depth=1
	addi	a3, a3, 8
	addi	a2, a2, -1
	bnez	a2, .LBB0_3
.LBB0_5:
	beqz	a3, .LBB0_8
# %bb.6:
	slli	a0, a1, 2
	addi	a1, a1, 1
	add	a0, s0, a0
	sw	a4, 0(a0)
	j	.LBB0_8
.LBB0_7:
	li	a1, 1
.LBB0_8:
	addi	a0, s0, 4
	addi	a1, a1, -1
	call	br_i31_bit_length
	sw	a0, 0(s0)
	lw	ra, 12(sp)                      # 4-byte Folded Reload
	lw	s0, 8(sp)                       # 4-byte Folded Reload
	addi	sp, sp, 16
	ret
.Lfunc_end0:
	.size	br_i31_decode, .Lfunc_end0-br_i31_decode
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
