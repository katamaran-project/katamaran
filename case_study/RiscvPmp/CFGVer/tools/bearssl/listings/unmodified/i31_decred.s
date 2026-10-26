	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_decred.c"
	.globl	br_i31_decode_reduce            # -- Begin function br_i31_decode_reduce
	.p2align	2
	.type	br_i31_decode_reduce,@function
br_i31_decode_reduce:                   # @br_i31_decode_reduce
# %bb.0:
	addi	sp, sp, -48
	sw	ra, 44(sp)                      # 4-byte Folded Spill
	sw	s0, 40(sp)                      # 4-byte Folded Spill
	sw	s1, 36(sp)                      # 4-byte Folded Spill
	sw	s2, 32(sp)                      # 4-byte Folded Spill
	sw	s3, 28(sp)                      # 4-byte Folded Spill
	sw	s4, 24(sp)                      # 4-byte Folded Spill
	sw	s5, 20(sp)                      # 4-byte Folded Spill
	sw	s6, 16(sp)                      # 4-byte Folded Spill
	sw	s7, 12(sp)                      # 4-byte Folded Spill
	sw	s8, 8(sp)                       # 4-byte Folded Spill
	lw	s5, 0(a3)
	mv	s0, a0
	beqz	s5, .LBB0_7
# %bb.1:
	mv	s1, a3
	mv	s2, a2
	mv	s3, a1
	addi	a0, s0, 4
	sw	s5, 0(s0)
	addi	a1, s5, 31
	srli	a1, a1, 3
	andi	a2, a1, -4
	li	a1, 0
	call	memset
	srli	a0, s5, 5
	sub	a0, s5, a0
	addi	a0, a0, 7
	srli	s6, a0, 3
	mv	a0, s0
	addi	s4, s6, -1
	bgeu	s4, s2, .LBB0_8
# %bb.2:
	mv	a1, s3
	mv	a2, s4
	call	br_i31_decode
	li	a0, 0
	li	a1, 0
	sw	s5, 0(s0)
	add	s3, s3, s4
	sub	s2, s2, s6
	addi	s2, s2, 1
	li	s4, 23
	li	s5, 255
	j	.LBB0_5
.LBB0_3:                                #   in Loop: Header=BB0_5 Depth=1
	slli	a1, a1, 8
	or	a1, a1, s6
	addi	a0, a0, 8
.LBB0_4:                                #   in Loop: Header=BB0_5 Depth=1
	addi	s2, s2, -1
	addi	s3, s3, 1
	beqz	s2, .LBB0_9
.LBB0_5:                                # =>This Inner Loop Header: Depth=1
	lbu	s6, 0(s3)
	blt	a0, s4, .LBB0_3
# %bb.6:                                #   in Loop: Header=BB0_5 Depth=1
	addi	s7, a0, -23
	not	s8, a0
	sll	a0, a1, s8
	srl	a1, s6, s7
	or	a1, a1, a0
	mv	a0, s0
	mv	a2, s1
	call	br_i31_muladd_small
	srl	a0, s5, s8
	and	a1, a0, s6
	mv	a0, s7
	j	.LBB0_4
.LBB0_7:
	sw	zero, 0(s0)
	j	.LBB0_11
.LBB0_8:
	mv	a1, s3
	mv	a2, s2
	call	br_i31_decode
	sw	s5, 0(s0)
	j	.LBB0_11
.LBB0_9:
	beqz	a0, .LBB0_11
# %bb.10:
	lw	a2, 4(s0)
	sll	a2, a2, a0
	or	a1, a2, a1
	slli	a1, a1, 1
	srli	s2, a1, 1
	li	a1, 31
	sub	a1, a1, a0
	mv	a0, s0
	call	br_i31_rshift
	mv	a0, s0
	mv	a1, s2
	mv	a2, s1
	lw	ra, 44(sp)                      # 4-byte Folded Reload
	lw	s0, 40(sp)                      # 4-byte Folded Reload
	lw	s1, 36(sp)                      # 4-byte Folded Reload
	lw	s2, 32(sp)                      # 4-byte Folded Reload
	lw	s3, 28(sp)                      # 4-byte Folded Reload
	lw	s4, 24(sp)                      # 4-byte Folded Reload
	lw	s5, 20(sp)                      # 4-byte Folded Reload
	lw	s6, 16(sp)                      # 4-byte Folded Reload
	lw	s7, 12(sp)                      # 4-byte Folded Reload
	lw	s8, 8(sp)                       # 4-byte Folded Reload
	addi	sp, sp, 48
	tail	br_i31_muladd_small
.LBB0_11:
	lw	ra, 44(sp)                      # 4-byte Folded Reload
	lw	s0, 40(sp)                      # 4-byte Folded Reload
	lw	s1, 36(sp)                      # 4-byte Folded Reload
	lw	s2, 32(sp)                      # 4-byte Folded Reload
	lw	s3, 28(sp)                      # 4-byte Folded Reload
	lw	s4, 24(sp)                      # 4-byte Folded Reload
	lw	s5, 20(sp)                      # 4-byte Folded Reload
	lw	s6, 16(sp)                      # 4-byte Folded Reload
	lw	s7, 12(sp)                      # 4-byte Folded Reload
	lw	s8, 8(sp)                       # 4-byte Folded Reload
	addi	sp, sp, 48
	ret
.Lfunc_end0:
	.size	br_i31_decode_reduce, .Lfunc_end0-br_i31_decode_reduce
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
