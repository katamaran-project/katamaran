	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_muladd.c"
	.globl	br_i31_muladd_small             # -- Begin function br_i31_muladd_small
	.p2align	2
	.type	br_i31_muladd_small,@function
br_i31_muladd_small:                    # @br_i31_muladd_small
# %bb.0:
	addi	sp, sp, -80
	sw	ra, 76(sp)                      # 4-byte Folded Spill
	sw	s0, 72(sp)                      # 4-byte Folded Spill
	sw	s1, 68(sp)                      # 4-byte Folded Spill
	sw	s2, 64(sp)                      # 4-byte Folded Spill
	sw	s3, 60(sp)                      # 4-byte Folded Spill
	sw	s4, 56(sp)                      # 4-byte Folded Spill
	sw	s5, 52(sp)                      # 4-byte Folded Spill
	sw	s6, 48(sp)                      # 4-byte Folded Spill
	sw	s7, 44(sp)                      # 4-byte Folded Spill
	sw	s8, 40(sp)                      # 4-byte Folded Spill
	sw	s9, 36(sp)                      # 4-byte Folded Spill
	sw	s10, 32(sp)                     # 4-byte Folded Spill
	sw	s11, 28(sp)                     # 4-byte Folded Spill
	mv	s1, a2
	lw	a2, 0(a2)
	beqz	a2, .LBB0_9
# %bb.1:
	mv	s0, a0
	li	a0, 31
	bltu	a0, a2, .LBB0_3
# %bb.2:
	lw	a3, 4(s0)
	lw	a2, 4(s1)
	srli	a0, a3, 1
	slli	a3, a3, 31
	or	a1, a3, a1
	addi	a3, sp, 20
	call	br_divrem
	lw	a0, 20(sp)
	sw	a0, 4(s0)
	j	.LBB0_9
.LBB0_3:
	mv	s9, a1
	lui	s5, 524288
	addi	s4, a2, 31
	srli	s6, s4, 5
	slli	s6, s6, 2
	add	s11, s0, s6
	lw	s8, 0(s11)
	addi	s5, s5, -1
	andi	s10, a2, 31
	addi	s2, s0, 4
	sw	s8, 16(sp)                      # 4-byte Folded Spill
	beqz	s10, .LBB0_5
# %bb.4:
	addi	s3, s6, -4
	add	s7, s0, s3
	lw	a0, 0(s7)
	sw	s4, 12(sp)                      # 4-byte Folded Spill
	xori	s4, s10, 31
	sll	a1, s8, s4
	srl	a0, a0, s10
	and	a1, a1, s5
	or	s8, a0, a1
	addi	a0, s0, 8
	mv	a1, s2
	mv	a2, s3
	call	memmove
	sw	s9, 4(s0)
	lw	a0, 0(s11)
	lw	a1, 0(s7)
	sll	a0, a0, s4
	srl	a1, a1, s10
	add	a2, s1, s6
	lw	a2, 0(a2)
	add	s3, s1, s3
	lw	a3, 0(s3)
	and	a0, a0, s5
	or	a1, a0, a1
	sll	a0, a2, s4
	lw	s4, 12(sp)                      # 4-byte Folded Reload
	srl	a2, a3, s10
	and	a0, a0, s5
	or	s3, a0, a2
	j	.LBB0_6
.LBB0_5:
	addi	a0, s0, 8
	addi	a1, s0, 4
	addi	a2, s6, -4
	call	memmove
	sw	s9, 4(s0)
	lw	a1, 0(s11)
	add	a0, s1, s6
	lw	s3, 0(a0)
.LBB0_6:
	srli	a0, s8, 1
	slli	a2, s8, 31
	or	a1, a2, a1
	addi	a3, sp, 24
	mv	a2, s3
	call	br_divrem
	li	a1, 32
	bgeu	s4, a1, .LBB0_10
# %bb.7:
	li	a3, 0
	li	a1, 1
	lw	t0, 16(sp)                      # 4-byte Folded Reload
.LBB0_8:
	sub	a0, t0, a3
	xor	a4, a3, t0
	xor	a2, a0, a3
	and	a2, a2, a4
	xor	a0, a2, a0
	srli	a2, a0, 31
	not	a0, a2
	sub	a3, a3, t0
	xor	a5, a3, t0
	and	a4, a5, a4
	xor	a3, a4, a3
	srli	a3, a3, 31
	or	a1, a3, a1
	and	s2, a1, a0
	mv	a0, s0
	mv	a1, s1
	call	br_i31_add
	mv	a0, s0
	mv	a1, s1
	mv	a2, s2
	call	br_i31_sub
.LBB0_9:
	lw	ra, 76(sp)                      # 4-byte Folded Reload
	lw	s0, 72(sp)                      # 4-byte Folded Reload
	lw	s1, 68(sp)                      # 4-byte Folded Reload
	lw	s2, 64(sp)                      # 4-byte Folded Reload
	lw	s3, 60(sp)                      # 4-byte Folded Reload
	lw	s4, 56(sp)                      # 4-byte Folded Reload
	lw	s5, 52(sp)                      # 4-byte Folded Reload
	lw	s6, 48(sp)                      # 4-byte Folded Reload
	lw	s7, 44(sp)                      # 4-byte Folded Reload
	lw	s8, 40(sp)                      # 4-byte Folded Reload
	lw	s9, 36(sp)                      # 4-byte Folded Reload
	lw	s10, 32(sp)                     # 4-byte Folded Reload
	lw	s11, 28(sp)                     # 4-byte Folded Reload
	addi	sp, sp, 80
	ret
.LBB0_10:
	bne	s8, s3, .LBB0_12
# %bb.11:
	lui	a0, 524288
	addi	a0, a0, -1
	j	.LBB0_13
.LBB0_12:
	addi	a1, a0, -1
	snez	a0, a0
	addi	a0, a0, -1
	xor	a0, a1, a0
.LBB0_13:
	lw	t0, 16(sp)                      # 4-byte Folded Reload
	li	a3, 0
	addi	a2, s1, 4
	add	s6, s2, s6
	li	a1, 1
	j	.LBB0_15
.LBB0_14:                               #   in Loop: Header=BB0_15 Depth=1
	mulhu	a4, a4, a0
	sltu	a6, a3, a6
	add	a4, a4, a6
	slli	a4, a4, 1
	srli	a3, a3, 31
	or	a3, a3, a4
	srli	a5, a5, 31
	add	a3, a5, a3
	addi	s2, s2, 4
	addi	a2, a2, 4
	beq	s2, s6, .LBB0_8
.LBB0_15:                               # =>This Inner Loop Header: Depth=1
	lw	a4, 0(a2)
	lw	a5, 0(s2)
	mul	a6, a4, a0
	add	a3, a6, a3
	and	a7, a3, s5
	sub	a5, a5, a7
	and	a7, a5, s5
	sw	a7, 0(s2)
	beq	a4, a7, .LBB0_14
# %bb.16:                               #   in Loop: Header=BB0_15 Depth=1
	sub	a1, a4, a7
	not	a7, a4
	and	a1, a1, a7
	srli	a1, a1, 31
	j	.LBB0_14
.Lfunc_end0:
	.size	br_i31_muladd_small, .Lfunc_end0-br_i31_muladd_small
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
