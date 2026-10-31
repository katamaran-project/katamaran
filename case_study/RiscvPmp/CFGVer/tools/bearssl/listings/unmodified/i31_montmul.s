	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_montmul.c"
	.globl	br_i31_montymul                 # -- Begin function br_i31_montymul
	.p2align	2
	.type	br_i31_montymul,@function
br_i31_montymul:                        # @br_i31_montymul
# %bb.0:
	addi	sp, sp, -64
	sw	ra, 60(sp)                      # 4-byte Folded Spill
	sw	s0, 56(sp)                      # 4-byte Folded Spill
	sw	s1, 52(sp)                      # 4-byte Folded Spill
	sw	s2, 48(sp)                      # 4-byte Folded Spill
	sw	s3, 44(sp)                      # 4-byte Folded Spill
	sw	s4, 40(sp)                      # 4-byte Folded Spill
	sw	s5, 36(sp)                      # 4-byte Folded Spill
	sw	s6, 32(sp)                      # 4-byte Folded Spill
	sw	s7, 28(sp)                      # 4-byte Folded Spill
	sw	s8, 24(sp)                      # 4-byte Folded Spill
	sw	s9, 20(sp)                      # 4-byte Folded Spill
	sw	s10, 16(sp)                     # 4-byte Folded Spill
	sw	s11, 12(sp)                     # 4-byte Folded Spill
	mv	s0, a3
	lw	a3, 0(a3)
	mv	s2, a4
	mv	s3, a2
	mv	s4, a1
	mv	s1, a0
	addi	a0, a3, 31
	srli	s6, a0, 5
	addi	s5, s1, 4
	sw	a3, 0(s1)
	srli	a0, a0, 3
	andi	a2, a0, -4
	mv	a0, s5
	li	a1, 0
	call	memset
	sw	s0, 4(sp)                       # 4-byte Folded Spill
	sw	s1, 0(sp)                       # 4-byte Folded Spill
	beqz	s6, .LBB0_10
# %bb.1:
	li	a0, 0
	li	s7, 0
	andi	a1, s6, -4
	li	a2, -1
	lui	a3, 524288
	addi	a3, a3, -1
	slli	t2, s6, 2
	add	a4, s1, t2
	addi	a5, s0, 8
	addi	a6, s3, 8
	addi	a7, s1, 8
	addi	s0, s0, 4
	sw	s0, 8(sp)                       # 4-byte Folded Spill
	addi	t1, s3, 4
	add	t2, s5, t2
	j	.LBB0_3
.LBB0_2:                                #   in Loop: Header=BB0_3 Depth=1
	add	s7, s10, s7
	and	t0, s7, a3
	sw	t0, 0(a4)
	srli	s7, s7, 31
	beq	a0, s6, .LBB0_11
.LBB0_3:                                # =>This Loop Header: Depth=1
                                        #     Child Loop BB0_5 Depth 2
                                        #     Child Loop BB0_9 Depth 2
	addi	a0, a0, 1
	slli	t3, a0, 2
	add	t3, s4, t3
	lw	t3, 0(t3)
	lw	t4, 4(s3)
	lw	t5, 0(s5)
	mul	t4, t4, t3
	add	t4, t4, t5
	mul	t4, t4, s2
	and	t4, t4, a3
	beqz	a1, .LBB0_7
# %bb.4:                                #   in Loop: Header=BB0_3 Depth=1
	li	t5, 0
	li	s10, 0
	mv	t6, a7
	mv	s8, a6
	mv	s9, a5
.LBB0_5:                                #   Parent Loop BB0_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	lw	s11, -4(s8)
	lw	ra, -4(s9)
	lw	s0, -4(t6)
	mulhu	s1, s11, t3
	mul	s11, s11, t3
	mulhu	t0, ra, t4
	mul	ra, ra, t4
	add	s10, s0, s10
	sltu	s0, s10, s0
	add	s11, s10, s11
	sltu	s10, s11, s10
	add	s0, s0, s1
	add	s0, s0, s10
	add	ra, s11, ra
	sltu	s1, ra, s11
	add	t0, s0, t0
	add	t0, t0, s1
	slli	t0, t0, 1
	and	s0, ra, a3
	sw	s0, -8(t6)
	lw	s0, 0(s8)
	srli	s1, ra, 31
	or	t0, s1, t0
	lw	s1, 0(t6)
	mulhu	s10, s0, t3
	lw	s11, 0(s9)
	mul	s0, s0, t3
	add	s1, s0, s1
	sltu	s0, s1, s0
	mulhu	ra, s11, t4
	mul	s11, s11, t4
	add	s11, s1, s11
	sltu	s1, s11, s1
	add	s10, s10, ra
	add	s0, s10, s0
	add	s0, s0, s1
	and	t0, t0, a2
	add	t0, s11, t0
	sltu	s1, t0, s11
	add	s0, s0, s1
	srli	s1, t0, 31
	and	t0, t0, a3
	sw	t0, -4(t6)
	lw	t0, 4(s8)
	slli	s0, s0, 1
	or	s0, s1, s0
	lw	s1, 4(t6)
	mulhu	s10, t0, t3
	lw	s11, 4(s9)
	mul	t0, t0, t3
	add	s1, t0, s1
	sltu	t0, s1, t0
	mulhu	ra, s11, t4
	mul	s11, s11, t4
	add	s11, s1, s11
	sltu	s1, s11, s1
	add	s10, s10, ra
	add	t0, s10, t0
	add	t0, t0, s1
	and	s0, s0, a2
	add	s0, s11, s0
	sltu	s1, s0, s11
	add	t0, t0, s1
	srli	s1, s0, 31
	slli	t0, t0, 1
	and	s0, s0, a3
	sw	s0, 0(t6)
	lw	s0, 8(s8)
	or	t0, s1, t0
	addi	t5, t5, 4
	lw	s1, 8(t6)
	mulhu	s10, s0, t3
	lw	s11, 8(s9)
	mul	s0, s0, t3
	add	s1, s0, s1
	sltu	s0, s1, s0
	mulhu	ra, s11, t4
	mul	s11, s11, t4
	add	s11, s1, s11
	sltu	s1, s11, s1
	add	s10, s10, ra
	add	s0, s10, s0
	add	s0, s0, s1
	and	t0, t0, a2
	add	t0, s11, t0
	sltu	s1, t0, s11
	add	s0, s0, s1
	srli	s1, t0, 31
	slli	s0, s0, 1
	or	s10, s1, s0
	and	t0, t0, a3
	sw	t0, 4(t6)
	addi	s9, s9, 16
	addi	s8, s8, 16
	addi	t6, t6, 16
	bltu	t5, a1, .LBB0_5
# %bb.6:                                #   in Loop: Header=BB0_3 Depth=1
	bgeu	t5, s6, .LBB0_2
	j	.LBB0_8
.LBB0_7:                                #   in Loop: Header=BB0_3 Depth=1
	li	s10, 0
	li	t5, 0
	bgeu	zero, s6, .LBB0_2
.LBB0_8:                                #   in Loop: Header=BB0_3 Depth=1
	slli	s8, t5, 2
	add	t5, s5, s8
	lw	t6, 8(sp)                       # 4-byte Folded Reload
	add	t6, t6, s8
	add	s8, t1, s8
.LBB0_9:                                #   Parent Loop BB0_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	lw	t0, 0(s8)
	lw	s0, 0(t6)
	lw	s1, 0(t5)
	mulhu	s9, t0, t3
	mul	t0, t0, t3
	mulhu	s11, s0, t4
	mul	s0, s0, t4
	add	s10, s1, s10
	sltu	s1, s10, s1
	add	t0, s10, t0
	sltu	s10, t0, s10
	add	s1, s1, s9
	add	s1, s1, s10
	add	s0, t0, s0
	sltu	t0, s0, t0
	add	s1, s1, s11
	add	t0, s1, t0
	slli	t0, t0, 1
	srli	s1, s0, 31
	or	s10, s1, t0
	and	s0, s0, a3
	sw	s0, -4(t5)
	addi	t5, t5, 4
	addi	t6, t6, 4
	addi	s8, s8, 4
	bne	t5, t2, .LBB0_9
	j	.LBB0_2
.LBB0_10:
	li	s7, 0
.LBB0_11:
	lw	s0, 4(sp)                       # 4-byte Folded Reload
	lw	a0, 0(s0)
	lw	s1, 0(sp)                       # 4-byte Folded Reload
	sw	a0, 0(s1)
	mv	a0, s1
	mv	a1, s0
	li	a2, 0
	call	br_i31_sub
	xori	a0, a0, 1
	or	a2, a0, s7
	mv	a0, s1
	mv	a1, s0
	lw	ra, 60(sp)                      # 4-byte Folded Reload
	lw	s0, 56(sp)                      # 4-byte Folded Reload
	lw	s1, 52(sp)                      # 4-byte Folded Reload
	lw	s2, 48(sp)                      # 4-byte Folded Reload
	lw	s3, 44(sp)                      # 4-byte Folded Reload
	lw	s4, 40(sp)                      # 4-byte Folded Reload
	lw	s5, 36(sp)                      # 4-byte Folded Reload
	lw	s6, 32(sp)                      # 4-byte Folded Reload
	lw	s7, 28(sp)                      # 4-byte Folded Reload
	lw	s8, 24(sp)                      # 4-byte Folded Reload
	lw	s9, 20(sp)                      # 4-byte Folded Reload
	lw	s10, 16(sp)                     # 4-byte Folded Reload
	lw	s11, 12(sp)                     # 4-byte Folded Reload
	addi	sp, sp, 64
	tail	br_i31_sub
.Lfunc_end0:
	.size	br_i31_montymul, .Lfunc_end0-br_i31_montymul
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
