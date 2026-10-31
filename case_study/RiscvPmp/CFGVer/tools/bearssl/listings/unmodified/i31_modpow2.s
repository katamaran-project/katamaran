	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_modpow2.c"
	.globl	br_i31_modpow_opt               # -- Begin function br_i31_modpow_opt
	.p2align	2
	.type	br_i31_modpow_opt,@function
br_i31_modpow_opt:                      # @br_i31_modpow_opt
# %bb.0:
	addi	sp, sp, -112
	sw	ra, 108(sp)                     # 4-byte Folded Spill
	sw	s0, 104(sp)                     # 4-byte Folded Spill
	sw	s1, 100(sp)                     # 4-byte Folded Spill
	sw	s2, 96(sp)                      # 4-byte Folded Spill
	sw	s3, 92(sp)                      # 4-byte Folded Spill
	sw	s4, 88(sp)                      # 4-byte Folded Spill
	sw	s5, 84(sp)                      # 4-byte Folded Spill
	sw	s6, 80(sp)                      # 4-byte Folded Spill
	sw	s7, 76(sp)                      # 4-byte Folded Spill
	sw	s8, 72(sp)                      # 4-byte Folded Spill
	sw	s9, 68(sp)                      # 4-byte Folded Spill
	sw	s10, 64(sp)                     # 4-byte Folded Spill
	sw	s11, 60(sp)                     # 4-byte Folded Spill
	mv	s0, a3
	lw	a3, 0(a3)
	addi	a3, a3, 63
	srli	s4, a3, 5
	andi	a3, s4, 1
	add	s2, a3, s4
	slli	a3, s2, 1
	bgeu	a6, a3, .LBB0_2
# %bb.1:
	li	a0, 0
	j	.LBB0_33
.LBB0_2:
	mv	s5, a5
	mv	s1, a4
	mv	s7, a2
	mv	s6, a1
	mv	s3, a0
	slli	s4, s4, 2
	slli	s11, s2, 2
	add	a0, a5, s11
	sw	a0, 48(sp)                      # 4-byte Folded Spill
	slli	a0, s2, 5
	add	a0, a0, s2
	li	s10, 5
	sw	s2, 40(sp)                      # 4-byte Folded Spill
	sw	a1, 20(sp)                      # 4-byte Folded Spill
	bgeu	a6, a0, .LBB0_7
# %bb.3:
	slli	a0, s2, 4
	add	a0, a0, s2
	li	s10, 4
	bgeu	a6, a0, .LBB0_7
# %bb.4:
	slli	a0, s2, 3
	add	a0, a0, s2
	li	s10, 3
	bgeu	a6, a0, .LBB0_7
# %bb.5:
	add	a0, s11, s2
	li	s10, 2
	bgeu	a6, a0, .LBB0_7
# %bb.6:
	mv	a0, s3
	mv	a1, s0
	call	br_i31_to_monty
	lw	a0, 48(sp)                      # 4-byte Folded Reload
	mv	a1, s3
	mv	a2, s4
	call	memcpy
	sw	zero, 36(sp)                    # 4-byte Folded Spill
	li	s10, 1
	j	.LBB0_10
.LBB0_7:
	mv	a0, s3
	mv	a1, s0
	call	br_i31_to_monty
	lw	s8, 48(sp)                      # 4-byte Folded Reload
	add	s8, s8, s11
	mv	a0, s8
	mv	a1, s3
	mv	a2, s4
	call	memcpy
	li	a0, 12
	mul	s9, s2, a0
	add	s9, s5, s9
	li	s2, 3
.LBB0_8:                                # =>This Inner Loop Header: Depth=1
	mv	a0, s9
	mv	a1, s8
	mv	a2, s3
	mv	a3, s0
	mv	a4, s1
	call	br_i31_montymul
	srl	a0, s2, s10
	addi	s2, s2, 1
	add	s9, s9, s11
	add	s8, s8, s11
	beqz	a0, .LBB0_8
# %bb.9:
	li	a0, 1
	sw	a0, 36(sp)                      # 4-byte Folded Spill
	lw	s2, 40(sp)                      # 4-byte Folded Reload
.LBB0_10:
	lw	a1, 0(s0)
	addi	a0, s3, 4
	sw	a1, 0(s3)
	addi	a1, a1, 31
	srli	a1, a1, 3
	andi	a2, a1, -4
	li	a1, 0
	call	memset
	lw	a0, 0(s0)
	addi	a0, a0, 31
	srli	a0, a0, 3
	andi	a0, a0, -4
	add	a0, s3, a0
	li	a1, 1
	sw	a1, 0(a0)
	mv	a0, s3
	li	a1, 0
	mv	a2, s0
	call	br_i31_muladd_small
	beqz	s7, .LBB0_32
# %bb.11:
	li	s6, 0
	sw	zero, 44(sp)                    # 4-byte Folded Spill
	lui	a0, 131072
	addi	a0, a0, -4
	sw	a0, 16(sp)                      # 4-byte Folded Spill
	lw	a0, 48(sp)                      # 4-byte Folded Reload
	addi	a3, a0, 4
	li	a0, 1
	sll	a0, a0, s10
	sw	a0, 28(sp)                      # 4-byte Folded Spill
	addi	a0, a0, -1
	sw	a0, 24(sp)                      # 4-byte Folded Spill
	slli	s2, s2, 3
	add	s2, s5, s2
	addi	a0, s2, 4
	sw	a0, 12(sp)                      # 4-byte Folded Spill
	li	a0, 1
	sw	s10, 32(sp)                     # 4-byte Folded Spill
	sw	a3, 56(sp)                      # 4-byte Folded Spill
.LBB0_12:                               # =>This Loop Header: Depth=1
                                        #     Child Loop BB0_18 Depth 2
                                        #     Child Loop BB0_26 Depth 2
                                        #       Child Loop BB0_28 Depth 3
	bge	s6, s10, .LBB0_15
# %bb.13:                               #   in Loop: Header=BB0_12 Depth=1
	andi	a0, a0, 1
	beqz	a0, .LBB0_31
# %bb.14:                               #   in Loop: Header=BB0_12 Depth=1
	lw	a2, 20(sp)                      # 4-byte Folded Reload
	lbu	a0, 0(a2)
	lw	a1, 44(sp)                      # 4-byte Folded Reload
	slli	a1, a1, 8
	addi	a2, a2, 1
	or	a0, a1, a0
	sw	a0, 44(sp)                      # 4-byte Folded Spill
	addi	s7, s7, -1
	sw	s7, 52(sp)                      # 4-byte Folded Spill
	addi	s6, s6, 8
	sw	a2, 20(sp)                      # 4-byte Folded Spill
	j	.LBB0_16
.LBB0_15:                               #   in Loop: Header=BB0_12 Depth=1
	sw	s7, 52(sp)                      # 4-byte Folded Spill
.LBB0_16:                               #   in Loop: Header=BB0_12 Depth=1
	sub	s8, s6, s10
	lw	a0, 44(sp)                      # 4-byte Folded Reload
	srl	a0, a0, s8
	lw	a1, 24(sp)                      # 4-byte Folded Reload
	and	s7, a0, a1
	lw	s9, 28(sp)                      # 4-byte Folded Reload
	mv	s6, s10
.LBB0_17:                               #   in Loop: Header=BB0_12 Depth=1
	mv	s10, s6
.LBB0_18:                               #   Parent Loop BB0_12 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	mv	a0, s5
	mv	a1, s3
	mv	a2, s3
	mv	a3, s0
	mv	a4, s1
	call	br_i31_montymul
	mv	a0, s3
	mv	a1, s5
	mv	a2, s4
	call	memcpy
	addi	s10, s10, -1
	bnez	s10, .LBB0_18
# %bb.19:                               #   in Loop: Header=BB0_12 Depth=1
	mv	s10, s6
	lw	a3, 56(sp)                      # 4-byte Folded Reload
.LBB0_20:                               #   in Loop: Header=BB0_12 Depth=1
	mv	s6, s8
	lw	s8, 40(sp)                      # 4-byte Folded Reload
	lw	a0, 36(sp)                      # 4-byte Folded Reload
	beqz	a0, .LBB0_29
# %bb.21:                               #   in Loop: Header=BB0_12 Depth=1
	lw	a0, 0(s0)
	lw	a1, 48(sp)                      # 4-byte Folded Reload
	sw	a0, 0(a1)
	addi	a0, a0, 31
	srli	a0, a0, 3
	lw	a2, 16(sp)                      # 4-byte Folded Reload
	and	a2, a0, a2
	mv	a0, a3
	li	a1, 0
	call	memset
	li	t0, 2
	lw	a7, 56(sp)                      # 4-byte Folded Reload
	beqz	s10, .LBB0_29
# %bb.22:                               #   in Loop: Header=BB0_12 Depth=1
	li	a0, 2
	bltu	a0, s9, .LBB0_24
# %bb.23:                               #   in Loop: Header=BB0_12 Depth=1
	li	s9, 2
.LBB0_24:                               #   in Loop: Header=BB0_12 Depth=1
	li	a0, 1
	lw	a1, 12(sp)                      # 4-byte Folded Reload
	j	.LBB0_26
.LBB0_25:                               #   in Loop: Header=BB0_26 Depth=2
	addi	a0, a0, 1
	add	a1, a1, s11
	beq	a0, s9, .LBB0_29
.LBB0_26:                               #   Parent Loop BB0_12 Depth=1
                                        # =>  This Loop Header: Depth=2
                                        #       Child Loop BB0_28 Depth 3
	bltu	s8, t0, .LBB0_25
# %bb.27:                               #   in Loop: Header=BB0_26 Depth=2
	mv	a2, a1
	mv	a3, a7
.LBB0_28:                               #   Parent Loop BB0_12 Depth=1
                                        #     Parent Loop BB0_26 Depth=2
                                        # =>    This Inner Loop Header: Depth=3
	xor	a4, a0, s7
	lw	a5, 0(a2)
	lw	a6, 0(a3)
	snez	a4, a4
	addi	a4, a4, -1
	and	a4, a4, a5
	or	a4, a6, a4
	sw	a4, 0(a3)
	addi	a3, a3, 4
	addi	a2, a2, 4
	bne	a3, s2, .LBB0_28
	j	.LBB0_25
.LBB0_29:                               #   in Loop: Header=BB0_12 Depth=1
	mv	a0, s5
	mv	a1, s3
	lw	a2, 48(sp)                      # 4-byte Folded Reload
	mv	a3, s0
	mv	a4, s1
	call	br_i31_montymul
	snez	a0, s7
	mv	a1, s3
	mv	a2, s5
	mv	a3, s4
	call	br_ccopy
	lw	a3, 56(sp)                      # 4-byte Folded Reload
	lw	s7, 52(sp)                      # 4-byte Folded Reload
	snez	a0, s7
	lw	s10, 32(sp)                     # 4-byte Folded Reload
	bgtz	s6, .LBB0_12
# %bb.30:                               #   in Loop: Header=BB0_12 Depth=1
	bnez	s7, .LBB0_12
	j	.LBB0_32
.LBB0_31:                               #   in Loop: Header=BB0_12 Depth=1
	li	s8, 0
	sw	zero, 52(sp)                    # 4-byte Folded Spill
	li	a0, 1
	sll	s9, a0, s6
	addi	a0, s9, -1
	lw	a1, 44(sp)                      # 4-byte Folded Reload
	and	s7, a1, a0
	mv	s10, s6
	bgtz	s6, .LBB0_17
	j	.LBB0_20
.LBB0_32:
	mv	a0, s3
	mv	a1, s0
	mv	a2, s1
	call	br_i31_from_monty
	li	a0, 1
.LBB0_33:
	lw	ra, 108(sp)                     # 4-byte Folded Reload
	lw	s0, 104(sp)                     # 4-byte Folded Reload
	lw	s1, 100(sp)                     # 4-byte Folded Reload
	lw	s2, 96(sp)                      # 4-byte Folded Reload
	lw	s3, 92(sp)                      # 4-byte Folded Reload
	lw	s4, 88(sp)                      # 4-byte Folded Reload
	lw	s5, 84(sp)                      # 4-byte Folded Reload
	lw	s6, 80(sp)                      # 4-byte Folded Reload
	lw	s7, 76(sp)                      # 4-byte Folded Reload
	lw	s8, 72(sp)                      # 4-byte Folded Reload
	lw	s9, 68(sp)                      # 4-byte Folded Reload
	lw	s10, 64(sp)                     # 4-byte Folded Reload
	lw	s11, 60(sp)                     # 4-byte Folded Reload
	addi	sp, sp, 112
	ret
.Lfunc_end0:
	.size	br_i31_modpow_opt, .Lfunc_end0-br_i31_modpow_opt
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
