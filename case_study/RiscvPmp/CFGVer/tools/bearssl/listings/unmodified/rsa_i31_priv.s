	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"rsa_i31_priv.c"
	.globl	br_rsa_i31_private              # -- Begin function br_rsa_i31_private
	.p2align	2
	.type	br_rsa_i31_private,@function
br_rsa_i31_private:                     # @br_rsa_i31_private
# %bb.0:
	addi	sp, sp, -2032
	sw	ra, 2028(sp)                    # 4-byte Folded Spill
	sw	s0, 2024(sp)                    # 4-byte Folded Spill
	sw	s1, 2020(sp)                    # 4-byte Folded Spill
	sw	s2, 2016(sp)                    # 4-byte Folded Spill
	sw	s3, 2012(sp)                    # 4-byte Folded Spill
	sw	s4, 2008(sp)                    # 4-byte Folded Spill
	sw	s5, 2004(sp)                    # 4-byte Folded Spill
	sw	s6, 2000(sp)                    # 4-byte Folded Spill
	sw	s7, 1996(sp)                    # 4-byte Folded Spill
	sw	s8, 1992(sp)                    # 4-byte Folded Spill
	sw	s9, 1988(sp)                    # 4-byte Folded Spill
	sw	s10, 1984(sp)                   # 4-byte Folded Spill
	sw	s11, 1980(sp)                   # 4-byte Folded Spill
	addi	sp, sp, -288
	mv	s1, a1
	lw	s5, 8(a1)
	lw	s4, 4(a1)
	mv	s8, a0
	beqz	s5, .LBB0_5
# %bb.1:
	add	a0, s4, s5
.LBB0_2:                                # =>This Inner Loop Header: Depth=1
	lbu	a1, 0(s4)
	bnez	a1, .LBB0_5
# %bb.3:                                #   in Loop: Header=BB0_2 Depth=1
	addi	s5, s5, -1
	addi	s4, s4, 1
	bnez	s5, .LBB0_2
# %bb.4:
	mv	s4, a0
.LBB0_5:
	lw	a2, 16(s1)
	lw	a1, 12(s1)
	beqz	a2, .LBB0_10
# %bb.6:
	add	a0, a1, a2
.LBB0_7:                                # =>This Inner Loop Header: Depth=1
	lbu	a3, 0(a1)
	bnez	a3, .LBB0_10
# %bb.8:                                #   in Loop: Header=BB0_7 Depth=1
	addi	a2, a2, -1
	addi	a1, a1, 1
	bnez	a2, .LBB0_7
# %bb.9:
	mv	a1, a0
.LBB0_10:
	mv	a0, s5
	bltu	a2, s5, .LBB0_12
# %bb.11:
	mv	a0, a2
.LBB0_12:
	slli	a0, a0, 3
	blez	a0, .LBB0_16
# %bb.13:
	li	a4, 31
	mv	a3, a0
	blt	a0, a4, .LBB0_15
# %bb.14:
	li	a3, 31
.LBB0_15:
	sub	a0, a0, a3
	addi	a0, a0, 30
	lui	a3, 33825
	addi	a3, a3, 133
	mulhu	a3, a0, a3
	sub	a0, a0, a3
	srli	a0, a0, 1
	add	a0, a0, a3
	srli	a0, a0, 4
	addi	s11, a0, 2
	j	.LBB0_17
.LBB0_16:
	li	s11, 1
.LBB0_17:
	andi	a0, s11, 1
	add	s11, a0, s11
	li	a0, 93
	bgeu	a0, s11, .LBB0_19
# %bb.18:
	li	a0, 0
	j	.LBB0_23
.LBB0_19:
	lw	a0, 0(s1)
	addi	a0, a0, 7
	srli	s2, a0, 3
	addi	a0, sp, 24
	addi	s7, sp, 24
	call	br_i31_decode
	slli	s6, s11, 2
	add	s3, s7, s6
	mv	a0, s3
	mv	a1, s4
	mv	a2, s5
	call	br_i31_decode
	lw	a1, 24(sp)
	slli	s4, s11, 3
	add	s4, s7, s4
	addi	a0, s4, 4
	sw	a1, 0(s4)
	addi	a1, a1, 31
	srli	a1, a1, 3
	andi	a2, a1, -4
	li	a1, 0
	call	memset
	addi	a1, sp, 24
	mv	a0, s4
	mv	a2, s3
	call	br_i31_mulacc
	slli	s5, s11, 4
	add	s5, s7, s5
	mv	a0, s5
	mv	a1, s2
	mv	a2, s4
	call	br_i31_encode
	li	s0, 0
	beqz	s2, .LBB0_22
# %bb.20:
	addi	a0, s8, -1
	addi	a1, s5, -1
	mv	a2, s2
.LBB0_21:                               # =>This Inner Loop Header: Depth=1
	add	a3, a1, a2
	lbu	a3, 0(a3)
	add	a4, a0, a2
	lbu	a4, 0(a4)
	addi	a5, a2, -1
	add	a3, s0, a3
	sub	a4, a4, a3
	slli	a4, a4, 23
	srli	s0, a4, 31
	mv	a2, a5
	bnez	a5, .LBB0_21
.LBB0_22:
	mv	a0, s4
	mv	a1, s3
	mv	a2, s6
	call	memmove
	lw	a0, 28(sp)
	call	br_i31_ninv31
	mv	s10, a0
	sw	a0, 20(sp)                      # 4-byte Folded Spill
	addi	a3, sp, 24
	mv	a0, s3
	mv	a1, s8
	mv	a2, s2
	call	br_i31_decode_reduce
	lw	a1, 28(s1)
	lw	a2, 32(s1)
	slli	a0, s11, 1
	add	a0, a0, s11
	slli	s9, a0, 2
	add	s9, s7, s9
	mv	s7, s8
	li	s8, 560
	sub	a6, s8, a0
	addi	a3, sp, 24
	mv	a0, s3
	mv	a4, s10
	mv	a5, s9
	call	br_i31_modpow_opt
	lw	a1, 4(s4)
	sw	a0, 16(sp)                      # 4-byte Folded Spill
	mv	a0, a1
	call	br_i31_ninv31
	mv	s10, a0
	mv	a0, s9
	mv	a1, s7
	mv	a2, s2
	mv	a3, s4
	call	br_i31_decode_reduce
	lw	a1, 20(s1)
	lw	a2, 24(s1)
	sub	a6, s8, s6
	mv	a0, s9
	mv	a3, s4
	mv	a4, s10
	mv	a5, s5
	call	br_i31_modpow_opt
	mv	s6, a0
	li	a0, 20
	mul	s11, s11, a0
	addi	a0, sp, 24
	add	s11, a0, s11
	mv	a0, s11
	mv	a1, s3
	mv	a2, s4
	call	br_i31_reduce
	li	a2, 1
	mv	a0, s9
	mv	a1, s11
	call	br_i31_sub
	mv	a2, a0
	mv	a0, s9
	mv	a1, s4
	call	br_i31_add
	mv	a0, s9
	mv	a1, s4
	call	br_i31_to_monty
	lw	a1, 36(s1)
	lw	a2, 40(s1)
	mv	a0, s5
	mv	a3, s4
	call	br_i31_decode_reduce
	mv	a0, s11
	mv	a1, s9
	mv	a2, s5
	mv	a3, s4
	mv	a4, s10
	call	br_i31_montymul
	addi	a1, sp, 24
	mv	a0, s3
	mv	a2, s11
	call	br_i31_mulacc
	mv	a0, s7
	mv	a1, s2
	mv	a2, s3
	call	br_i31_encode
	lw	a0, 16(sp)                      # 4-byte Folded Reload
	and	a0, a0, s6
	lw	a1, 20(sp)                      # 4-byte Folded Reload
	and	a0, a0, a1
	and	a0, a0, s10
	and	a0, s0, a0
.LBB0_23:
	addi	sp, sp, 288
	lw	ra, 2028(sp)                    # 4-byte Folded Reload
	lw	s0, 2024(sp)                    # 4-byte Folded Reload
	lw	s1, 2020(sp)                    # 4-byte Folded Reload
	lw	s2, 2016(sp)                    # 4-byte Folded Reload
	lw	s3, 2012(sp)                    # 4-byte Folded Reload
	lw	s4, 2008(sp)                    # 4-byte Folded Reload
	lw	s5, 2004(sp)                    # 4-byte Folded Reload
	lw	s6, 2000(sp)                    # 4-byte Folded Reload
	lw	s7, 1996(sp)                    # 4-byte Folded Reload
	lw	s8, 1992(sp)                    # 4-byte Folded Reload
	lw	s9, 1988(sp)                    # 4-byte Folded Reload
	lw	s10, 1984(sp)                   # 4-byte Folded Reload
	lw	s11, 1980(sp)                   # 4-byte Folded Reload
	addi	sp, sp, 2032
	ret
.Lfunc_end0:
	.size	br_rsa_i31_private, .Lfunc_end0-br_rsa_i31_private
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
