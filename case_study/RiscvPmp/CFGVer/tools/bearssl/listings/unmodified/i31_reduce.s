	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_reduce.c"
	.globl	br_i31_reduce                   # -- Begin function br_i31_reduce
	.p2align	2
	.type	br_i31_reduce,@function
br_i31_reduce:                          # @br_i31_reduce
# %bb.0:
	addi	sp, sp, -32
	sw	ra, 28(sp)                      # 4-byte Folded Spill
	sw	s0, 24(sp)                      # 4-byte Folded Spill
	sw	s1, 20(sp)                      # 4-byte Folded Spill
	sw	s2, 16(sp)                      # 4-byte Folded Spill
	sw	s3, 12(sp)                      # 4-byte Folded Spill
	sw	s4, 8(sp)                       # 4-byte Folded Spill
	sw	s5, 4(sp)                       # 4-byte Folded Spill
	sw	s6, 0(sp)                       # 4-byte Folded Spill
	mv	s1, a2
	lw	a2, 0(a2)
	sw	a2, 0(a0)
	beqz	a2, .LBB0_8
# %bb.1:
	mv	s0, a0
	lw	a3, 0(a1)
	addi	a0, a2, 31
	srli	s2, a0, 5
	addi	a0, a3, 31
	srli	s3, a0, 5
	addi	a0, s0, 4
	bgeu	a3, a2, .LBB0_5
# %bb.2:
	addi	a1, a1, 4
	slli	s1, s3, 2
	mv	a2, s1
	call	memcpy
	bgeu	s3, s2, .LBB0_8
# %bb.3:
	add	a0, s1, s0
	addi	a0, a0, 4
	slli	s2, s2, 2
	add	a1, s2, s0
	addi	a1, a1, 4
.LBB0_4:                                # =>This Inner Loop Header: Depth=1
	sw	zero, 0(a0)
	addi	a0, a0, 4
	bne	a0, a1, .LBB0_4
	j	.LBB0_8
.LBB0_5:
	sub	s6, s3, s2
	slli	a2, s6, 2
	add	a2, a1, a2
	addi	a3, a2, 8
	slli	s4, s2, 2
	addi	a2, s4, -4
	mv	s5, a1
	mv	a1, a3
	call	memcpy
	add	a1, s0, s4
	li	a2, -1
	sw	zero, 0(a1)
	beq	s6, a2, .LBB0_8
# %bb.6:
	mv	a0, s5
	not	a1, s3
	add	s2, a1, s2
	slli	s3, s3, 2
	sub	a1, s3, s4
	add	a0, a1, s5
	addi	s3, a0, 4
.LBB0_7:                                # =>This Inner Loop Header: Depth=1
	lw	a1, 0(s3)
	mv	a0, s0
	mv	a2, s1
	call	br_i31_muladd_small
	addi	s2, s2, 1
	addi	s3, s3, -4
	bnez	s2, .LBB0_7
.LBB0_8:
	lw	ra, 28(sp)                      # 4-byte Folded Reload
	lw	s0, 24(sp)                      # 4-byte Folded Reload
	lw	s1, 20(sp)                      # 4-byte Folded Reload
	lw	s2, 16(sp)                      # 4-byte Folded Reload
	lw	s3, 12(sp)                      # 4-byte Folded Reload
	lw	s4, 8(sp)                       # 4-byte Folded Reload
	lw	s5, 4(sp)                       # 4-byte Folded Reload
	lw	s6, 0(sp)                       # 4-byte Folded Reload
	addi	sp, sp, 32
	ret
.Lfunc_end0:
	.size	br_i31_reduce, .Lfunc_end0-br_i31_reduce
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
