	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_fmont.c"
	.globl	br_i31_from_monty               # -- Begin function br_i31_from_monty
	.p2align	2
	.type	br_i31_from_monty,@function
br_i31_from_monty:                      # @br_i31_from_monty
# %bb.0:
	addi	sp, sp, -32
	sw	ra, 28(sp)                      # 4-byte Folded Spill
	sw	s0, 24(sp)                      # 4-byte Folded Spill
	sw	s1, 20(sp)                      # 4-byte Folded Spill
	sw	s2, 16(sp)                      # 4-byte Folded Spill
	sw	s3, 12(sp)                      # 4-byte Folded Spill
	lw	a3, 0(a1)
	addi	a3, a3, 31
	srli	a3, a3, 5
	beqz	a3, .LBB0_6
# %bb.1:
	li	a4, 0
	lui	a5, 524288
	addi	a5, a5, -1
	slli	t1, a3, 2
	add	a6, a0, t1
	addi	a7, a1, 8
	addi	t0, a0, 8
	add	t1, t1, a1
	addi	t1, t1, 4
	li	t2, 1
	j	.LBB0_3
.LBB0_2:                                #   in Loop: Header=BB0_3 Depth=1
	addi	a4, a4, 1
	sw	t4, 0(a6)
	beq	a4, a3, .LBB0_6
.LBB0_3:                                # =>This Loop Header: Depth=1
                                        #     Child Loop BB0_5 Depth 2
	lw	t4, 4(a0)
	lw	t5, 4(a1)
	mul	t3, t4, a2
	and	t3, t3, a5
	mulhu	s0, t5, t3
	mul	t5, t5, t3
	add	t4, t5, t4
	sltu	t5, t4, t5
	add	s0, s0, t5
	slli	t5, s0, 1
	srli	t4, t4, 31
	or	t4, t4, t5
	beq	a3, t2, .LBB0_2
# %bb.4:                                #   in Loop: Header=BB0_3 Depth=1
	srli	s0, s0, 31
	mv	t5, t0
	mv	t6, a7
.LBB0_5:                                #   Parent Loop BB0_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	lw	s1, 0(t6)
	lw	s2, 0(t5)
	mulhu	s3, s1, t3
	mul	s1, s1, t3
	add	s2, t4, s2
	sltu	t4, s2, t4
	add	s1, s2, s1
	sltu	s2, s1, s2
	add	s0, s0, s3
	add	t4, s0, t4
	add	s0, t4, s2
	slli	t4, s0, 1
	srli	s2, s1, 31
	or	t4, s2, t4
	srli	s0, s0, 31
	and	s1, s1, a5
	sw	s1, -4(t5)
	addi	t6, t6, 4
	addi	t5, t5, 4
	bne	t6, t1, .LBB0_5
	j	.LBB0_2
.LBB0_6:
	mv	s0, a0
	mv	s1, a1
	li	a2, 0
	call	br_i31_sub
	xori	a2, a0, 1
	mv	a0, s0
	mv	a1, s1
	lw	ra, 28(sp)                      # 4-byte Folded Reload
	lw	s0, 24(sp)                      # 4-byte Folded Reload
	lw	s1, 20(sp)                      # 4-byte Folded Reload
	lw	s2, 16(sp)                      # 4-byte Folded Reload
	lw	s3, 12(sp)                      # 4-byte Folded Reload
	addi	sp, sp, 32
	tail	br_i31_sub
.Lfunc_end0:
	.size	br_i31_from_monty, .Lfunc_end0-br_i31_from_monty
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
