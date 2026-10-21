	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_mulacc.c"
	.globl	br_i31_mulacc                   # -- Begin function br_i31_mulacc
	.p2align	2
	.type	br_i31_mulacc,@function
br_i31_mulacc:                          # @br_i31_mulacc
# %bb.0:
	lw	a4, 0(a2)
	lw	a5, 0(a1)
	addi	a3, a4, 31
	srli	a3, a3, 5
	andi	a6, a5, 31
	andi	a7, a4, 31
	add	a6, a7, a6
	andi	a7, a5, -32
	add	a4, a4, a7
	andi	a4, a4, -32
	add	a4, a4, a6
	sltiu	a6, a6, 31
	xori	a6, a6, 1
	add	a4, a4, a6
	sw	a4, 0(a0)
	beqz	a3, .LBB0_8
# %bb.1:
	addi	sp, sp, -16
	sw	s0, 12(sp)                      # 4-byte Folded Spill
	sw	s1, 8(sp)                       # 4-byte Folded Spill
	li	a4, 0
	addi	a5, a5, 31
	srli	a6, a5, 5
	slli	a7, a6, 2
	add	a6, a0, a7
	addi	a1, a1, 4
	addi	a0, a0, 4
	add	a7, a1, a7
	li	t0, 32
	j	.LBB0_4
.LBB0_2:                                #   in Loop: Header=BB0_4 Depth=1
	li	t5, 0
.LBB0_3:                                #   in Loop: Header=BB0_4 Depth=1
	add	t1, a6, t1
	sw	t5, 0(t1)
	addi	a0, a0, 4
	beq	a4, a3, .LBB0_7
.LBB0_4:                                # =>This Loop Header: Depth=1
                                        #     Child Loop BB0_6 Depth 2
	addi	a4, a4, 1
	slli	t1, a4, 2
	bltu	a5, t0, .LBB0_2
# %bb.5:                                #   in Loop: Header=BB0_4 Depth=1
	add	t2, a2, t1
	lw	t2, 0(t2)
	li	t5, 0
	mv	t3, a0
	mv	t4, a1
.LBB0_6:                                #   Parent Loop BB0_4 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	lw	t6, 0(t4)
	lw	s0, 0(t3)
	mulhu	s1, t6, t2
	mul	t6, t6, t2
	add	t5, s0, t5
	sltu	s0, t5, s0
	add	t6, t5, t6
	sltu	t5, t6, t5
	add	s0, s0, s1
	add	t5, s0, t5
	slli	t5, t5, 1
	srli	s0, t6, 31
	or	t5, s0, t5
	slli	t6, t6, 1
	srli	t6, t6, 1
	sw	t6, 0(t3)
	addi	t4, t4, 4
	addi	t3, t3, 4
	bne	t4, a7, .LBB0_6
	j	.LBB0_3
.LBB0_7:
	lw	s0, 12(sp)                      # 4-byte Folded Reload
	lw	s1, 8(sp)                       # 4-byte Folded Reload
	addi	sp, sp, 16
.LBB0_8:
	ret
.Lfunc_end0:
	.size	br_i31_mulacc, .Lfunc_end0-br_i31_mulacc
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
