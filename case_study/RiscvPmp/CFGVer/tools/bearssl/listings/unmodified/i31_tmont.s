	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_m2p0"
	.file	"i31_tmont.c"
	.globl	br_i31_to_monty                 # -- Begin function br_i31_to_monty
	.p2align	2
	.type	br_i31_to_monty,@function
br_i31_to_monty:                        # @br_i31_to_monty
# %bb.0:
	addi	sp, sp, -16
	sw	ra, 12(sp)                      # 4-byte Folded Spill
	sw	s0, 8(sp)                       # 4-byte Folded Spill
	sw	s1, 4(sp)                       # 4-byte Folded Spill
	sw	s2, 0(sp)                       # 4-byte Folded Spill
	mv	s0, a1
	lw	a1, 0(a1)
	addi	a1, a1, 31
	srli	s2, a1, 5
	beqz	s2, .LBB0_3
# %bb.1:
	mv	s1, a0
.LBB0_2:                                # =>This Inner Loop Header: Depth=1
	mv	a0, s1
	li	a1, 0
	mv	a2, s0
	call	br_i31_muladd_small
	addi	s2, s2, -1
	bnez	s2, .LBB0_2
.LBB0_3:
	lw	ra, 12(sp)                      # 4-byte Folded Reload
	lw	s0, 8(sp)                       # 4-byte Folded Reload
	lw	s1, 4(sp)                       # 4-byte Folded Reload
	lw	s2, 0(sp)                       # 4-byte Folded Reload
	addi	sp, sp, 16
	ret
.Lfunc_end0:
	.size	br_i31_to_monty, .Lfunc_end0-br_i31_to_monty
                                        # -- End function
	.ident	"Ubuntu clang version 18.1.3 (1ubuntu1)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
