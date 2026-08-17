#!/usr/bin/env python3
"""
Translate RV32I assembly (as pasted from e.g. Compiler Explorer) into a
Katamaran `list AST` literal (case_study/RiscvPmp/Base.v).

Design goal: TRUSTWORTHINESS over cleverness. This script never tries to
infer what a register "means" (e.g. "a5 := y[0]") -- that requires actually
understanding the program and would be exactly the kind of manual,
error-prone step we want to remove. Instead every generated AST term is
tagged with the verbatim source line it came from, so the translation can
be checked instruction-by-instruction against the original assembly.

Supported: the RV32I base integer instructions plus the M-extension mul*
ops and the common pseudo-instructions (neg, mv, not, seqz, snez, sltz,
sgtz, beqz/bnez/blez/bgez/bltz/bgtz, j, jr, jal/jalr 1-operand forms, ret,
nop, li). Anything else (CSR ops, atomics, F/D, la/call/tail, compressed
mnemonics, RV64-only ops like ld/sd) is rejected with an explicit error --
this script refuses to guess.

Local, same-listing labels are resolved to PC-relative byte offsets for
branches/jal, so loops (e.g. a future jmp_bwd example) are supported.

Usage:
    python3 asm_to_ast.py input.s --name cmovznz4 --drop-ret > out.v
    cat input.s | python3 asm_to_ast.py --name cmovznz4
"""
import argparse
import re
import sys

ABI_NAMES = [
    'zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1',
    'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
    's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11',
    't3', 't4', 't5', 't6',
]
NAME_TO_X = {name: i for i, name in enumerate(ABI_NAMES)}
NAME_TO_X.update({f'x{i}': i for i in range(32)})
NAME_TO_X['fp'] = 8


class AsmError(Exception):
    pass


def canonical_reg(tok):
    key = tok.strip().lower()
    if key not in NAME_TO_X:
        raise AsmError(f"unknown register {tok!r}")
    return ABI_NAMES[NAME_TO_X[key]]


INT_RE = re.compile(r'^-?\d+$')
MEM_RE = re.compile(r'^(-?\d+)\(([A-Za-z][\w]*)\)$')
LABEL_DEF_RE = re.compile(r'^([.\w$][\w.$]*):$')


def is_int(tok):
    return bool(INT_RE.match(tok))


RTYPE_OPS = {
    'add': 'RISCV_ADD', 'sub': 'RISCV_SUB', 'and': 'RISCV_AND',
    'or': 'RISCV_OR', 'xor': 'RISCV_XOR', 'sll': 'RISCV_SLL',
    'srl': 'RISCV_SRL', 'sra': 'RISCV_SRA', 'slt': 'RISCV_SLT',
    'sltu': 'RISCV_SLTU',
}
ITYPE_OPS = {
    'addi': 'RISCV_ADDI', 'slti': 'RISCV_SLTI', 'sltiu': 'RISCV_SLTIU',
    'andi': 'RISCV_ANDI', 'ori': 'RISCV_ORI', 'xori': 'RISCV_XORI',
}
SHIFTIOP_OPS = {'slli': 'RISCV_SLLI', 'srli': 'RISCV_SRLI', 'srai': 'RISCV_SRAI'}
UTYPE_OPS = {'lui': 'RISCV_LUI', 'auipc': 'RISCV_AUIPC'}
BTYPE_OPS = {
    'beq': 'RISCV_BEQ', 'bne': 'RISCV_BNE', 'blt': 'RISCV_BLT',
    'bge': 'RISCV_BGE', 'bltu': 'RISCV_BLTU', 'bgeu': 'RISCV_BGEU',
}
LOAD_OPS = {
    'lb': ('BYTE', False), 'lbu': ('BYTE', True),
    'lh': ('HALF', False), 'lhu': ('HALF', True),
    'lw': ('WORD', False),
}
STORE_OPS = {'sb': 'BYTE', 'sh': 'HALF', 'sw': 'WORD'}
MUL_OPS = {
    'mul': (False, True, True), 'mulh': (True, True, True),
    'mulhsu': (True, True, False), 'mulhu': (True, False, False),
}
NULLARY_OPS = {'ecall': 'ECALL', 'ebreak': 'EBREAK', 'mret': 'MRET'}


def split_operands(s):
    s = s.strip()
    if not s:
        return []
    return [tok.strip() for tok in s.split(',')]


def li_split(imm):
    """Return (hi20, lo12) such that (hi20 << 12) + lo12 == imm, lo12 signed."""
    lo = imm & 0xFFF
    if lo >= 0x800:
        lo -= 0x1000
    hi = (imm - lo) >> 12
    return hi, lo


def expand(mnemonic, ops):
    """Expand one source instruction (real or pseudo) into a list of
    canonical instruction dicts. Raises AsmError for anything unsupported."""
    m = mnemonic.lower()

    if m in RTYPE_OPS:
        rd, rs1, rs2 = ops
        return [{'kind': 'RTYPE', 'op': RTYPE_OPS[m],
                  'rd': canonical_reg(rd), 'rs1': canonical_reg(rs1), 'rs2': canonical_reg(rs2)}]

    if m in ITYPE_OPS:
        rd, rs1, imm = ops
        if not is_int(imm):
            raise AsmError(f"{m}: expected numeric immediate, got {imm!r}")
        return [{'kind': 'ITYPE', 'op': ITYPE_OPS[m],
                  'rd': canonical_reg(rd), 'rs1': canonical_reg(rs1), 'imm': int(imm)}]

    if m in SHIFTIOP_OPS:
        rd, rs1, shamt = ops
        if not is_int(shamt):
            raise AsmError(f"{m}: expected numeric shamt, got {shamt!r}")
        return [{'kind': 'SHIFTIOP', 'op': SHIFTIOP_OPS[m],
                  'rd': canonical_reg(rd), 'rs1': canonical_reg(rs1), 'shamt': int(shamt)}]

    if m in UTYPE_OPS:
        rd, imm = ops
        if not is_int(imm):
            raise AsmError(f"{m}: expected numeric immediate, got {imm!r}")
        return [{'kind': 'UTYPE', 'op': UTYPE_OPS[m],
                  'rd': canonical_reg(rd), 'imm': int(imm)}]

    if m in BTYPE_OPS:
        rs1, rs2, imm = ops
        return [{'kind': 'BTYPE', 'op': BTYPE_OPS[m],
                  'rs1': canonical_reg(rs1), 'rs2': canonical_reg(rs2), 'imm': imm}]

    if m in LOAD_OPS:
        rd, mem = ops
        mm = MEM_RE.match(mem)
        if not mm:
            raise AsmError(f"{m}: expected imm(reg) operand, got {mem!r}")
        width, unsigned = LOAD_OPS[m]
        return [{'kind': 'LOAD', 'rd': canonical_reg(rd), 'rs1': canonical_reg(mm.group(2)),
                  'imm': int(mm.group(1)), 'unsigned': unsigned, 'width': width}]

    if m in STORE_OPS:
        rs2, mem = ops
        mm = MEM_RE.match(mem)
        if not mm:
            raise AsmError(f"{m}: expected imm(reg) operand, got {mem!r}")
        return [{'kind': 'STORE', 'rs2': canonical_reg(rs2), 'rs1': canonical_reg(mm.group(2)),
                  'imm': int(mm.group(1)), 'width': STORE_OPS[m]}]

    if m in MUL_OPS:
        rd, rs1, rs2 = ops
        high, s1, s2 = MUL_OPS[m]
        return [{'kind': 'MUL', 'rd': canonical_reg(rd), 'rs1': canonical_reg(rs1),
                  'rs2': canonical_reg(rs2), 'high': high, 'signed1': s1, 'signed2': s2}]

    if m in NULLARY_OPS:
        return [{'kind': 'NULLARY', 'op': NULLARY_OPS[m]}]

    if m == 'jal':
        if len(ops) == 2:
            rd, imm = ops
        elif len(ops) == 1:
            rd, (imm,) = 'ra', ops
        else:
            raise AsmError("jal: expected 1 or 2 operands")
        return [{'kind': 'JAL', 'rd': canonical_reg(rd), 'imm': imm}]

    if m == 'j':
        (imm,) = ops
        return [{'kind': 'JAL', 'rd': 'zero', 'imm': imm}]

    if m == 'jalr':
        if len(ops) == 1:
            return [{'kind': 'JALR', 'rd': 'ra', 'rs1': canonical_reg(ops[0]), 'imm': 0}]
        if len(ops) == 2:
            rd, mem = ops
            mm = MEM_RE.match(mem)
            if mm:
                return [{'kind': 'JALR', 'rd': canonical_reg(rd),
                          'rs1': canonical_reg(mm.group(2)), 'imm': int(mm.group(1))}]
            raise AsmError(f"jalr: unrecognised 2-operand form {ops!r}")
        if len(ops) == 3:
            rd, rs1, imm = ops
            if not is_int(imm):
                raise AsmError(f"jalr: expected numeric immediate, got {imm!r}")
            return [{'kind': 'JALR', 'rd': canonical_reg(rd), 'rs1': canonical_reg(rs1), 'imm': int(imm)}]
        raise AsmError("jalr: unsupported operand count")

    if m == 'jr':
        (rs1,) = ops
        return [{'kind': 'JALR', 'rd': 'zero', 'rs1': canonical_reg(rs1), 'imm': 0}]

    if m == 'ret':
        return [{'kind': 'JALR', 'rd': 'zero', 'rs1': 'ra', 'imm': 0}]

    if m == 'nop':
        return [{'kind': 'ITYPE', 'op': 'RISCV_ADDI', 'rd': 'zero', 'rs1': 'zero', 'imm': 0}]

    if m == 'mv':
        rd, rs1 = ops
        return [{'kind': 'ITYPE', 'op': 'RISCV_ADDI',
                  'rd': canonical_reg(rd), 'rs1': canonical_reg(rs1), 'imm': 0}]

    if m == 'not':
        rd, rs1 = ops
        return [{'kind': 'ITYPE', 'op': 'RISCV_XORI',
                  'rd': canonical_reg(rd), 'rs1': canonical_reg(rs1), 'imm': -1}]

    if m == 'neg':
        rd, rs1 = ops
        return [{'kind': 'RTYPE', 'op': 'RISCV_SUB',
                  'rd': canonical_reg(rd), 'rs1': 'zero', 'rs2': canonical_reg(rs1)}]

    if m == 'seqz':
        rd, rs1 = ops
        return [{'kind': 'ITYPE', 'op': 'RISCV_SLTIU',
                  'rd': canonical_reg(rd), 'rs1': canonical_reg(rs1), 'imm': 1}]

    if m == 'snez':
        rd, rs1 = ops
        return [{'kind': 'RTYPE', 'op': 'RISCV_SLTU',
                  'rd': canonical_reg(rd), 'rs1': 'zero', 'rs2': canonical_reg(rs1)}]

    if m == 'sltz':
        rd, rs1 = ops
        return [{'kind': 'RTYPE', 'op': 'RISCV_SLT',
                  'rd': canonical_reg(rd), 'rs1': canonical_reg(rs1), 'rs2': 'zero'}]

    if m == 'sgtz':
        rd, rs1 = ops
        return [{'kind': 'RTYPE', 'op': 'RISCV_SLT',
                  'rd': canonical_reg(rd), 'rs1': 'zero', 'rs2': canonical_reg(rs1)}]

    if m in ('beqz', 'bnez', 'blez', 'bgez', 'bltz', 'bgtz'):
        rs1, imm = ops
        rs1 = canonical_reg(rs1)
        table = {
            'beqz': ('RISCV_BEQ', rs1, 'zero'), 'bnez': ('RISCV_BNE', rs1, 'zero'),
            'blez': ('RISCV_BGE', 'zero', rs1), 'bgez': ('RISCV_BGE', rs1, 'zero'),
            'bltz': ('RISCV_BLT', rs1, 'zero'), 'bgtz': ('RISCV_BLT', 'zero', rs1),
        }
        op, a, b = table[m]
        return [{'kind': 'BTYPE', 'op': op, 'rs1': a, 'rs2': b, 'imm': imm}]

    if m == 'li':
        rd, imm = ops
        if not is_int(imm):
            raise AsmError(f"li: expected numeric immediate, got {imm!r}")
        rd = canonical_reg(rd)
        val = int(imm)
        if -2048 <= val <= 2047:
            return [{'kind': 'ITYPE', 'op': 'RISCV_ADDI', 'rd': rd, 'rs1': 'zero', 'imm': val}]
        hi, lo = li_split(val)
        instrs = [{'kind': 'UTYPE', 'op': 'RISCV_LUI', 'rd': rd, 'imm': hi}]
        if lo != 0:
            instrs.append({'kind': 'ITYPE', 'op': 'RISCV_ADDI', 'rd': rd, 'rs1': rd, 'imm': lo})
        return instrs

    raise AsmError(
        f"unsupported mnemonic {mnemonic!r} -- refusing to guess "
        "(CSR ops, atomics, F/D, la/call/tail, compressed and RV64-only "
        "mnemonics like ld/sd are not handled)")


DIRECTIVE_RE = re.compile(r'^\s*\.')


def parse(text):
    """Two passes: (1) expand every source line into canonical instructions
    and record label -> instruction-index; (2) resolve symbolic
    branch/jal immediates to PC-relative byte offsets."""
    labels = {}
    canon = []  # list of (dict, comment)

    for raw in text.splitlines():
        line = raw.split('#', 1)[0].strip()
        if not line:
            continue
        # Labels MUST be matched before directives: clang's local labels
        # (".LBB0_2:") start with a dot, so DIRECTIVE_RE swallows them and
        # every branch target silently becomes "undefined label". Real
        # directives never end in ':', so this ordering is unambiguous.
        mlabel = LABEL_DEF_RE.match(line)
        if mlabel:
            labels[mlabel.group(1)] = len(canon)
            continue
        if DIRECTIVE_RE.match(line):
            continue
        parts = line.split(None, 1)
        mnemonic = parts[0]
        ops = split_operands(parts[1]) if len(parts) > 1 else []
        try:
            expanded = expand(mnemonic, ops)
        except AsmError as e:
            raise AsmError(f"line {raw.strip()!r}: {e}") from e
        n = len(expanded)
        for i, instr in enumerate(expanded):
            tag = raw.strip() if n == 1 else f"{raw.strip()}  ({i + 1}/{n})"
            canon.append((instr, tag))

    # Pass 2: resolve symbolic branch/jal targets.
    for idx, (instr, _comment) in enumerate(canon):
        if instr['kind'] in ('BTYPE', 'JAL') and isinstance(instr['imm'], str):
            target = instr['imm']
            if target not in labels:
                raise AsmError(f"undefined label {target!r} (instr #{idx})")
            instr['imm'] = 4 * (labels[target] - idx)

    return canon


def bv(n):
    # Parenthesize negative literals: `bv.of_Z -1` parses in Coq as the
    # infix expression `bv.of_Z - 1`, not application to a negative literal.
    return f"(bv.of_Z {n})" if n >= 0 else f"(bv.of_Z ({n}))"


def emit_instr(instr):
    k = instr['kind']
    if k == 'RTYPE':
        return f"RTYPE {instr['rs2']} {instr['rs1']} {instr['rd']} {instr['op']}"
    if k == 'ITYPE':
        return f"ITYPE {bv(instr['imm'])} {instr['rs1']} {instr['rd']} {instr['op']}"
    if k == 'SHIFTIOP':
        return f"SHIFTIOP {bv(instr['shamt'])} {instr['rs1']} {instr['rd']} {instr['op']}"
    if k == 'UTYPE':
        return f"UTYPE {bv(instr['imm'])} {instr['rd']} {instr['op']}"
    if k == 'BTYPE':
        return f"BTYPE {bv(instr['imm'])} {instr['rs2']} {instr['rs1']} {instr['op']}"
    if k == 'JAL':
        return f"RISCV_JAL {bv(instr['imm'])} {instr['rd']}"
    if k == 'JALR':
        return f"RISCV_JALR {bv(instr['imm'])} {instr['rs1']} {instr['rd']}"
    if k == 'LOAD':
        unsigned = 'true' if instr['unsigned'] else 'false'
        return f"LOAD {bv(instr['imm'])} {instr['rs1']} {instr['rd']} {unsigned} {instr['width']}"
    if k == 'STORE':
        return f"STORE {bv(instr['imm'])} {instr['rs2']} {instr['rs1']} {instr['width']}"
    if k == 'MUL':
        b = lambda x: 'true' if x else 'false'
        return (f"MUL {instr['rs2']} {instr['rs1']} {instr['rd']} "
                f"{b(instr['high'])} {b(instr['signed1'])} {b(instr['signed2'])}")
    if k == 'NULLARY':
        return instr['op']
    raise AssertionError(k)


def used_registers(canon):
    regs = set()
    for instr, _ in canon:
        for field in ('rd', 'rs1', 'rs2'):
            if field in instr:
                regs.add(instr[field])
    return sorted(regs, key=lambda r: NAME_TO_X[r])


def render(canon, name, drop_ret):
    if drop_ret and canon and canon[-1][0] == {'kind': 'JALR', 'rd': 'zero', 'rs1': 'ra', 'imm': 0}:
        canon = canon[:-1]

    lines = []
    lines.append("(* AUTO-GENERATED by case_study/RiscvPmp/CFGVer/tools/asm_to_ast.py")
    lines.append("   from the assembly listing below -- do not hand-edit, regenerate instead.")
    lines.append("   Requires ZArith's `Z_scope` (%Z) to be open for the `bv.of_Z` numerals")
    lines.append("   below to parse correctly -- already the case in CFGVer/Examples.v, but")
    lines.append("   if pasted into a fresh file add `From Coq Require Import ZArith.ZArith.`")
    lines.append("   first; otherwise bare numerals fall back to Bitvector's `bitstring`")
    lines.append("   Number Notation and fail to elaborate. *)")
    lines.append("")
    for r in used_registers(canon):
        lines.append(f"Definition {r} : RegIdx := bv.of_nat {NAME_TO_X[r]}.")
    lines.append("")
    lines.append(f"Definition {name}_instrs : list AST :=")
    for i, (instr, comment) in enumerate(canon):
        prefix = '  [ ' if i == 0 else '  ; '
        lines.append(f"{prefix}{emit_instr(instr)}   (* {comment} *)")
    lines.append("  ].")
    return '\n'.join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('input', nargs='?', help="assembly file (default: stdin)")
    ap.add_argument('--name', default='prog', help="base name for the Coq definition")
    ap.add_argument('--drop-ret', action='store_true',
                     help="drop a trailing bare `ret` (jalr x0,ra,0) -- CFGVer's "
                          "sexec_cfg_addr can't step through a symbolic jump target, "
                          "so straight-line blocks are usually verified up to the ret "
                          "instead of through it")
    args = ap.parse_args()

    text = open(args.input).read() if args.input else sys.stdin.read()
    try:
        canon = parse(text)
    except AsmError as e:
        print(f"error: {e}", file=sys.stderr)
        sys.exit(1)

    print(render(canon, args.name, args.drop_ret))


if __name__ == '__main__':
    main()
