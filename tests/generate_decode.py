#!/usr/bin/env python3
"""Disassemble the decode vectors of cases.py with llvm-objdump and write the
instructions and lengths it reports to x86DecodeCasesScript.sml.

Each single-instruction execution case is given to the decoder as its
15-byte fetch window, padded with int3. The encodings in cases.REJECTED
must be rejected by the model. LLVM must read each as one instruction
of its length, or as one <unknown> for the over-long nop. The model also
rejects the encodings in cases.UNDECODED, which
llvm-objdump reports as <unknown> at their first byte, and every proper
prefix of those in cases.TRUNCATED, each read whole by llvm-objdump as one
instruction, which the model must find truncated. The windows in
cases.REJECTED_EARLY end at the byte that rules a rejected encoding out,
which the model must reject. llvm-objdump's AT&T output is parsed into the
model's instruction syntax; a form outside the slice stops the script.
"""
import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import tempfile

from cases import (REG8, REG16, REG32, REG64, REJECTED, REJECTED_EARLY, TRUNCATED, UNDECODED,
                   exec_cases)

WINDOW = 15
CONDITIONS = ["o", "no", "b", "ae", "e", "ne", "be", "a", "s", "ns", "p", "np", "l", "ge", "le", "g"]
BINOPS = {"add": "ADD", "or": "OR", "adc": "ADC", "sbb": "SBB", "and": "AND", "sub": "SUB",
          "xor": "XOR", "cmp": "CMP", "test": "TEST"}
UNARY = {"not": "Not", "neg": "Neg", "inc": "Inc"}
SHIFTS = {"shl": "SHL", "shr": "SHR", "sar": "SAR"}
ROTATES = {"rol": "T", "ror": "F"}
VEX_SHIFTS = {"shlxq": "SHL", "shrxq": "SHR", "sarxq": "SAR"}
BLS = {"blsrq": "BLSR", "blsiq": "BLSI", "blsmskq": "BLSMSK"}
PBINOPS = {"xorps": "PXOR", "pxor": "PXOR", "paddd": "PADDD", "paddq": "PADDQ", "pand": "PAND",
           "por": "POR", "pcmpeqb": "PCMPEQB", "pmulld": "PMULLD", "pminud": "PMINUD",
           "pmaxud": "PMAXUD", "psubd": "PSUBD", "psubq": "PSUBQ", "pabsd": "PABSD",
           "phaddd": "PHADDD", "pcmpgtq": "PCMPGTQ", "pmuludq": "PMULUDQ", "pmuldq": "PMULDQ",
           "pminsd": "PMINSD", "pmaxsd": "PMAXSD", "packusdw": "PACKUSDW",
           "packssdw": "PACKSSDW", "pmaddwd": "PMADDWD", "pmaddubsw": "PMADDUBSW",
           "packuswb": "PACKUSWB", "psadbw": "PSADBW", "pavgb": "PAVGB", "pavgw": "PAVGW",
           "paddusb": "PADDUSB", "psubusb": "PSUBUSB", "phminposuw": "PHMINPOSUW"}
PSHIFTS = {"pslld": ("T", "S32"), "psrld": ("F", "S32"), "psllq": ("T", "S64"),
           "psrlq": ("F", "S64")}


@dataclass
class Vector:
    comment: str
    window: bytes
    expected: str  # HOL term of type x86_instr decoded


@dataclass
class Disassembled:
    offset: int
    length: int
    mnemonic: str
    operands: list[str]
    target: int | None  # branch target address


def register(text: str) -> tuple[int, str]:
    name = text.removeprefix("%")
    for names, size in [(REG64, "S64"), (REG32, "S32"), (REG16, "S16"), (REG8, "S8")]:
        if name in names:
            return names.index(name), size
    raise ValueError(f"unexpected register {text}")


def xmm(text: str) -> int:
    match = re.fullmatch(r"%xmm(\d+)", text)
    if not match:
        raise ValueError(f"unexpected xmm register {text}")
    return int(match.group(1))


def number(text: str) -> int:
    return int(text.removeprefix("$"), 0)


def signed(value: int, bits: int) -> int:
    """value as a 64-bit word, sign-extended from the low `bits` bits."""
    value &= (1 << bits) - 1
    if value >> (bits - 1):
        value -= 1 << bits
    return value & (1 << 64) - 1


def memory(text: str) -> str:
    """The model's address for an AT&T memory operand."""
    text = text.removeprefix("%cs:")
    if re.fullmatch(r"-?0x[0-9a-f]+|-?\d+", text):  # absolute, no base or index
        return f"(Mem NONE NONE 0w 0x{signed(int(text, 0), 64):x}w)"
    match = re.fullmatch(r"(-?0x[0-9a-f]+|-?\d+)?\((%\w+)?(?:,(%\w+)(?:,(\d))?)?\)", text)
    if not match:
        raise ValueError(f"unexpected memory operand {text}")
    disp, base, index, scale = match.groups()
    displacement = signed(int(disp, 0) if disp else 0, 64)
    if base == "%rip":
        return f"(RipRel 0x{displacement:x}w)"
    base_term = "NONE" if base is None else f"(SOME {register(base)[0]}w)"
    index_term = "NONE" if index is None else f"(SOME {register(index)[0]}w)"
    log_scale = {None: 0, "1": 0, "2": 1, "4": 2, "8": 3}[scale]
    return f"(Mem {base_term} {index_term} {log_scale}w 0x{displacement:x}w)"


def operand(text: str) -> tuple[str, str | None]:
    """The model's rm term for a register or memory operand, and the
    register's size (None for memory)."""
    if text.startswith("%"):
        reg, size = register(text)
        return f"(RmReg {reg}w)", size
    return f"(RmMem {memory(text)})", None


def relative(d: Disassembled) -> str:
    return f"0x{(d.target - d.offset - d.length) & (1 << 64) - 1:x}w"


def instruction(d: Disassembled) -> str:
    """The model's instruction for llvm-objdump's mnemonic and operands."""
    m, ops = d.mnemonic, d.operands
    sizes = {"b": "S8", "w": "S16", "l": "S32", "q": "S64"}
    if m.startswith("nop"):
        return "Nop"
    if m == "movdqa" and ops[0].startswith("%xmm"):
        return f"VecMov {xmm(ops[1])}w {xmm(ops[0])}w"
    if m in ("movups", "movdqu", "movdqa") and ops[1].startswith("%xmm"):
        return f"VecLoad {'T' if m == 'movdqa' else 'F'} {xmm(ops[1])}w {memory(ops[0])}"
    if m in ("movups", "movdqu"):
        return f"VecStore {memory(ops[1])} {xmm(ops[0])}w"
    if m == "pxor" and not ops[0].startswith("%xmm"):
        return f"PxorMem {xmm(ops[1])}w {memory(ops[0])}"
    if m in PBINOPS:
        return f"Pbinop {PBINOPS[m]} {xmm(ops[1])}w {xmm(ops[0])}w"
    if m == "ptest":
        return f"Ptest {xmm(ops[1])}w {xmm(ops[0])}w"
    if m in ("crc32b", "crc32q"):
        width = "S8" if m == "crc32b" else "S64"
        src, src_size = operand(ops[0])
        d, dst_size = register(ops[1])
        if dst_size != {"S8": "S32", "S64": "S64"}[width] or src_size not in (None, width):
            raise ValueError(f"unexpected {m} operands {ops}")
        return f"Crc32 {width} {d}w {src}"
    if m == "pshufd":
        return f"Pshufd {xmm(ops[2])}w {xmm(ops[1])}w 0x{number(ops[0]):x}w"
    if m in ("pshuflw", "pshufhw"):
        return (f"Pshufw {'T' if m == 'pshufhw' else 'F'} {xmm(ops[2])}w {xmm(ops[1])}w "
                f"0x{number(ops[0]):x}w")
    if m == "aesimc":
        return f"AesImc {xmm(ops[1])}w {xmm(ops[0])}w"
    if m in ("pblendvb", "pcmpgtd", "pcmpeqd", "pshufb", "aesenc", "aesenclast", "aesdec", "aesdeclast"):
        if m == "pblendvb":
            if ops[0] != "%xmm0":
                raise ValueError(f"unexpected pblendvb mask {ops[0]}")
            ops = ops[1:]
        src = f"(RmReg {xmm(ops[0])}w)" if ops[0].startswith("%xmm") else f"(RmMem {memory(ops[0])})"
        instr = {"pblendvb": "Pblendvb", "pcmpgtd": "Pcmpd T", "pcmpeqd": "Pcmpd F",
                 "pshufb": "Pshufb"}.get(m, f"AesRound {m.upper()}")
        return f"{instr} {xmm(ops[1])}w {src}"
    if m in ("pmovzxbd", "pmovsxbd", "pmovzxdq", "pmovsxdq", "pmovzxbw", "pmovsxbw"):
        sign_extend = "T" if m.startswith("pmovsx") else "F"
        size = {"bd": "S32", "bw": "S16", "dq": "S64"}[m[-2:]]
        return f"Pwiden {sign_extend} {size} {xmm(ops[1])}w {memory(ops[0])}"
    if m in ("pslldq", "psrldq"):
        return f"Pshiftdq {'T' if m == 'pslldq' else 'F'} {xmm(ops[1])}w 0x{number(ops[0]):x}w"
    if m == "pinsrq":
        src, size = operand(ops[1])
        if size not in (None, "S64"):
            raise ValueError(f"unexpected pinsrq source {ops[1]}")
        return f"Pinsrq {xmm(ops[2])}w {src} 0x{number(ops[0]):x}w"
    if m == "pextrq":
        dst, size = operand(ops[2])
        if size not in (None, "S64"):
            raise ValueError(f"unexpected pextrq destination {ops[2]}")
        return f"Pextrq {dst} {xmm(ops[1])}w 0x{number(ops[0]):x}w"
    if m in ("pinsrd", "pextrd"):
        scalar = ops[1] if m == "pinsrd" else ops[2]
        rm, size = operand(scalar)
        if size not in (None, "S32"):
            raise ValueError(f"unexpected {m} operand {scalar}")
        if m == "pinsrd":
            return f"Pinsrd {xmm(ops[2])}w {rm} 0x{number(ops[0]):x}w"
        return f"Pextrd {rm} {xmm(ops[1])}w 0x{number(ops[0]):x}w"
    if m == "movd" and ops[1].startswith("%xmm"):
        rm, size = operand(ops[0])
        if size not in (None, "S32"):
            raise ValueError(f"unexpected movd source {ops[0]}")
        return f"MovdXmm {xmm(ops[1])}w {rm}"
    if m == "punpcklqdq":
        return f"Punpcklqdq {xmm(ops[1])}w {xmm(ops[0])}w"
    if m == "decq":
        return f"Dec64 {register(ops[0])[0]}w"
    if m in ("pclmulqdq", "aeskeygenassist", "palignr"):
        instr = {"pclmulqdq": "Pclmul", "aeskeygenassist": "AesKeygen", "palignr": "Palignr"}[m]
        return f"{instr} {xmm(ops[2])}w {xmm(ops[1])}w 0x{number(ops[0]):x}w"
    if m == "movq" and ops[1].startswith("%xmm"):
        reg, size = register(ops[0])
        if size != "S64":
            raise ValueError(f"unexpected movq source {ops[0]}")
        return f"MovqXmm {xmm(ops[1])}w {reg}w"
    if m in PSHIFTS:
        left, size = PSHIFTS[m]
        return f"Pshift {left} {size} {xmm(ops[1])}w 0x{number(ops[0]):x}w"
    if m == "psrad":
        return f"Psrad {xmm(ops[1])}w 0x{number(ops[0]):x}w"
    if m == "pmovmskb":
        reg, size = register(ops[1])
        if size != "S32":
            raise ValueError(f"unexpected pmovmskb destination {ops[1]}")
        return f"Pmovmskb {reg}w {xmm(ops[0])}w"
    if m in ("movd", "movq") and ops[0].startswith("%xmm"):
        reg, size = register(ops[1])
        if size != {"movd": "S32", "movq": "S64"}[m]:
            raise ValueError(f"unexpected {m} destination {ops[1]}")
        return f"Movd {size} {reg}w {xmm(ops[0])}w"
    if m in ("adcxq", "adoxq"):
        return f"Adx {'T' if m == 'adoxq' else 'F'} {register(ops[1])[0]}w {register(ops[0])[0]}w"
    if m == "movbeq":
        if ops[0].startswith("%"):
            return f"MovbeStore {memory(ops[1])} {register(ops[0])[0]}w"
        return f"MovbeLoad {register(ops[1])[0]}w {memory(ops[0])}"
    if m in ("ret", "retq"):
        return "Ret"
    if m == "cltq":
        return "Cdqe"
    if m in ("jmp", "jmpq") and ops and ops[0].startswith("*%"):
        return f"JmpReg {register(ops[0][1:])[0]}w"
    if m in ("jmp", "jmpq"):
        return f"Jmp {relative(d)}"
    if m in ("call", "callq"):
        return f"Call {relative(d)}"
    if m.startswith("j") and m[1:] in CONDITIONS:
        return f"Jcc {CONDITIONS.index(m[1:])}w {relative(d)}"
    if m in ("push", "pushq", "pop", "popq"):
        return f"{'Push' if m.startswith('push') else 'Pop'} {register(ops[0])[0]}w"
    if m in ("movzbl", "movzwl"):
        return f"Movzx {sizes[m[4]]} {register(ops[1])[0]}w {operand(ops[0])[0]}"
    if m == "movsbl":
        return f"Movsx {register(ops[1])[0]}w {operand(ops[0])[0]}"
    if m == "movslq":
        return f"Movsxd {register(ops[1])[0]}w {operand(ops[0])[0]}"
    if m == "leaq":
        return f"Lea {register(ops[1])[0]}w {memory(ops[0])}"
    if m in ("mulq", "imulq") and len(ops) == 1:
        return f"MulWide {'T' if m == 'imulq' else 'F'} {register(ops[0])[0]}w"
    if m in ("divl", "divq", "idivq"):
        return f"Div {'T' if m == 'idivq' else 'F'} {sizes[m[-1]]} {register(ops[0])[0]}w"
    if m == "cqto":
        return "Cqo"
    if m in ("shldq", "shrdq") and ops[0] == "%cl":
        left = "T" if m == "shldq" else "F"
        return f"ShiftDouble {left} {register(ops[2])[0]}w {register(ops[1])[0]}w"
    if m == "bswapq":
        return f"Bswap {register(ops[0])[0]}w"
    if m[:-1] in ("tzcnt", "lzcnt", "popcnt") and m[-1] in "lq":
        size = sizes[m[-1]]
        return f"BitCount {m[:-1].upper()} {size} {register(ops[1])[0]}w {register(ops[0])[0]}w"
    if m == "mulxq":
        return f"Mulx {register(ops[2])[0]}w {register(ops[1])[0]}w {operand(ops[0])[0]}"
    if m in ("rorxl", "rorxq"):
        return (f"Rorx {sizes[m[-1]]} {register(ops[2])[0]}w {register(ops[1])[0]}w "
                f"0x{number(ops[0]):x}w")
    if m in VEX_SHIFTS:
        return (f"ShiftX {VEX_SHIFTS[m]} {register(ops[2])[0]}w {register(ops[1])[0]}w "
                f"{register(ops[0])[0]}w")
    if m in ("andnq", "bzhiq"):
        return (f"{m[0].upper()}{m[1:-1]} {register(ops[2])[0]}w {register(ops[1])[0]}w "
                f"{register(ops[0])[0]}w")
    if m in BLS:
        return f"Bls {BLS[m]} {register(ops[1])[0]}w {register(ops[0])[0]}w"
    if m in ("pdepq", "pextq"):
        return (f"Pdep {m[:-1].upper()} {register(ops[2])[0]}w {register(ops[1])[0]}w "
                f"{register(ops[0])[0]}w")
    if m == "bextrq":
        return f"Bextr {register(ops[2])[0]}w {register(ops[1])[0]}w {register(ops[0])[0]}w"
    if m == "movabsq":
        return f"MovImm64 {register(ops[1])[0]}w 0x{signed(number(ops[0]), 64):x}w"
    if m == "imulq":
        return f"Imul {register(ops[1])[0]}w {operand(ops[0])[0]}"
    if m.startswith("cmov") and m[4:-1] in CONDITIONS:
        dst, size = register(ops[1])
        return f"Cmov {CONDITIONS.index(m[4:-1])}w {size} {dst}w {operand(ops[0])[0]}"
    if m.startswith("set") and m[3:] in CONDITIONS:
        return f"Setcc {CONDITIONS.index(m[3:])}w {operand(ops[0])[0]}"
    if m[:-1] in UNARY and m[-1] in sizes:
        return f"{UNARY[m[:-1]]} {sizes[m[-1]]} {operand(ops[0])[0]}"
    if m[:-1] in SHIFTS and m[-1] in sizes and len(ops) == 1:  # D1: shift by one
        return f"Shift {SHIFTS[m[:-1]]} {sizes[m[-1]]} {operand(ops[0])[0]} (SOME 0x1w)"
    if m[:-1] in SHIFTS and m[-1] in sizes:
        count = "NONE" if ops[0] == "%cl" else f"(SOME 0x{number(ops[0]):x}w)"
        return f"Shift {SHIFTS[m[:-1]]} {sizes[m[-1]]} {operand(ops[1])[0]} {count}"
    if m[:-1] in ROTATES and m[-1] in sizes:
        count = "NONE" if ops[0] == "%cl" else f"(SOME 0x{number(ops[0]):x}w)"
        return f"Rotate {ROTATES[m[:-1]]} {sizes[m[-1]]} {register(ops[1])[0]}w {count}"
    if m == "movq" and ops[0].startswith("$"):  # REX.W C7 /0: sign-extended imm32
        return f"MovImm64 {register(ops[1])[0]}w 0x{signed(number(ops[0]), 64):x}w"
    if m[:-1] == "mov" and m[-1] in sizes and ops[0].startswith("$"):
        return f"MovImm {register(ops[1])[0]}w 0x{number(ops[0]) & 0xFFFFFFFF:x}w"
    if m[:-1] == "mov" and m[-1] in sizes:
        return f"Mov {sizes[m[-1]]} {operand(ops[1])[0]} {operand(ops[0])[0]}"
    if m[:-1] in BINOPS and m[-1] in sizes:
        op, size = BINOPS[m[:-1]], sizes[m[-1]]
        if ops[0].startswith("$"):
            immediate = signed(number(ops[0]), {"S8": 8, "S64": 64}.get(size, 32))
            return f"BinopImm {op} {size} {operand(ops[1])[0]} 0x{immediate:x}w"
        return f"Binop {op} {size} {operand(ops[1])[0]} {operand(ops[0])[0]}"
    raise ValueError(f"no model instruction for {m} {','.join(ops)}")


def split_operands(text: str) -> list[str]:
    """Operands separated by commas outside parentheses."""
    operands, depth, current = [], 0, ""
    for char in text:
        depth += {"(": 1, ")": -1}.get(char, 0)
        if char == "," and depth == 0:
            operands.append(current.strip())
            current = ""
        else:
            current += char
    return [o for o in operands + [current.strip()] if o]


def disassemble(symbols: dict[str, bytes], zig: str, objdump: str) -> dict[str, list[Disassembled]]:
    source = [".text"]
    for name, code in symbols.items():
        source += [f".globl {name}", f"{name}:", ".byte " + ", ".join(map(str, code))]
    with tempfile.TemporaryDirectory(prefix="x86-decode-") as temporary:
        assembly, obj = Path(temporary) / "vectors.s", Path(temporary) / "vectors.o"
        assembly.write_text("\n".join(source) + "\n")
        subprocess.run([zig, "cc", "--target=x86_64-linux-gnu", "-c", str(assembly), "-o", str(obj)],
                       check=True)
        listing = subprocess.run([objdump, "-d", str(obj)], capture_output=True, text=True,
                                 check=True).stdout
    result: dict[str, list[Disassembled]] = {}
    current: list[Disassembled] = []
    for line in listing.splitlines():
        header = re.fullmatch(r"[0-9a-f]+ <(\w+)>:", line)
        if header:
            current = result.setdefault(header.group(1), [])
            continue
        row = re.fullmatch(r"\s*([0-9a-f]+):\s+([0-9a-f]{2}(?: [0-9a-f]{2})*)\s+(\S+)\s*([^#<]*)(?:<.*>)?\s*(?:#.*)?", line)
        if not row:
            continue
        offset, raw, mnemonic, operands = row.groups()
        operands = split_operands(operands)
        target = None
        if mnemonic.startswith(("j", "call")) and re.fullmatch(r"(0x)?[0-9a-f]+", operands[0]):
            target = int(operands[0], 16)
            operands = []
        current.append(Disassembled(int(offset, 16), len(raw.split()), mnemonic, operands, target))
    return result


def window(code: bytes) -> bytes:
    """The bytes from an instruction's start that step fetches, int3-padded."""
    return code[:WINDOW] + b"\xcc" * (WINDOW - len(code[:WINDOW]))


def vectors(zig: str, objdump: str) -> list[Vector]:
    singles = {}
    for case in exec_cases():
        if case.single:
            singles.setdefault(case.code, case.name)
    symbols = {f"v{i}": code for i, code in enumerate(singles)}
    rejected = {f"r{i}": (name, code) for i, (name, code) in enumerate(REJECTED.items())}
    undecoded = {f"u{i}": (name, code) for i, (name, code) in enumerate(UNDECODED.items())}
    truncated = {f"t{i}": (name, code) for i, (name, code) in enumerate(TRUNCATED.items())}
    listing = disassemble(symbols | {s: code for s, (_, code) in
                                     (rejected | undecoded | truncated).items()}, zig, objdump)
    result = []
    for name, code in symbols.items():
        label = singles[code]
        rows = listing[name]
        if len(rows) != 1 or rows[0].length != len(code):
            raise SystemExit(f"{label}: llvm-objdump does not read one instruction of {len(code)} bytes")
        row = rows[0]
        text = f"{row.mnemonic} {','.join(row.operands)}".strip()
        result.append(Vector(f"{label}: {text}", window(code),
                             f"Decoded ({instruction(row)}) {row.length}"))
    for symbol, (name, code) in rejected.items():
        rows = listing[symbol]
        if len(rows) != 1 or rows[0].length != len(code):
            raise SystemExit(f"rejected {name}: llvm-objdump does not read one instruction")
        text = f"{rows[0].mnemonic} {','.join(rows[0].operands)}".strip()
        # Whole, so the 16-byte nop reaches the decoder's 15-byte limit.
        padded = code + b"\xcc" * max(0, WINDOW - len(code))
        result.append(Vector(f"rejected: {name}: {text}", padded, "Rejected"))
        if name in REJECTED_EARLY:
            n = REJECTED_EARLY[name]
            result.append(Vector(f"rejected: {name}: first {n} bytes", code[:n], "Rejected"))
    for symbol, (name, code) in undecoded.items():
        if listing[symbol][0].mnemonic != "<unknown>":
            raise SystemExit(f"undecoded {name}: llvm-objdump decodes it")
        padded = code + b"\xcc" * (WINDOW - len(code))
        result.append(Vector(f"rejected: {name}: <unknown>", padded, "Rejected"))
    for symbol, (name, code) in truncated.items():
        rows = listing[symbol]
        if len(rows) != 1 or rows[0].length != len(code):
            raise SystemExit(f"truncated {name}: llvm-objdump does not read one instruction")
        instruction(rows[0])
        for n in range(1, len(code)):
            result.append(Vector(f"truncated: {name}: first {n} bytes", code[:n], "Truncated"))
    return result


def render(vectors: list[Vector]) -> str:
    entries = []
    for v in vectors:
        window_term = "[" + "; ".join(f"0x{b:02x}w" for b in v.window) + "]"
        entries.append(f"    (* {v.comment} *)\n    ({window_term},\n     {v.expected})")
    return "\n".join([
        "(* Generated by generate_decode.py from cases.py and llvm-objdump. *)",
        "Theory x86DecodeCases", "Ancestors x86Isa", "",
        "(* A 15-byte fetch window, and the instruction and length llvm-objdump",
        "   reads there, or Rejected for an encoding outside the modelled slice. *)",
        "Definition decode_cases_def:",
        "  decode_cases : (word8 list # x86_instr decoded) list = [",
        ";\n".join(entries), "  ]", "End", ""])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig", default="python-zig", help="zig executable, used as assembler")
    parser.add_argument("--objdump", default="llvm-objdump", help="llvm-objdump executable")
    parser.add_argument("--check", action="store_true",
                        help="fail if the committed theory differs instead of writing it")
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    rebuilt = render(vectors(args.zig, args.objdump))
    output = directory / "x86DecodeCasesScript.sml"
    if args.check:
        if output.read_text() != rebuilt:
            raise SystemExit("llvm-objdump's decoding differs from x86DecodeCasesScript.sml")
        print("decode vectors match llvm-objdump")
    else:
        output.write_text(rebuilt)


if __name__ == "__main__":
    main()
