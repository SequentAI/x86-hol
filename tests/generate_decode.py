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
UNARY = {"not": "Not", "neg": "Neg", "inc": "Inc", "dec": "Dec"}
SHIFTS = {"shl": "SHL", "shr": "SHR", "sar": "SAR"}
ROTATES = {"rol": "ROL", "ror": "ROR", "rcl": "RCL", "rcr": "RCR"}
BT_OPS = {"bt": "BT", "bts": "BTS", "btr": "BTR", "btc": "BTC"}
VEX_SHIFTS = {"shlx": "SHL", "shrx": "SHR", "sarx": "SAR"}
BLS = {"blsr": "BLSR", "blsi": "BLSI", "blsmsk": "BLSMSK"}
STRING_OPS = {"movs": "MOVS", "cmps": "CMPS", "stos": "STOS", "lods": "LODS", "scas": "SCAS"}
FLAG_OPS = {"clc": "CLC", "stc": "STC", "cmc": "CMC", "cld": "CLD", "std": "STD"}
LOOPS = {"loop": "LOOP", "loope": "LOOPE", "loopne": "LOOPNE", "jrcxz": "JRCXZ"}
SIZES = {"b": "S8", "w": "S16", "l": "S32", "q": "S64"}
LEGACY_PREFIXES = {0x66, 0xF2, 0xF3, 0x2E, 0x3E, 0x26, 0x36}
BITS = {"S8": 8, "S16": 16, "S32": 32, "S64": 64}
HIGH = ["ah", "ch", "dh", "bh"]
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
    raw: bytes  # the encoding, for forms LLVM prints alike (LEAVE and ENTER with 66)


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
    text = re.sub(r"^%[cdes]s:", "", text)
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
    if text.removeprefix("%") in HIGH:
        return f"(RmHigh {HIGH.index(text.removeprefix('%'))}w)", "S8"
    if text.startswith("%") and ":" not in text:
        reg, size = register(text)
        return f"(RmReg {reg}w)", size
    return f"(RmMem {memory(text)})", None


def rm(text: str) -> str:
    return operand(text)[0]


def reg(text: str) -> str:
    return f"{register(text)[0]}w"


def sized(m: str, bases: dict[str, str] | tuple[str, ...]) -> tuple[str, str] | None:
    """The base and size of a mnemonic with an AT&T size suffix."""
    if m[:-1] in bases and m[-1] in SIZES:
        return m[:-1], SIZES[m[-1]]
    return None


def immediate(text: str, size: str) -> str:
    """An immediate held sign-extended to 64 bits from the operand size."""
    return f"0x{signed(number(text), BITS[size]):x}w"


def relative(d: Disassembled) -> str:
    return f"0x{(d.target - d.offset - d.length) & (1 << 64) - 1:x}w"


def instruction(d: Disassembled) -> str:
    """The model's instruction for llvm-objdump's mnemonic and operands."""
    m, ops = d.mnemonic, d.operands
    # 0F 18 /4 and /7 with a memory operand are hint NOPs that newer CPUs
    # read as PREFETCHRST2 and PREFETCHIT0.
    if m.startswith("nop") or m in ("pause", "endbr64", "endbr32", "prefetchrst2", "prefetchit0"):
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
    return integer_instruction(d)


def stack_size(raw: bytes) -> str:
    """The operand size of LEAVE and ENTER: 16 bits with a 66 prefix and no
    REX.W in the REX byte right before the opcode, else 64."""
    n = 0
    while raw[n] in LEGACY_PREFIXES or raw[n] & 0xF0 == 0x40:
        n += 1
    rex_w = n > 0 and raw[n - 1] & 0xF8 == 0x48
    return "S16" if 0x66 in raw[:n] and not rex_w else "S64"


def integer_instruction(d: Disassembled) -> str:
    """The model's general-purpose instruction for llvm-objdump's text."""
    m, ops = d.mnemonic, d.operands
    if m in ("rep", "repe", "repne"):  # a prefix printed as its own mnemonic
        inner, *rest = ops[0].split(None, 1)
        inner_ops = split_operands(rest[0]) + ops[1:] if rest else ops[1:]
        if inner[:-1] in STRING_OPS and inner[-1] in SIZES:
            op = STRING_OPS[inner[:-1]]
            rep = "RepNE" if m == "repne" and op in ("CMPS", "SCAS") else "RepE"
            return f"StringOp {op} {SIZES[inner[-1]]} {rep}"
        return instruction(Disassembled(d.offset, d.length, inner, inner_ops, d.target, d.raw))
    if m[:-1] in STRING_OPS and m[-1] in SIZES and len(m) == 5:
        return f"StringOp {STRING_OPS[m[:-1]]} {SIZES[m[-1]]} NoRep"
    stack = stack_size(d.raw)
    if m in ("leave", "leaveq", "leavew"):
        return f"Leave {stack}"
    if m in ("enter", "enterq", "enterw"):
        return f"Enter {stack} 0x{number(ops[0]):x}w 0x{number(ops[1]):x}w"
    if m in ("ret", "retq"):
        return f"Ret 0x{number(ops[0]) if ops else 0:x}w"
    if m in ("jmp", "jmpq", "call", "callq") and ops and ops[0].startswith("*"):
        return f"{'Call' if m.startswith('call') else 'Jmp'}Ind {rm(ops[0][1:])}"
    if m in ("jmp", "jmpq"):
        return f"Jmp {relative(d)}"
    if m in ("call", "callq"):
        return f"Call {relative(d)}"
    if m in LOOPS:
        return f"Loop {LOOPS[m]} {relative(d)}"
    if m.startswith("j") and m[1:] in CONDITIONS:
        return f"Jcc {CONDITIONS.index(m[1:])}w {relative(d)}"
    if m in FLAG_OPS:
        return f"FlagOp {FLAG_OPS[m]}"
    simple = {"lahf": "Lahf", "sahf": "Sahf", "xlatb": "Xlat", "pushfq": "Pushf S64",
              "pushfw": "Pushf S16", "popfq": "Popf S64", "popfw": "Popf S16",
              "cbtw": "Cbw S16", "cwtl": "Cbw S32", "cltq": "Cbw S64",
              "cwtd": "Cwd S16", "cltd": "Cwd S32", "cqto": "Cwd S64"}
    if m in simple:
        return simple[m]
    if (p := sized(m, ("push", "pop"))):
        base, size = p
        if ops[0].startswith("$"):
            return f"PushImm {size} {immediate(ops[0], size)}"
        return f"{base.capitalize()} {size} {rm(ops[0])}"
    if m in ("cmpxchg8b", "cmpxchg16b"):
        return f"Cmpxchg2 {'T' if m == 'cmpxchg16b' else 'F'} {memory(ops[0])}"
    if m == "movabsq" and ops[0].startswith("$"):
        return f"MovImm S64 {rm(ops[1])} 0x{number(ops[0]) & (1 << 64) - 1:x}w"
    if (p := sized(m, ("mov", "movabs"))):
        size = p[1]
        if ops[0].startswith("$"):
            bits = 32 if size == "S64" else BITS[size]  # REX.W C7: imm32
            return f"MovImm {size} {rm(ops[1])} 0x{signed(number(ops[0]), bits):x}w"
        return f"Mov {size} {rm(ops[1])} {rm(ops[0])}"
    movx = re.fullmatch(r"mov([zs])([bwl])([wlq])", m)
    if movx:
        signed_, src, dst = movx.groups()
        if src == "l":  # MOVSXD; LLVM names it movslq at every destination size
            dst_size = register(ops[1])[1]
            return (f"Movx T {dst_size} {'S32' if dst_size == 'S64' else dst_size} "
                    f"{reg(ops[1])} {rm(ops[0])}")
        return (f"Movx {'T' if signed_ == 's' else 'F'} {SIZES[dst]} {SIZES[src]} "
                f"{reg(ops[1])} {rm(ops[0])}")
    if (p := sized(m, ("lea",))):
        return f"Lea {p[1]} {reg(ops[1])} {memory(ops[0])}"
    if (p := sized(m, ("mul", "imul", "div", "idiv"))) and len(ops) == 1:
        base, size = p
        kind = "MulWide" if base.endswith("mul") else "Div"
        return f"{kind} {'T' if base.startswith('i') else 'F'} {size} {rm(ops[0])}"
    if (p := sized(m, ("imul",))):
        size = p[1]
        if len(ops) == 3:
            return f"Imul {size} {reg(ops[2])} {rm(ops[1])} (SOME {immediate(ops[0], size)})"
        return f"Imul {size} {reg(ops[1])} {rm(ops[0])} NONE"
    if (p := sized(m, UNARY)):
        return f"{UNARY[p[0]]} {p[1]} {rm(ops[0])}"
    if (p := sized(m, SHIFTS | ROTATES)):
        base, size = p
        count = ("(SOME 0x1w)" if len(ops) == 1 else "NONE" if ops[0] == "%cl"
                 else f"(SOME 0x{number(ops[0]) & 0xFF:x}w)")
        kind = f"Shift {SHIFTS[base]}" if base in SHIFTS else f"Rotate {ROTATES[base]}"
        return f"{kind} {size} {rm(ops[-1])} {count}"
    if (p := sized(m, ("shld", "shrd"))):
        base, size = p
        count = "NONE" if ops[0] == "%cl" else f"(SOME 0x{number(ops[0]) & 0xFF:x}w)"
        return f"ShiftDouble {'T' if base == 'shld' else 'F'} {size} {rm(ops[2])} {reg(ops[1])} {count}"
    if (p := sized(m, ("bswap",))):
        return f"Bswap {p[1]} {reg(ops[0])}"
    if (p := sized(m, ("xchg",))):
        first, second = (ops[1], ops[0]) if not ops[1].startswith("%") else (ops[0], ops[1])
        return f"Xchg {p[1]} {rm(first)} {rm(second)}"
    if (p := sized(m, ("xadd", "cmpxchg"))):
        return f"{'Xadd' if p[0] == 'xadd' else 'Cmpxchg'} {p[1]} {rm(ops[1])} {rm(ops[0])}"
    if (p := sized(m, BT_OPS)):
        base, size = p
        if ops[0].startswith("$"):
            return f"BtImm {BT_OPS[base]} {size} {rm(ops[1])} 0x{number(ops[0]) & 0xFF:x}w"
        return f"Bt {BT_OPS[base]} {size} {rm(ops[1])} {reg(ops[0])}"
    if (p := sized(m, ("bsf", "bsr"))):
        return f"BitScan {'T' if p[0] == 'bsr' else 'F'} {p[1]} {reg(ops[1])} {rm(ops[0])}"
    if (p := sized(m, ("tzcnt", "lzcnt", "popcnt"))):
        return f"BitCount {p[0].upper()} {p[1]} {reg(ops[1])} {rm(ops[0])}"
    if (p := sized(m, ("crc32",))):
        return f"Crc32 {p[1]} {reg(ops[1])} {rm(ops[0])}"
    if (p := sized(m, ("movbe",))):
        return f"Movbe {p[1]} {rm(ops[1])} {rm(ops[0])}"
    if (p := sized(m, ("adcx", "adox"))):
        return f"Adx {'T' if p[0] == 'adox' else 'F'} {p[1]} {reg(ops[1])} {rm(ops[0])}"
    if (p := sized(m, ("mulx",))):
        return f"Mulx {p[1]} {reg(ops[2])} {reg(ops[1])} {rm(ops[0])}"
    if (p := sized(m, ("rorx",))):
        return f"Rorx {p[1]} {reg(ops[2])} {rm(ops[1])} 0x{number(ops[0]):x}w"
    if (p := sized(m, VEX_SHIFTS)):
        return f"ShiftX {VEX_SHIFTS[p[0]]} {p[1]} {reg(ops[2])} {rm(ops[1])} {reg(ops[0])}"
    if (p := sized(m, ("andn",))):
        return f"Andn {p[1]} {reg(ops[2])} {reg(ops[1])} {rm(ops[0])}"
    if (p := sized(m, ("bzhi", "bextr"))):
        return f"{p[0].capitalize()} {p[1]} {reg(ops[2])} {rm(ops[1])} {reg(ops[0])}"
    if (p := sized(m, BLS)):
        return f"Bls {BLS[p[0]]} {p[1]} {reg(ops[1])} {rm(ops[0])}"
    if (p := sized(m, ("pdep", "pext"))):
        return f"Pdep {p[0].upper()} {p[1]} {reg(ops[2])} {reg(ops[1])} {rm(ops[0])}"
    if m.startswith("cmov") and m[4:-1] in CONDITIONS:
        dst, size = register(ops[1])
        return f"Cmov {CONDITIONS.index(m[4:-1])}w {size} {dst}w {rm(ops[0])}"
    if m.startswith("set") and m[3:] in CONDITIONS:
        return f"Setcc {CONDITIONS.index(m[3:])}w {rm(ops[0])}"
    if (p := sized(m, BINOPS)):
        op, size = BINOPS[p[0]], p[1]
        if ops[0].startswith("$"):
            return f"BinopImm {op} {size} {rm(ops[1])} {immediate(ops[0], size)}"
        return f"Binop {op} {size} {rm(ops[1])} {rm(ops[0])}"
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
        if (mnemonic.startswith(("j", "call", "loop")) and operands
                and re.fullmatch(r"(0x)?[0-9a-f]+", operands[0])):
            target = int(operands[0], 16)
            operands = []
        current.append(Disassembled(int(offset, 16), len(raw.split()), mnemonic, operands, target,
                                    bytes.fromhex(raw.replace(" ", ""))))
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
