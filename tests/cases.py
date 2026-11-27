"""Instruction encodings and test cases shared by generate_decode.py and
generate_exec.py.

Every case runs from its code placed at CODE_BASE + 0x100 in a code page
otherwise filled with int3 (0xCC), with a data window at DATA_BASE and the
return address at STACK_TOP, the last 8 bytes of the stack page. Each page
is followed by an inaccessible one. The model's test states in
x86ExecTestScript.sml use the same layout.
"""
from dataclasses import dataclass, field
import random
from typing import Callable

CODE_BASE = 0x100000
DATA_BASE = 0x200000
STACK_BASE = 0x300000
ENTRY = CODE_BASE + 0x100
STACK_TOP = STACK_BASE + 0xFF8
SENTINEL = CODE_BASE + 0x1F0
STACK_END = STACK_BASE + 0x1000
DATA_SIZE = 256
STACK_WINDOW = 128  # bytes below STACK_END the harnesses report
FLAG_BITS = (0, 2, 4, 6, 7, 11)  # CF PF AF ZF SF OF
FLAG_MASK = sum(1 << b for b in FLAG_BITS)
# Outcomes compare DF too; cases start with DF clear.
OUTCOME_MASK = FLAG_MASK | 1 << 10
MASK64 = (1 << 64) - 1

REG64 = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"] + [f"r{i}" for i in range(8, 16)]
REG32 = ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi"] + [f"r{i}d" for i in range(8, 16)]
REG16 = ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"] + [f"r{i}w" for i in range(8, 16)]
REG8 = ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"] + [f"r{i}b" for i in range(8, 16)]
RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI = range(8)
M32, M64 = (1 << 32) - 1, (1 << 64) - 1


def signed(v: int, bits: int) -> int:
    return v - (1 << bits) if v >> (bits - 1) & 1 else v


def lanes32(lanes: list[int]) -> int:
    return sum((v & M32) << 32 * i for i, v in enumerate(lanes))


def lanes64(lanes: list[int]) -> int:
    return sum((v & M64) << 64 * i for i, v in enumerate(lanes))


def lane(v: int, bits: int, i: int) -> int:
    return v >> bits * i & (1 << bits) - 1


# Packed dword and qword operations, with their opcodes after 66 and results.
LANE_OPS = [
    ("psubd", b"\x0f\xfa", lambda a, b: lanes32([lane(a, 32, i) - lane(b, 32, i) for i in range(4)])),
    ("psubq", b"\x0f\xfb", lambda a, b: lanes64([lane(a, 64, i) - lane(b, 64, i) for i in range(2)])),
    ("pabsd", b"\x0f\x38\x1e", lambda a, b: lanes32([abs(signed(lane(b, 32, i), 32)) for i in range(4)])),
    ("phaddd", b"\x0f\x38\x02", lambda a, b: lanes32([lane(v, 32, i) + lane(v, 32, i + 1)
                                                      for v in (a, b) for i in (0, 2)])),
    ("pcmpgtq", b"\x0f\x38\x37", lambda a, b: lanes64([M64 if signed(lane(a, 64, i), 64) >
                                                        signed(lane(b, 64, i), 64) else 0
                                                        for i in range(2)])),
]


def lanes16(lanes: list[int]) -> int:
    return sum((v & 0xFFFF) << 16 * i for i, v in enumerate(lanes))


def saturate(v: int, low: int, high: int) -> int:
    return min(max(v, low), high)


# Packed widening, comparison and saturation operations, with their opcodes after 66 and results.
PACK_OPS = [
    ("pmuludq", b"\x0f\xf4", lambda a, b: lanes64([lane(a, 32, i) * lane(b, 32, i) for i in (0, 2)])),
    ("pmuldq", b"\x0f\x38\x28", lambda a, b: lanes64([signed(lane(a, 32, i), 32) *
                                                      signed(lane(b, 32, i), 32) for i in (0, 2)])),
    ("pminsd", b"\x0f\x38\x39", lambda a, b: lanes32([min(signed(lane(a, 32, i), 32),
                                                          signed(lane(b, 32, i), 32)) for i in range(4)])),
    ("pmaxsd", b"\x0f\x38\x3d", lambda a, b: lanes32([max(signed(lane(a, 32, i), 32),
                                                          signed(lane(b, 32, i), 32)) for i in range(4)])),
    ("packusdw", b"\x0f\x38\x2b", lambda a, b: lanes16([saturate(signed(lane(v, 32, i), 32), 0, 0xFFFF)
                                                         for v in (a, b) for i in range(4)])),
    ("packssdw", b"\x0f\x6b", lambda a, b: lanes16([saturate(signed(lane(v, 32, i), 32), -0x8000, 0x7FFF)
                                                    for v in (a, b) for i in range(4)])),
]


def madd_words(a: int, b: int) -> int:
    """PMADDWD: sums of signed word products, wrapping at 32 bits."""
    return lanes32([sum(signed(lane(a, 16, j), 16) * signed(lane(b, 16, j), 16)
                        for j in (2 * i, 2 * i + 1)) for i in range(4)])


def madd_bytes(a: int, b: int) -> int:
    """PMADDUBSW: sums of a's unsigned by b's signed byte products, saturated
    to a signed word."""
    return lanes16([saturate(sum(lane(a, 8, j) * signed(lane(b, 8, j), 8)
                                 for j in (2 * i, 2 * i + 1)), -0x8000, 0x7FFF)
                    for i in range(8)])


def pack_words(a: int, b: int) -> int:
    """PACKUSWB: a's then b's signed words saturated to unsigned bytes."""
    return sum(saturate(signed(lane(v, 16, i), 16), 0, 0xFF) << 8 * (8 * k + i)
               for k, v in enumerate((a, b)) for i in range(8))


# Packed multiply-add and narrowing operations, with their opcodes after 66 and results.
MADD_OPS = [
    ("pmaddwd", b"\x0f\xf5", madd_words),
    ("pmaddubsw", b"\x0f\x38\x04", madd_bytes),
    ("packuswb", b"\x0f\x67", pack_words),
]


def byte_lanes(f, a: int, b: int) -> int:
    return sum(f(lane(a, 8, i), lane(b, 8, i)) << 8 * i for i in range(16))


def sad_bytes(a: int, b: int) -> int:
    """PSADBW: sums of |a_i - b_i| over bytes 0..7 and 8..15, one per qword."""
    return lanes64([sum(abs(lane(a, 8, i) - lane(b, 8, i)) for i in range(8 * k, 8 * k + 8))
                    for k in range(2)])


def minpos_words(v: int) -> int:
    """PHMINPOSUW: the least unsigned word and the lowest index holding it."""
    words = [lane(v, 16, i) for i in range(8)]
    least = min(words)
    return least | words.index(least) << 16


# Packed byte and word operations, with their opcodes after 66 and results.
SAD_OPS = [
    ("psadbw", b"\x0f\xf6", sad_bytes),
    ("pavgb", b"\x0f\xe0", lambda a, b: byte_lanes(lambda x, y: (x + y + 1) // 2, a, b)),
    ("pavgw", b"\x0f\xe3", lambda a, b: lanes16([(lane(a, 16, i) + lane(b, 16, i) + 1) // 2
                                                   for i in range(8)])),
    ("paddusb", b"\x0f\xdc", lambda a, b: byte_lanes(lambda x, y: min(x + y, 0xFF), a, b)),
    ("psubusb", b"\x0f\xd8", lambda a, b: byte_lanes(lambda x, y: max(x - y, 0), a, b)),
    ("phminposuw", b"\x0f\x38\x41", lambda a, b: minpos_words(b)),
]


def psrad(v: int, count: int) -> int:
    return lanes32([signed(lane(v, 32, i), 32) >> count for i in range(4)])
CF, AF, OF, SF, ZF, PF = 1, 1 << 4, 1 << 11, 1 << 7, 1 << 6, 1 << 2

# The supported PMOVZX/PMOVSX forms: mnemonic, opcode
# after 66 0F 38, source and result lane widths in bytes, and signedness.
WIDEN_FORMS = (
    ("pmovzxbd", 0x31, 1, 4, False),
    ("pmovsxbd", 0x21, 1, 4, True),
    ("pmovzxdq", 0x35, 4, 8, False),
    ("pmovsxdq", 0x25, 4, 8, True),
)
WIDEN16_FORMS = (
    ("pmovzxbw", 0x30, 1, 2, False),
    ("pmovsxbw", 0x20, 1, 2, True),
)


def widen_lanes(data: bytes, width: int, result_width: int, signed: bool) -> bytes:
    return b"".join(int.from_bytes(data[i:i + width], "little", signed=signed)
                    .to_bytes(result_width, "little", signed=signed)
                    for i in range(0, len(data), width))


def rex(w: int, r: int, x: int, b: int, force: bool = False) -> bytes:
    value = 0x40 | w << 3 | (r >> 3) << 2 | (x >> 3) << 1 | (b >> 3)
    return bytes([value]) if value != 0x40 or force else b""


def reg_reg(opcode: int, w: int, dst: int, src: int) -> bytes:
    """op r/m, r with both operands registers (01, 31, 39, 85, 89)."""
    return rex(w, src, 0, dst) + bytes([opcode, 0xC0 | (src & 7) << 3 | dst & 7])


def reg_imm8(digit: int, w: int, dst: int, imm: int) -> bytes:
    """83 /digit ib with a register operand."""
    return rex(w, 0, 0, dst) + bytes([0x83, 0xC0 | digit << 3 | dst & 7, imm & 0xFF])


def mov_imm32(reg: int, imm: int) -> bytes:
    return rex(0, 0, 0, reg) + bytes([0xB8 + (reg & 7)]) + (imm & 0xFFFFFFFF).to_bytes(4, "little")


@dataclass
class Address:
    base: int | None  # None: no base (SIB) or, with rip, RIP-relative
    index: int | None = None
    scale: int = 0  # log2
    disp: int = 0
    rip: bool = False

    def rex_x(self) -> int:
        return 0 if self.index is None else self.index

    def rex_b(self) -> int:
        return 0 if self.base is None else self.base

    def __str__(self) -> str:
        """The operand's shape: registers and scale, without the displacement."""
        if self.rip:
            return "rip+disp"
        parts = [] if self.base is None else [REG64[self.base]]
        if self.index is not None:
            parts.append(f"{REG64[self.index]}*{1 << self.scale}")
        return "+".join(parts + ["disp"])


def modrm_memory(reg: int, a: Address) -> bytes:
    """The ModRM, SIB and displacement bytes for a memory operand."""
    disp32 = (a.disp & 0xFFFFFFFF).to_bytes(4, "little")
    if a.rip:
        return bytes([(reg & 7) << 3 | 5]) + disp32
    if a.base is None:
        index = RSP if a.index is None else a.index
        return bytes([(reg & 7) << 3 | 4, a.scale << 6 | (index & 7) << 3 | 5]) + disp32
    size = 0 if a.disp == 0 else 8 if -128 <= a.disp < 128 else 32
    if size == 0 and a.base & 7 == RBP:
        size = 8  # mod 00 with base 101 means RIP-relative or no base
    mod = {0: 0, 8: 1, 32: 2}[size]
    disp = (a.disp & (1 << size) - 1).to_bytes(size // 8, "little")
    if a.index is None and a.base & 7 != RSP:
        return bytes([mod << 6 | (reg & 7) << 3 | a.base & 7]) + disp
    if a.index == RSP:
        raise ValueError("rsp cannot be an index")
    index = RSP if a.index is None else a.index  # SIB index 100 means none
    sib = a.scale << 6 | (index & 7) << 3 | a.base & 7
    return bytes([mod << 6 | (reg & 7) << 3 | 4, sib]) + disp


def movzx8(dst: int, a: Address) -> bytes:
    return rex(0, dst, a.rex_x(), a.rex_b()) + b"\x0f\xb6" + modrm_memory(dst, a)


def mem_op(opcode: bytes, w: int, reg: int, a: Address, prefix: bytes = b"",
           byte_reg: bool = False, force_rex: bool = False) -> bytes:
    """An instruction with a ModRM memory operand: prefix, REX, opcode, ModRM...
    With byte_reg, reg is a byte register, which needs a REX prefix for 4..7.
    With force_rex, a REX prefix is emitted even when it has no bits set."""
    return (prefix + rex(w, reg, a.rex_x(), a.rex_b(), byte_reg and 4 <= reg < 8 or force_rex)
            + opcode + modrm_memory(reg, a))


def reg_op(opcode: bytes, w: int, reg: int, rm: int, force_rex: bool = False) -> bytes:
    """An instruction with a ModRM register operand rm and reg field reg."""
    return rex(w, reg, 0, rm, force_rex) + opcode + bytes([0xC0 | (reg & 7) << 3 | rm & 7])


def vex(mmmmm: int, pp: int, w: int, v: int, r: int, x: int, b: int, l: int = 0) -> bytes:
    """A three-byte VEX prefix: C4, the inverted R, X and B bits and the map,
    then W, the inverted register v, L and the implied prefix pp."""
    rxb = (~r >> 3 & 1) << 7 | (~x >> 3 & 1) << 6 | (~b >> 3 & 1) << 5
    return bytes([0xC4, rxb | mmmmm, w << 7 | (~v & 15) << 3 | l << 2 | pp])


def vex_reg(mmmmm: int, pp: int, w: int, opcode: int, reg: int, v: int, rm: int) -> bytes:
    """A VEX instruction with a ModRM register operand rm and reg field reg."""
    return vex(mmmmm, pp, w, v, reg, 0, rm) + bytes([opcode, 0xC0 | (reg & 7) << 3 | rm & 7])


def vex_mem(mmmmm: int, pp: int, w: int, opcode: int, reg: int, v: int, a: Address) -> bytes:
    """A VEX instruction with a ModRM memory operand."""
    return vex(mmmmm, pp, w, v, reg, a.rex_x(), a.rex_b()) + bytes([opcode]) + modrm_memory(reg, a)


def rel32(opcode: bytes, disp: int) -> bytes:
    return opcode + (disp & 0xFFFFFFFF).to_bytes(4, "little")


def jcc8(cc: int, disp: int) -> bytes:
    return bytes([0x70 | cc, disp & 0xFF])


def jmp8(disp: int) -> bytes:
    return bytes([0xEB, disp & 0xFF])


RET = b"\xc3"
NOPS = [bytes.fromhex(h) for h in [
    "0f1f00", "0f1f4000", "0f1f440000", "660f1f440000", "0f1f8000000000",
    "0f1f840000000000", "660f1f840000000000", "662e0f1f840000000000",
    "66662e0f1f840000000000", "66" * 6 + "2e0f1f840000000000"]]

# Encodings the model rejects (Unsupported) although llvm-objdump reads
# them: forms outside the model (system, I/O, LOCK, FS/GS, 67, x87, MMX and
# SSE beyond the slice), near branches with a 66 prefix, which Intel and AMD
# execute differently, and prefix orders the CPU faults on.
REJECTED = {name: bytes.fromhex(h) for name, h in [
    ("jmp rel8 with a 66 prefix", "66eb00"),
    ("je rel8 with a 66 prefix", "667400"),
    ("call rel32 with a 66 prefix", "66e800000000"),
    ("ret with a 66 prefix", "66c3"),
    ("mov from an FS address", "648b07"),
    ("mov from a GS address", "658b07"),
    ("mov with a 67 prefix", "678b07"),
    ("add with both F2 and F3", "f2f301c0"),
    ("syscall", "0f05"),
    ("cpuid", "0fa2"),
    ("rdtsc", "0f31"),
    ("hlt", "f4"),
    ("in al, dx", "ec"),
    ("int 0x80", "cd80"),
    ("ud2", "0f0b"),
    ("mov to a segment register", "8ed8"),
    ("far jmp through memory", "ff28"),
    ("fld1 (x87)", "d9e8"),
    ("prefetchnta (0F 18 /0)", "0f1800"),
    ("prefetchw (0F 0D /1)", "0f0d08"),
    ("cldemote (0F 1C /0)", "0f1c00"),
    ("rdsspq (F3 REX.W 0F 1E /1)", "f3480f1ec8"),
    ("16-byte nop over the 15-byte limit", "66" * 7 + "2e0f1f840000000000"),
    ("movups xmm, xmm (0F 10, register source)", "0f10c1"),
    ("movups xmm, xmm (0F 11, register destination)", "0f11c1"),
    ("movups with REX.W", "480f1006"),
    ("movupd (66 0F 10)", "660f1006"),
    ("movss (F3 0F 10)", "f30f1006"),
    ("movaps load (0F 28)", "0f2806"),
    ("movaps store (0F 29)", "0f2907"),
    ("movdqa store (66 0F 7F)", "660f7f07"),
    ("movdqu xmm, xmm (F3 0F 6F, register source)", "f30f6fc1"),
    ("movdqu with REX.W", "f3480f6f06"),
    ("movq xmm, m64 (F3 0F 7E)", "f30f7e06"),
    ("xorps xmm, m128 (0F 57, memory source)", "0f5706"),
    ("xorpd (66 0F 57)", "660f57c1"),
    ("pxor with REX.W", "66480fefc1"),
    ("pxor mmx (0F EF without 66)", "0fefc1"),
    ("paddd xmm, m128 (66 0F FE, memory source)", "660ffe06"),
    ("paddb (66 0F FC)", "660ffcc1"),
    ("paddw (66 0F FD)", "660ffdc1"),
    ("pshufd xmm, m128, imm8 (66 0F 70, memory source)", "660f700655"),
    ("movd r32, xmm to memory (66 0F 7E)", "660f7e07"),
    ("punpcklbw (66 0F 60)", "660f60c1"),
    ("punpcklwd (66 0F 61)", "660f61c1"),
    ("psraw (66 0F 71 /4)", "660f71e003"),
    ("psllw (66 0F 71 /6)", "660f71f003"),
    ("pslld mmx (0F 72 /6 without 66)", "0f72f003"),
    ("psrlq mmx (0F 73 /2 without 66)", "0f73d003"),
    ("pslld with REX.R (66 REX.R 0F 72 /6)", "66440f72f003"),
    ("psrlq with REX.R (66 REX.R 0F 73 /2)", "66440f73d003"),
    ("ptest from memory", "660f381707"),
    ("pmulld from memory", "660f384007"),
    ("pminud from memory", "660f383b07"),
    ("pmaxud from memory", "660f383f07"),
    ("pslld xmm, xmm (66 0F F2)", "660ff2c1"),
    ("psllq xmm, xmm (66 0F F3)", "660ff3c1"),
    ("pshufb mmx (0F 38 00 without 66)", "0f3800c1"),
    ("pshufb with REX.W", "66480f3800c1"),
    ("phaddw (66 0F 38 01)", "660f3801c1"),
    ("pshuflw xmm, m128 (F2 0F 70, memory source)", "f20f700655"),
    ("pshuflw with REX.W", "f2480f70c1d4"),
    ("movsd with REX.W (F2 REX.W 0F 10)", "f2480f1006"),
    ("pshufw mmx (0F 70 without a prefix)", "0f70c1d4"),
    ("movdqu xmm, xmm (F3 0F 7F, register destination)", "f30f7fc1"),
    ("movdqu store with REX.W", "f3480f7f07"),
    ("movsd (F2 0F 10)", "f20f1006"),
    ("F2 and 66 before 0F 70", "66f20f70c1d4"),
    ("pandn (66 0F DF)", "660fdfc1"),
    ("pcmpeqw (66 0F 75)", "660f75c1"),
    ("pcmpgtb (66 0F 64)", "660f64c1"),
    ("pcmpeqb mmx (0F 74 without 66)", "0f74c1"),
    ("pcmpeqb xmm, m128 (66 0F 74, memory source)", "660f7406"),
    ("pand xmm, m128 (66 0F DB, memory source)", "660fdb06"),
    ("por xmm, m128 (66 0F EB, memory source)", "660feb06"),
    ("paddq xmm, m128 (66 0F D4, memory source)", "660fd406"),
    ("pmovmskb with REX.W (66 REX.W 0F D7)", "66480fd7c1"),
    ("pmovmskb mmx (0F D7 without 66)", "0fd7c1"),
    ("pmovmskb with a memory operand (66 0F D7)", "660fd707"),
    ("movq xmm, m64 (66 REX.W 0F 6E, memory source)", "66480f6e07"),
    ("movq mm, r64 (REX.W 0F 6E without 66)", "480f6ec0"),
    ("pslldq with REX.W", "66480f73f904"),
    ("pclmulqdq xmm, m128 (memory source)", "660f3a440700"),
    ("pclmulqdq with REX.W", "66480f3a44c100"),
    ("aesimc xmm, m128 (memory source)", "660f38db02"),
    ("vaesenc (VEX)", "c4e279dcc1"),
    ("palignr xmm, m128 (memory source)", "660f3a0f0704"),
    ("palignr with REX.W", "66480f3a0fc104"),
    ("aeskeygenassist xmm, m128 (memory source)", "660f3adf0701"),
    ("aeskeygenassist with REX.W", "66480f3adfc101"),
    ("vaeskeygenassist (VEX)", "c4e379dfc101"),
    ("vpextrq (VEX)", "c4e3f916c001"),
    ("pcmpgtd mmx without 66", "0f66c1"),
    ("pcmpeqd mmx without 66", "0f76c1"),
    ("pcmpgtw xmm (word lanes)", "660f65c1"),
    ("pblendvb with REX.W", "66480f3810c1"),
    ("pcmpgtd with REX.W", "66480f66c1"),
    ("pcmpeqd with REX.W", "66480f76c1"),
    ("pmovzxbd register source", "66450f3831ca"),
    ("pmovsxbd register source", "66450f3821ca"),
    ("pmovzxdq register source", "66450f3835ca"),
    ("pmovsxdq register source", "66450f3825ca"),
    ("pmovzxbd with REX.W", "66480f383107"),
    ("pmovzxbq byte-to-qword lanes", "660f383207"),
    ("pmovsxbq byte-to-qword lanes", "660f382207"),
    ("punpcklqdq xmm, m128 (memory source)", "66440f6c27"),
    ("punpcklqdq with REX.W", "66480f6cc1"),
    ("palignr mmx (0F 3A 0F without 66)", "0f3a0fc104"),
    ("extractps (66 0F 3A 17)", "660f3a17c001"),
    ("movd mm, r32 (0F 6E without 66)", "0f6ec0"),
    ("psubd xmm, m128 (memory source)", "660ffa07"),
    ("psubq xmm, m128 (memory source)", "660ffb07"),
    ("psubd with REX.W", "66480ffac1"),
    ("pabsd xmm, m128 (memory source)", "660f381e07"),
    ("pabsd mmx without 66", "0f381ec1"),
    ("phaddd xmm, m128 (memory source)", "660f380207"),
    ("phaddd mmx without 66", "0f3802c1"),
    ("pcmpgtq xmm, m128 (memory source)", "660f383707"),
    ("pcmpgtq with REX.W", "66480f3837c1"),
    ("pmuludq xmm, m128 (memory source)", "660ff407"),
    ("pmuludq mmx without 66", "0ff4c1"),
    ("pmuldq xmm, m128 (memory source)", "660f382807"),
    ("pminsd xmm, m128 (memory source)", "660f383907"),
    ("pmaxsd xmm, m128 (memory source)", "660f383d07"),
    ("pmaxsd with REX.W", "66480f383dc1"),
    ("packusdw xmm, m128 (memory source)", "660f382b07"),
    ("packssdw xmm, m128 (memory source)", "660f6b07"),
    ("packssdw mmx without 66", "0f6bc1"),
    ("packsswb (66 0F 63)", "660f63c1"),
    ("pmaddwd xmm, m128 (memory source)", "660ff507"),
    ("pmaddwd mmx without 66", "0ff5c1"),
    ("pmaddwd with REX.W", "66480ff5c1"),
    ("pmaddubsw xmm, m128 (memory source)", "660f380407"),
    ("pmaddubsw mmx without 66", "0f3804c1"),
    ("pmaddubsw with REX.W", "66480f3804c1"),
    ("packuswb xmm, m128 (memory source)", "660f6707"),
    ("packuswb mmx without 66", "0f67c1"),
    ("packuswb with REX.W", "66480f67c1"),
    ("pmovzxbw register source", "66450f3830ca"),
    ("pmovsxbw register source", "66450f3820ca"),
    ("pmovzxbw with REX.W", "66480f383007"),
    ("pmovsxbw with REX.W", "66480f382007"),
    ("pmovzxwd word-to-dword lanes", "660f383307"),
    ("pmovsxwd word-to-dword lanes", "660f382307"),
    ("pminsb (66 0F 38 38)", "660f3838c1"),
    ("psadbw xmm, m128 (memory source)", "660ff607"),
    ("psadbw mmx without 66", "0ff6c1"),
    ("psadbw with REX.W", "66480ff6c1"),
    ("pavgb xmm, m128 (memory source)", "660fe007"),
    ("pavgb mmx without 66", "0fe0c1"),
    ("pavgb with REX.W", "66480fe0c1"),
    ("pavgw xmm, m128 (memory source)", "660fe307"),
    ("pavgw mmx without 66", "0fe3c1"),
    ("pavgw with REX.W", "66480fe3c1"),
    ("paddusb xmm, m128 (memory source)", "660fdc07"),
    ("paddusb mmx without 66", "0fdcc1"),
    ("paddusb with REX.W", "66480fdcc1"),
    ("paddusw (66 0F DD)", "660fddc1"),
    ("paddsb (66 0F EC)", "660fecc1"),
    ("psubusb xmm, m128 (memory source)", "660fd807"),
    ("psubusb mmx without 66", "0fd8c1"),
    ("psubusb with REX.W", "66480fd8c1"),
    ("psubusw (66 0F D9)", "660fd9c1"),
    ("psubsb (66 0F E8)", "660fe8c1"),
    ("phminposuw xmm, m128 (memory source)", "660f384107"),
    ("phminposuw with REX.W", "66480f3841c1"),
    ("psrad mmx (0F 72 /4 without 66)", "0f72e003"),
    ("psrad with REX.R (66 REX.R 0F 72 /4)", "66440f72e003"),
    ("movq r64, xmm to memory (66 REX.W 0F 7E)", "66480f7e07"),
    ("movq xmm, xmm (66 0F D6)", "660fd6c1"),
    ("movdqa with REX.W", "66480f6f06"),
    ("movapd (66 0F 28)", "660f2806"),
    ("andn with a 66 prefix", "66c4e2f0f2c0"),
    ("andn with an F3 prefix", "f3c4e2f0f2c0"),
    ("andn with a REX prefix", "40c4e2f0f2c0"),
    ("andn after a REX byte and a 2E prefix", "402ec4e278f2c1"),
    ("vzeroupper (C5)", "c5f877"),
]}

# Rejected encodings, each with the length of the window ending at the byte
# that already rules it out: the model must reject that window rather than
# find it truncated.
REJECTED_EARLY = {"psrad with REX.R (66 REX.R 0F 72 /4)": 4,
                  "pslldq with REX.W": 4, "pclmulqdq with REX.W": 5,
                  "pclmulqdq xmm, m128 (memory source)": 5,
                  "palignr xmm, m128 (memory source)": 5, "palignr with REX.W": 5,
                  "aeskeygenassist xmm, m128 (memory source)": 5,
                  "aeskeygenassist with REX.W": 5,
                  "pshufb mmx (0F 38 00 without 66)": 3, "phaddw (66 0F 38 01)": 4,
                  "pshuflw with REX.W": 4,
                  "movsd with REX.W (F2 REX.W 0F 10)": 4, "pshufw mmx (0F 70 without a prefix)": 2,
                  "pslld with REX.R (66 REX.R 0F 72 /6)": 4,
                  "psrlq with REX.R (66 REX.R 0F 73 /2)": 4}

# Encodings the model rejects that llvm-objdump does not decode either: it
# reports <unknown> at their first byte.
UNDECODED = {name: bytes.fromhex(h) for name, h in [
    ("movbe with a register r/m", "480f38f0c0"),
    ("ADX without a mandatory prefix", "480f38f6c1"),
    ("andn with VEX.L = 1", "c4e2f4f2c0"),
    ("pdep with VEX.L = 1", "c4e2f7f5c0"),
    ("pext with VEX.L = 1", "c4e2f6f5c0"),
    ("bextr with VEX.L = 1", "c4e2f4f7c0"),
    ("F5 with the 66 prefix (no PDEP, PEXT or BZHI)", "c4e2f1f5c0"),
    ("rorx with vvvv in use", "c4e3f3f0c002"),
    ("andn's group F3 /4", "c4e2f0f3e0"),
    ("andn's opcode in map 0F (C4 map 1)", "c4e1f0f2c0"),
    ("pslld with a memory operand (66 0F 72 /6)", "660f723003"),
    ("pslldq with a memory operand (66 0F 73 /7)", "660f733808"),
    ("66 0F 72 /7", "660f72f804"),
    ("psrad with a memory operand (66 0F 72 /4)", "660f722003"),
    ("66 0F 73 /4 (no PSRAQ)", "660f73e004"),
    ("66 0F 73 /1", "660f73c804"),
    ("pclmulqdq without 66 (0F 3A 44)", "0f3a44c100"),
    ("pclmulqdq with F3 for 66", "f30f3a44c100"),
    ("pblendvb without 66", "0f3810c1"),
    ("pmovzxbd without 66", "0f383107"),
    ("pmovsxbd without 66", "0f382107"),
    ("pmovzxbw without 66", "0f383007"),
    ("phminposuw without 66", "0f3841c1"),
    ("pmovsxbw without 66", "0f382007"),
    ("aesimc without 66", "0f38dbc1"),
    ("aesenc without 66", "0f38dcc1"),
    ("aesenclast without 66", "0f38ddc1"),
    ("aesdec without 66", "0f38dec1"),
    ("aesdeclast without 66", "0f38dfc1"),
    ("aeskeygenassist without 66", "0f3adfc101"),
]}

# Encodings the model decodes, each checked whole by llvm-objdump; every
# proper prefix of one is a decode vector that expects Truncated.
TRUNCATED = {name: bytes.fromhex(h) for name, h in [
    ("pblendvb with high registers", "66450f3810f9"),
    ("pblendvb with SIB and disp32", "66470f3810bc8c00010000"),
    ("pcmpgtd with high registers", "66450f66f9"),
    ("pcmpeqd with SIB and disp32", "66470f76bc8c00010000"),
    ("pmovzxbd with high base and disp8", "66450f38317c2403"),
    ("pmovsxbd with high base and disp8", "66450f38217c2403"),
    ("pmovzxdq with RIP-relative disp32", "66440f38353d00100000"),
    ("pmovsxdq with RIP-relative disp32", "66440f38253d00100000"),
    ("pmovzxbw with high base and disp8", "66450f38307c2403"),
    ("pmovsxbw with RIP-relative disp32", "66440f38203d00100000"),
    ("pmaddwd with extended registers", "66450ff5c1"),
    ("pmaddubsw with extended registers", "66450f3804c1"),
    ("packuswb with extended registers", "66450f67c1"),
    ("psadbw with extended registers", "66450ff6c1"),
    ("pavgb with extended registers", "66450fe0c1"),
    ("pavgw with extended registers", "66440fe3c1"),
    ("paddusb with extended registers", "66410fdcc1"),
    ("psubusb with extended registers", "66450fd8c1"),
    ("phminposuw with extended registers", "66450f3841c1"),
    ("pinsrq to xmm13 from an extended SIB address", "664f0f3a226c8a08ff"),
    ("pextrq from xmm11 to r9", "664d0f3a16d901"),
    ("pinsrd to xmm13 from an extended SIB address", "66470f3a226c8a0803"),
    ("pextrd from xmm11 to r9d", "66450f3a16d902"),
    ("movd xmm9, m32 with disp32", "66440f6e8f00010000"),
    ("psubq with extended registers", "66450ffbc1"),
    ("pabsd with extended registers", "66450f381ec1"),
    ("phaddd with extended registers", "66450f3802c1"),
    ("pcmpgtq with extended registers", "66450f3837c1"),
    ("pmuludq with extended registers", "66450ff4c1"),
    ("pmuldq with extended registers", "66450f3828c1"),
    ("pminsd with extended registers", "66450f3839c1"),
    ("pmaxsd with extended registers", "66450f383dc1"),
    ("packusdw with extended registers", "66450f382bc1"),
    ("packssdw with extended registers", "66450f6bc1"),
    ("psrad $32 on xmm9", "66410f72e120"),
    ("movq $imm32, r64 (REX.W C7 /0)", "48c7c001000000"),
    ("cmpb $imm8, r8 (80 /7)", "80f902"),
    ("mulx with a disp32 source", "c4e2fbf68010000000"),
    ("rorx", "c4e3fbf0c105"),
    ("blsr", "c4e2f0f3c9"),
    ("jmpq *%r8 (REX.B FF /4)", "41ffe0"),
    ("movslq (%rdx,%r8,4), %r8", "4e630482"),
    ("adcx r64, r64", "66480f38f6c1"),
    ("adox r64, r64", "f3480f38f6c1"),
    ("movbe with a disp32 and SIB", "4e0f38f0848f00010000"),
    ("pshufb xmm, m128 (RIP-relative)", "66440f38000510000000"),
    ("psrlq $imm8, xmm (66 0F 73 /2)", "66410f73d333"),
    ("pshufhw", "f30f70c1b1"),
    ("pshuflw (F2 REX.B)", "f2410f70c1b1"),
    ("crc32b with high base, SIB and disp32", "f2410f38f0848800010000"),
    ("crc32q with extended registers", "f24d0f38f1c1"),
    ("ptest with extended registers", "66450f3817c1"),
    ("movdqu xmm, m128 store (F3 0F 7F)", "f3450f7f4c2410"),
    ("pclmulqdq with extended registers", "66450f3a44c111"),
    ("aesenc with extended registers", "66450f38dcc1"),
    ("aesdeclast with a disp32 memory key", "660f38df82a0000000"),
    ("aeskeygenassist with extended registers", "66450f3adfc136"),
    ("palignr with extended registers", "66450f3a0fc10c"),
    ("psrldq $imm8, xmm (REX.B)", "66410f73d808"),
    ("movq xmm, r64 with extended registers", "664d0f6ec0"),
    ("pdep with extended registers", "c442b3f5c2"),
    ("pext", "c4e2c2f5c6"),
    ("bextr with extended registers", "c442a8f7c1"),
    ("movabsq $imm64, %r15 (REX.WB B8+r)", "49bf8877665544332211"),
]}

INTERESTING = [0, 1, 7, 8, 0x7F, 0x80, 0xFF, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF,
               0x100000000, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, MASK64]


@dataclass
class ExecCase:
    name: str
    code: bytes
    regs: list[int]
    flags: int
    data: bytes = b""  # at DATA_BASE; compared again where the case stops
    ret_addr: int = SENTINEL
    entry: int = ENTRY
    data_prot: str = "rw"  # page permissions: subsets of "rwx"
    stack_prot: str = "rw"
    # The bytes just below STACK_END compared where the case stops.
    stack_watch: int = 0
    # Whether the whole code is a single instruction (checked by decode tests).
    single: bool = True
    # The flags the architecture leaves undefined where the case stops.
    undefined: int = 0
    # XMM0..XMM15 on entry; compared again where the case stops.
    xmm: list[int] = field(default_factory=lambda: [0] * 16)
    # Optional known answers in addition to the full backend observation.
    expected_reg: tuple[int, int] | None = None  # register number, value
    expected_xmm: tuple[int, int] | None = None  # register number, value
    expected_data: tuple[int, bytes] | None = None  # DATA_BASE offset, bytes


class CaseBuilder:
    def __init__(self, seed: int) -> None:
        self.random = random.Random(seed)
        self.cases: list[ExecCase] = []

    def value(self) -> int:
        if self.random.random() < 0.4:
            return self.random.choice(INTERESTING)
        return self.random.getrandbits(64)

    def regs(self) -> list[int]:
        regs = [self.value() for _ in range(16)]
        regs[RSP] = STACK_TOP
        return regs

    def flags(self) -> int:
        return sum(1 << b for b in FLAG_BITS if self.random.random() < 0.5)

    def operand(self, avoid: tuple[int, ...] = (RSP,)) -> int:
        return self.random.choice([r for r in range(16) if r not in avoid])

    def add(self, name: str, code: bytes, regs: list[int] | None = None, *,
            flags: int | None = None, **kw) -> None:
        self.cases.append(ExecCase(name, code, regs or self.regs(),
                                   self.flags() if flags is None else flags, **kw))

    def build(self) -> list[ExecCase]:
        r = self.random
        for i in range(6):
            reg = r.randrange(16)
            self.add(f"mov {REG32[reg]}, imm32 #{i}", mov_imm32(reg, r.getrandbits(32)))
        for width, mnemonic, registers in [(0, "movl", REG32), (1, "movq", REG64)]:
            for i in range(6):
                d, s = self.operand(), self.operand()
                self.add(f"{mnemonic} {registers[s]}->{registers[d]} #{i}",
                         reg_reg(0x89, width, d, s))
        for opcode, mnemonic, widths in [(0x01, "add", (0, 1)), (0x31, "xor", (0, 1)),
                                         (0x39, "cmp", (0, 1)), (0x85, "test", (0, 1))]:
            for w in widths:
                for i in range(6):
                    d = self.operand()
                    s = d if i == 0 else self.operand()
                    self.add(f"{mnemonic}{'q' if w else 'l'} {REG64[s]}, {REG64[d]} #{i}",
                             reg_reg(opcode, w, d, s),
                             undefined=0 if mnemonic in ("add", "cmp") else AF)
        for digit, mnemonic, widths in [(0, "add", (0, 1)), (4, "and", (0,)), (7, "cmp", (0,))]:
            for w in widths:
                for i in range(6):
                    d = self.operand()
                    imm = r.choice([0x01, 0x07, 0x08, 0x7F, 0x80, 0xF8, 0xFF, r.getrandbits(8)])
                    self.add(f"{mnemonic}{'q' if w else 'l'} ${imm:#x}, {REG64[d]} #{i}",
                             reg_imm8(digit, w, d, imm),
                             undefined=AF if mnemonic == "and" else 0)
        self.movzx_cases()
        for cc in (3, 4, 5):  # jae, je, jne
            for i in range(6):
                disp = r.choice([d for d in range(-100, 101) if d not in (-2, -1)])
                self.add(f"jcc {cc} {disp:+} #{i}", jcc8(cc, disp))
        for disp in (0, 5, 100, -100):
            self.add(f"jmp {disp:+}", jmp8(disp))
        for i in range(2):
            self.add(f"ret #{i}", RET, ret_addr=CODE_BASE + r.randrange(0, 0x200, 3))
        for nop in NOPS:
            self.add(f"nop {nop.hex()}", nop)
        self.fault_cases()
        self.scalar_cases()
        self.sse_and_scalar_cases()
        self.wide_integer_cases()
        self.rotate_and_memory_cases()
        self.byte_and_mask_cases()
        self.near_branch_cases()
        self.compare_and_extend_cases()
        self.bmi_and_compare_cases()
        self.indirect_dispatch_cases()
        self.adx_cases()
        self.ssse3_cases()
        self.sse4_cases()
        self.pclmul_cases()
        self.aes_cases()
        self.keygen_and_align_cases()
        self.pdep_cases()
        self.qword_lane_cases()
        self.blend_cases()
        self.lane_cases()
        self.pack_cases()
        self.madd_cases()
        self.sad_cases()
        self.tier1_cases()
        return self.cases

    def data(self) -> bytes:
        return bytes(self.random.getrandbits(8) for _ in range(DATA_SIZE))

    def point(self, a: Address, regs: list[int], target: int,
              encode: Callable[[Address], bytes]) -> bytes:
        """encode(a), with a's base register or displacement set so that a
        addresses target."""
        index = 0 if a.index is None else regs[a.index] << a.scale
        if a.rip:
            a = Address(None, disp=target - (ENTRY + len(encode(a))), rip=True)
        elif a.base is None:
            a = Address(None, a.index, a.scale, target - index)
        else:
            regs[a.base] = (target - a.disp - index) & MASK64
        return encode(a)

    def scalar_cases(self) -> None:
        self.memory_cases()
        self.memory_fault_cases()
        self.stack_cases()
        self.alu_cases()
        self.boundary_cases()

    def memory_cases(self) -> None:
        r = self.random
        shapes = [Address(RDI), Address(RSI, disp=8), Address(RDI, 2, 2), Address(9, 10, 3, -8),
                  Address(RBP, disp=0x100), Address(13, 1, 1, 0x10), Address(RSP, disp=4),
                  Address(None, 2, 2), Address(None), Address(None, rip=True)]
        imm = r.getrandbits(8)
        forms: list[tuple[str, Callable[[int, Address], bytes], int]] = [
            ("movl m32 -> r32", lambda g, a: mem_op(b"\x8b", 0, g, a), 0),
            ("movq m64 -> r64", lambda g, a: mem_op(b"\x8b", 1, g, a), 0),
            ("movl r32 -> m32", lambda g, a: mem_op(b"\x89", 0, g, a), 0),
            ("movq r64 -> m64", lambda g, a: mem_op(b"\x89", 1, g, a), 0),
            ("movb r8 -> m8", lambda g, a: mem_op(b"\x88", 0, g, a, byte_reg=True), 0),
            ("movw r16 -> m16", lambda g, a: mem_op(b"\x89", 0, g, a, b"\x66"), 0),
            ("movzwl m16 -> r32", lambda g, a: mem_op(b"\x0f\xb7", 0, g, a), 0),
            ("leaq m -> r64", lambda g, a: mem_op(b"\x8d", 1, g, a), 0),
            ("addq m64, r64", lambda g, a: mem_op(b"\x03", 1, g, a), 0),
            ("adcq m64, r64", lambda g, a: mem_op(b"\x13", 1, g, a), 0),
            ("subq m64, r64", lambda g, a: mem_op(b"\x2b", 1, g, a), 0),
            ("sbbq m64, r64", lambda g, a: mem_op(b"\x1b", 1, g, a), 0),
            (f"cmpl ${imm:#x}, m32", lambda g, a: mem_op(b"\x83", 0, 7, a) + bytes([imm]), 0),
        ]
        for k, (name, encode, undefined) in enumerate(forms):
            for i in range(4):
                a = shapes[(4 * k + i) % len(shapes)]
                regs = self.regs()
                for index in (1, 2, 10):
                    regs[index] = r.randrange(0, 16)
                g = self.operand(avoid=(RSP, a.base, a.index))
                target = DATA_BASE + r.randrange(0, DATA_SIZE - 8)
                code = self.point(a, regs, target, lambda a: encode(g, a))
                self.add(f"{name} ({REG64[g]}, {a}) #{i}", code, regs, data=self.data(),
                         undefined=undefined)

        address = Address(RDI, RCX, scale=2, disp=8)
        regs = [0] * 16
        regs[RDI], regs[RCX], regs[RAX], regs[RSP] = DATA_BASE, 3, 0x12345678, STACK_TOP
        for name, code in (
            ("movl to", mem_op(b"\x89", 0, RAX, address)),
            ("movb to", mem_op(b"\x88", 0, RAX, address)),
            ("leaq from", mem_op(b"\x8d", 1, RAX, address)),
            ("cmpl with", mem_op(b"\x83", 0, 7, address) + b"\x7f"),
        ):
            self.add(f"{name} base-index memory", code, regs, flags=0, data=bytes(range(32)))

    def memory_fault_cases(self) -> None:
        store32 = mem_op(b"\x89", 0, RAX, Address(RDI))
        for prot in ("r", "rx"):
            regs = self.regs()
            regs[RDI] = DATA_BASE + 16
            self.add(f"movl to {prot or 'no-access'} data", store32, regs, data=self.data(),
                     data_prot=prot)
        regs = self.regs()
        regs[RDI] = DATA_BASE + 3
        self.add("movb to read-only data", mem_op(b"\x88", 0, RCX, Address(RDI)), regs,
                 data=self.data(), data_prot="r")
        regs = self.regs()
        regs[RDI] = DATA_BASE + 32
        self.add("movl from unreadable data", mem_op(b"\x8b", 0, RAX, Address(RDI)), regs,
                 data_prot="")
        self.add("movl to the code page (RIP-relative)",
                 mem_op(b"\x89", 0, RAX, Address(None, rip=True)), single=True)
        # An 8-byte store whose last byte only is past the stack page: it
        # writes none of its first 7 bytes.
        self.add("movq store crossing the stack page end",
                 mem_op(b"\x89", 1, RAX, Address(RSP, disp=1)), stack_watch=16)
        self.add("movq load crossing the stack page end",
                 mem_op(b"\x8b", 1, RAX, Address(RSP, disp=4)), stack_watch=16)

    def boundary_cases(self) -> None:
        """Carry-in alone setting CF (adc of all ones, sbb of equal operands),
        negative 32-bit displacements, and a fault after a completed store."""
        r = self.random
        CF = 1
        for opcode, mnemonic in [(b"\x13", "adcq"), (b"\x1b", "sbbq")]:
            regs = self.regs()
            g = self.operand(avoid=(RSP, RSI))
            regs[RSI] = DATA_BASE + 64
            if mnemonic == "adcq":
                regs[g] = 0  # 0 + all ones carries only with the carry-in
            source = MASK64 if mnemonic == "adcq" else regs[g]
            data = bytearray(self.data())
            data[64:72] = source.to_bytes(8, "little")
            self.add(f"{mnemonic} (%rsi), {REG64[g]} with CF set, carry-in alone sets CF",
                     mem_op(opcode, 1, g, Address(RSI)), regs, flags=self.flags() | CF,
                     data=bytes(data))
        regs = self.regs()
        d = self.operand()
        regs[d] = r.getrandbits(32) << 32 | 0xFFFFFFFF
        self.add(f"sbbl $-1, {REG32[d]} with CF set, carry-in alone sets CF",
                 reg_imm8(3, 0, d, 0xFF), regs, flags=self.flags() | CF)
        for name, encode in [("movl m32 -> r32", lambda g, a: mem_op(b"\x8b", 0, g, a)),
                             ("movq r64 -> m64", lambda g, a: mem_op(b"\x89", 1, g, a)),
                             ("leaq m -> r64", lambda g, a: mem_op(b"\x8d", 1, g, a))]:
            a = Address(RBX, disp=-0x1000)
            regs = self.regs()
            g = self.operand(avoid=(RSP, RBX))
            code = self.point(a, regs, DATA_BASE + r.randrange(0, DATA_SIZE - 8),
                              lambda a: encode(g, a))
            self.add(f"{name} ({REG64[g]}, {a})", code, regs, data=self.data())
        regs = self.regs()
        regs[RDI] = DATA_BASE + 16
        self.add("movl to data, then movq store crossing the stack page end",
                 mem_op(b"\x89", 0, RAX, Address(RDI)) + mem_op(b"\x89", 1, RAX, Address(RSP, disp=1)),
                 regs, data=self.data(), stack_watch=16, single=False)

    def stack_cases(self) -> None:
        r = self.random
        for reg in (RAX, RBX, RBP, RSP, 12, 15):
            self.add(f"pushq {REG64[reg]}", rex(0, 0, 0, reg) + bytes([0x50 + (reg & 7)]),
                     stack_watch=16)
        for reg in (RAX, RBX, RSP, 12, 15):
            self.add(f"popq {REG64[reg]}", rex(0, 0, 0, reg) + bytes([0x58 + (reg & 7)]),
                     ret_addr=r.getrandbits(64), stack_watch=16)
        for disp in (0x20, -0x60, 0x300):
            self.add(f"callq {disp:+#x}", rel32(b"\xe8", disp), stack_watch=16)
        self.add("pushq to a read-only stack", b"\x53", stack_prot="r", stack_watch=16)
        self.add("callq to a read-only stack", rel32(b"\xe8", 0x20), stack_prot="r",
                 stack_watch=16)
        self.add("popq from an unreadable stack", b"\x5b", stack_prot="")
        for i, disp in enumerate((0x40, -0x80, 0, 0x40)):
            self.add(f"je rel32 {disp:+#x} #{i}", rel32(b"\x0f\x84", disp))

    def alu_cases(self) -> None:
        r = self.random
        for opcode, mnemonic in [(0x09, "orl"), (0x21, "andl")]:
            for i in range(4):
                d, s = self.operand(), self.operand()
                self.add(f"{mnemonic} {REG32[s]}, {REG32[d]} #{i}", reg_reg(opcode, 0, d, s),
                         undefined=AF)
        for i in range(8):
            d, s = r.randrange(16), r.randrange(16)
            byte_regs = 4 <= d < 8 or 4 <= s < 8
            self.add(f"xorb {REG8[s]}, {REG8[d]} #{i}", reg_op(b"\x30", 0, s, d, byte_regs),
                     undefined=AF)
        for i in range(6):
            d = self.operand()
            imm = r.choice([0x00, 0x01, 0x7F, 0x80, 0xFF, r.getrandbits(8)])
            self.add(f"sbbl ${imm:#x}, {REG32[d]} #{i}", reg_imm8(3, 0, d, imm))
        for digit, mnemonic in [(2, "notl"), (3, "negl")]:
            for i, value in enumerate([0, 0x80000000, None, None]):
                regs = self.regs()
                d = self.operand()
                if value is not None:
                    regs[d] = r.getrandbits(32) << 32 | value
                self.add(f"{mnemonic} {REG32[d]} #{i}", reg_op(b"\xf7", 0, digit, d), regs)
        for i, value in enumerate([MASK64, 0x7FFFFFFFFFFFFFFF, 0xF, None]):
            regs = self.regs()
            d = self.operand()
            if value is not None:
                regs[d] = value
            self.add(f"incq {REG64[d]} #{i}", reg_op(b"\xff", 1, 0, d), regs)
        for i in range(6):
            regs = self.regs()
            d, s = self.operand(), self.operand()
            if i < 3:  # small products, without overflow
                regs[d] = r.getrandbits(20)
                regs[s] = (r.getrandbits(20) | (MASK64 << 20 if i else 0)) & MASK64
            self.add(f"imulq {REG64[s]}, {REG64[d]} #{i}", reg_op(b"\x0f\xaf", 1, d, s), regs,
                     undefined=AF | SF | ZF | PF)
        for i in range(4):
            d, s = self.operand(), self.operand()
            self.add(f"movslq {REG32[s]}, {REG64[d]} #{i}", reg_op(b"\x63", 1, d, s))
        for i, value in enumerate([0x7FFFFFFF, 0x80000000, None]):
            regs = self.regs()
            if value is not None:
                regs[RAX] = r.getrandbits(32) << 32 | value
            self.add(f"cltq #{i}", b"\x48\x98", regs)
        self.shift_cases()
        for i in range(6):
            d, s = self.operand(), self.operand()
            self.add(f"cmovll {REG32[s]}, {REG32[d]} #{i}", reg_op(b"\x0f\x4c", 0, d, s))
        for i in range(4):
            self.add(f"setb {REG8[i]}", reg_op(b"\x0f\x92", 0, 0, i))
        self.add("nop 90", b"\x90")

    def shift_cases(self) -> None:
        r = self.random

        def undefined(count: int, wide: bool) -> int:
            masked = count & (63 if wide else 31)
            return 0 if masked == 0 else AF if masked == 1 else AF | OF

        for digit, w, mnemonic, counts in [(5, 0, "shrl", (0, 1, 2, 31, 32, 33)),
                                           (7, 1, "sarq", (0, 1, 2, 63, 64, 65))]:
            for count in counts:
                d = self.operand()
                self.add(f"{mnemonic} ${count}, {REG64[d]}",
                         reg_op(b"\xc1", w, digit, d) + bytes([count]),
                         undefined=undefined(count, w == 1))
        for digit, mnemonic in [(4, "shll"), (7, "sarl")]:
            for count in (0, 1, 2, 31, 32, 0xFF):
                regs = self.regs()
                regs[RCX] = r.getrandbits(56) << 8 | count
                d = self.operand(avoid=(RSP, RCX))
                self.add(f"{mnemonic} %cl={count}, {REG32[d]}", reg_op(b"\xd3", 0, digit, d), regs,
                         undefined=undefined(count, False))

    def movzx_cases(self) -> None:
        r = self.random
        shapes = [  # (base, index, scale, disp)
            (RDI, 2, 0, 0), (RDI, 2, 0, 1), (RDI, 2, 0, 7), (RDI, 2, 0, -1),
            (RSI, 12, 2, 0), (9, 10, 3, -8), (RBP, 3, 0, 0), (13, 1, 1, 0x10),
            (12, 0, 0, 0x7F), (RSP, 3, 2, 8), (0, 15, 3, -128),
        ]
        for i, (base, index, scale, disp) in enumerate(shapes):
            dst = self.operand(avoid=(RSP, base, index))
            regs = self.regs()
            index_value = r.randrange(0, 16)
            regs[index] = index_value
            target = DATA_BASE + r.randrange(0, DATA_SIZE)
            regs[base] = (target - disp - (index_value << scale)) & MASK64
            data = bytes(r.getrandbits(8) for _ in range(DATA_SIZE))
            self.add(f"movzbl {REG64[dst]} <- {REG64[base]},{index},{scale},{disp} #{i}",
                     movzx8(dst, Address(base, index, scale, disp)), regs, data=data)
        for i, a in enumerate([Address(RSI, 2, 0, 0x1000), Address(None, 12, 2),
                               Address(None), Address(None, rip=True)]):
            regs = self.regs()
            regs[2], regs[12] = r.randrange(0, 16), r.randrange(0, 16)
            dst = self.operand(avoid=(RSP, a.base, a.index))
            target = DATA_BASE + r.randrange(0, DATA_SIZE)
            code = self.point(a, regs, target, lambda a: movzx8(dst, a))
            self.add(f"movzbl {REG64[dst]} <- {a} #{i}", code, regs, data=self.data())

    def fault_cases(self) -> None:
        regs = self.regs()
        regs[RDI] = DATA_BASE
        regs[2] = 3
        self.add("movzx from unreadable data", movzx8(RSI, Address(RDI, 2)), regs,
                 data_prot="")
        self.add("ret with unreadable stack", RET, stack_prot="")
        regs = self.regs()
        regs[RSP] = STACK_TOP + 4
        self.add("ret reading past the stack page", RET, regs)
        self.add("fetch from writable data", b"", entry=DATA_BASE,
                 data=b"\x31\xc0\xcc", single=False)

    def xmm(self) -> list[int]:
        """Random XMM0..XMM15, so XMMn and XMMn+8 differ and an aliased
        register shows."""
        values = [self.random.getrandbits(128) for _ in range(16)]
        assert all(values[i] != values[i + 8] for i in range(8))
        return values

    def sse_and_scalar_cases(self) -> None:
        self.sse_cases()
        self.sse_fault_cases()
        r = self.random
        for digit, mnemonic in [(4, "andq"), (7, "cmpq")]:
            for i in range(6):
                d = self.operand()
                imm = r.choice([0x01, 0x08, 0x7F, 0x80, 0xF8, 0xFF, r.getrandbits(8)])
                self.add(f"{mnemonic} ${imm:#x}, {REG64[d]} #{i}", reg_imm8(digit, 1, d, imm),
                         undefined=AF if mnemonic == "andq" else 0)
        shapes = [Address(RDI, 1, 2), Address(RDI, 1, 2, 0x10), Address(9, 10, 2, -8),
                  Address(RSI), Address(None, rip=True), Address(13, disp=0x40)]
        for i, a in enumerate(shapes):
            regs = self.regs()
            for index in (1, 10):
                regs[index] = r.randrange(0, 16)
            g = self.operand(avoid=(RSP, a.base, a.index))
            target = DATA_BASE + r.randrange(0, DATA_SIZE - 4)
            code = self.point(a, regs, target, lambda a: mem_op(b"\x03", 0, g, a))
            self.add(f"addl m32, {REG32[g]} ({a}) #{i}", code, regs, data=self.data())

    def sse_cases(self) -> None:
        """Each SSE2 form over low and high XMM registers, the 16-byte loads
        and stores at aligned and unaligned addresses."""
        r = self.random
        # Each address shape with a low or high XMM register, so every
        # combination of REX.R, REX.X and REX.B occurs.
        shapes = [(Address(RSI), False), (Address(RDI, 1, 2), True),  # none, R
                  (Address(RDI, 10, 2), False), (Address(12, RCX, 3), False),  # X, B
                  (Address(RDI, 10, 3, 8), True), (Address(13, disp=0x40), True),  # RX, RB
                  (Address(9, 10, 3, -8), False), (Address(14, 11, 1), True),  # XB, RXB
                  (Address(RDI, 1, 2, 0x10), False), (Address(RSI, disp=0x10), True),
                  (Address(None, rip=True), True), (Address(RSP), False),
                  (Address(15, disp=-0x10), False), (Address(None, 2, 3), False),
                  (Address(RBX), True), (Address(11, 12, 0), True)]
        lows = [i for i, (_, high) in enumerate(shapes) if not high]
        highs = [i for i, (_, high) in enumerate(shapes) if high]
        assert len(lows) == len(highs) == 8
        loads = [("movups m128 -> xmm", lambda x, a, f=False: mem_op(b"\x0f\x10", 0, x, a, force_rex=f)),
                 ("movdqu m128 -> xmm",
                  lambda x, a, f=False: mem_op(b"\x0f\x6f", 0, x, a, b"\xf3", force_rex=f)),
                 ("movups xmm -> m128", lambda x, a, f=False: mem_op(b"\x0f\x11", 0, x, a, force_rex=f))]
        for k, (name, encode) in enumerate(loads):
            for i, (a, high) in enumerate(shapes):
                regs = self.regs()
                for index in (1, 2, 10, 11, 12):
                    regs[index] = r.randrange(0, 16)
                # Each form on every XMM register.
                x = ((highs if high else lows).index(i) + k) % 8 + (8 if high else 0)
                aligned = i % 3 != 2
                if a.base == RSP:  # in the stack window, below the return address
                    a = Address(RSP, disp=-0x28 if aligned else -0x25)
                    self.add(f"{name} (xmm{x}, {a}, {'aligned' if aligned else 'unaligned'})",
                             encode(x, a), regs, xmm=self.xmm(), stack_watch=48)
                    continue
                target = DATA_BASE + 16 * r.randrange(0, DATA_SIZE // 16 - 1)
                if not aligned:
                    target += r.randrange(1, 16)
                code = self.point(a, regs, target, lambda a: encode(x, a))
                self.add(f"{name} (xmm{x}, {a}, {'aligned' if aligned else 'unaligned'})",
                         code, regs, data=self.data(), xmm=self.xmm())
            # A bare REX (0x40), which these forms ignore, aligned and unaligned.
            for aligned in (True, False):
                regs = self.regs()
                regs[RCX] = r.randrange(0, 16)
                x, a = r.randrange(8), Address(RSI, RCX, 2, 0x10)
                target = DATA_BASE + 16 * r.randrange(0, DATA_SIZE // 16 - 2)
                if not aligned:
                    target += r.randrange(1, 16)
                code = self.point(a, regs, target, lambda a: encode(x, a, True))
                assert b"\x40\x0f" in code
                self.add(f"{name} with REX 0x40 (xmm{x}, {a}, {'aligned' if aligned else 'unaligned'})",
                         code, regs, data=self.data(), xmm=self.xmm())
        ops = [("xorps", lambda d, s: reg_op(b"\x0f\x57", 0, d, s)),
               ("pxor", lambda d, s: b"\x66" + reg_op(b"\x0f\xef", 0, d, s)),
               ("paddd", lambda d, s: b"\x66" + reg_op(b"\x0f\xfe", 0, d, s))]
        # Every register as destination and as source, and two with d = s.
        pairs = [(d, (5 * d + 3) % 16) for d in range(16)] + [(0, 0), (9, 9)]
        for name, encode in ops:
            for d, x in pairs:
                self.add(f"{name} xmm{x}, xmm{d}", encode(d, x), xmm=self.xmm())
        for i, (d, x) in enumerate(pairs):
            imm = [0xEE, 0x55, 0x1B, 0x00, 0xFF, 0xE4][i] if i < 6 else r.getrandbits(8)
            self.add(f"pshufd ${imm:#x}, xmm{x}, xmm{d}",
                     b"\x66" + reg_op(b"\x0f\x70", 0, d, x) + bytes([imm]), xmm=self.xmm())
        for x in range(16):
            g = [n for n in range(16) if n != RSP][(7 * x + 2) % 15]
            self.add(f"movd xmm{x}, {REG32[g]}", b"\x66" + reg_op(b"\x0f\x7e", 0, x, g),
                     xmm=self.xmm())
        # The register forms with a bare REX and with REX.X, which they ignore.
        forms = [("xorps", b"", b"\x0f\x57", b""), ("pxor", b"\x66", b"\x0f\xef", b""),
                 ("paddd", b"\x66", b"\x0f\xfe", b""), ("pshufd", b"\x66", b"\x0f\x70", b"\x1b"),
                 ("movd", b"\x66", b"\x0f\x7e", b"")]
        for name, prefix, opcode, imm in forms:
            for value in (0x40, 0x42, 0x43, 0x46, 0x47):
                d, x = r.randrange(8) | (value & 4) << 1, r.randrange(8) | (value & 1) << 3
                if name == "movd" and x == RSP:  # rm is the destination GPR here
                    x = RBP
                self.add(f"{name} with REX {value:#x} (reg {d}, rm {x})",
                         prefix + bytes([value]) + opcode + bytes([0xC0 | (d & 7) << 3 | x & 7]) + imm,
                         xmm=self.xmm())

    def sse_fault_cases(self) -> None:
        store = mem_op(b"\x0f\x11", 0, 9, Address(RDI))
        regs = self.regs()
        regs[RDI] = DATA_BASE + 16
        self.add("movups to read-only data", store, regs, data=self.data(), data_prot="r",
                 xmm=self.xmm())
        regs = self.regs()
        regs[RDI] = DATA_BASE + 32
        self.add("movdqu from unreadable data", mem_op(b"\x0f\x6f", 0, 2, Address(RDI), b"\xf3"),
                 regs, data_prot="", xmm=self.xmm())
        # 16-byte accesses whose last byte only is past the stack page: the
        # store writes none of its first 15 bytes.
        self.add("movups store crossing the stack page end",
                 mem_op(b"\x0f\x11", 0, 10, Address(RSP, disp=-7)), stack_watch=32, xmm=self.xmm())
        self.add("movups to the code page (RIP-relative)",
                 mem_op(b"\x0f\x11", 0, 4, Address(None, rip=True)), xmm=self.xmm())
        self.add("movups load crossing the stack page end",
                 mem_op(b"\x0f\x10", 0, 3, Address(RSP, disp=-7)), stack_watch=32, xmm=self.xmm())

    def wide_integer_cases(self) -> None:
        self.mul_div_cases()
        self.double_shift_cases()
        self.bit_cases()
        self.widened_cases()

    def mul_div_cases(self) -> None:
        """MUL and IMUL into RDX:RAX, DIV and IDIV with their divide errors
        (#DE: a zero divisor or a quotient that doesn't fit), and CQO."""
        r = self.random
        int64_min = 1 << 63
        for digit, mnemonic, pairs in [
                (4, "mulq", [(MASK64, MASK64), (0, MASK64), (int64_min, 2), (0xFFFF, 0x10000),
                             (1, MASK64), (None, None)]),
                (5, "imulq", [(int64_min, MASK64), (MASK64, MASK64), (int64_min, 1),
                              (MASK64, int64_min), (0x7FFFFFFFFFFFFFFF, 2), (None, None)])]:
            for i, (a, b) in enumerate(pairs):
                regs = self.regs()
                s = r.choice([RAX, RDX, RCX, RBX, RSI, RDI, 8, 9, 12, 15]) if i else 11
                if a is not None:
                    regs[RAX] = a
                    if s != RAX:
                        regs[s] = b
                self.add(f"{mnemonic} {REG64[s]} (rax={regs[RAX]:#x}) #{i}",
                         reg_op(b"\xf7", 1, digit, s), regs, undefined=AF | SF | ZF | PF)
        # (digit, w, mnemonic, rdx, rax, divisor); None is random.
        for digit, w, mnemonic, hi, lo, d in [
                (6, 0, "divl", 0, 100, 7), (6, 0, "divl", 6, 0xFFFFFFFF, 7),
                (6, 0, "divl", 0, 0xFFFFFFFF, 1), (6, 0, "divl", 0, 5, 0),
                (6, 0, "divl", 7, 0, 7), (6, 0, "divl", None, None, None),
                (6, 1, "divq", 0, MASK64, 1), (6, 1, "divq", 0, MASK64, 3),
                (6, 1, "divq", 2, 0, 3), (6, 1, "divq", 0x7FFFFFFFFFFFFFFF, MASK64, int64_min),
                (6, 1, "divq", 0, 5, 0), (6, 1, "divq", 7, 0, 7), (6, 1, "divq", 8, 0, 7),
                (6, 1, "divq", None, None, None),
                (7, 1, "idivq", MASK64, MASK64 - 6, 2), (7, 1, "idivq", 0, 7, MASK64 - 1),
                (7, 1, "idivq", MASK64, 0, 2), (7, 1, "idivq", MASK64, int64_min, 1),
                (7, 1, "idivq", MASK64, int64_min, MASK64), (7, 1, "idivq", 0, int64_min, 1),
                (7, 1, "idivq", 1, 0, 3), (7, 1, "idivq", 0, 5, 0),
                (7, 1, "idivq", MASK64, 1, 3)]:
            regs = self.regs()
            s = self.operand(avoid=(RSP, RAX, RDX))
            if w == 0:  # the upper halves are ignored
                hi = None if hi is None else r.getrandbits(32) << 32 | hi
                lo = None if lo is None else r.getrandbits(32) << 32 | lo
                d = None if d is None else r.getrandbits(32) << 32 | d
            for reg, value in [(RDX, hi), (RAX, lo), (s, d)]:
                if value is not None:
                    regs[reg] = value
            self.add(f"{mnemonic} {REG64[s]} ({regs[RDX]:#x}:{regs[RAX]:#x} / {regs[s]:#x})",
                     reg_op(b"\xf7", w, digit, s), regs, undefined=FLAG_MASK)
        for digit, w, mnemonic in [(6, 0, "divl"), (6, 1, "divq"), (7, 1, "idivq")]:
            for s in (RAX, RDX):  # the divisor is part of the dividend
                regs = self.regs()
                regs[RDX] = 0 if s == RAX else 1
                regs[RAX] = r.getrandbits(64 if w else 32)
                self.add(f"{mnemonic} {REG64[s]}", reg_op(b"\xf7", w, digit, s), regs,
                         undefined=FLAG_MASK)
        for i, value in enumerate([0, int64_min, MASK64, 0x7FFFFFFFFFFFFFFF, None]):
            regs = self.regs()
            if value is not None:
                regs[RAX] = value
            self.add(f"cqto #{i}", b"\x48\x99", regs)

    def double_shift_cases(self) -> None:
        """SHLD and SHRD by CL: counts mod 64, where count 0 changes nothing."""
        r = self.random

        def undefined(count: int) -> int:
            masked = count & 63
            return 0 if masked == 0 else AF if masked == 1 else AF | OF

        for opcode, mnemonic in [(b"\x0f\xa5", "shldq"), (b"\x0f\xad", "shrdq")]:
            for count in (0, 1, 2, 31, 63, 64, 65, 0xFF):
                regs = self.regs()
                regs[RCX] = r.getrandbits(56) << 8 | count
                d = self.operand(avoid=(RSP, RCX))
                s = self.operand(avoid=(RSP, RCX, d)) if count != 2 else d
                self.add(f"{mnemonic} %cl={count}, {REG64[s]}, {REG64[d]}",
                         reg_op(opcode, 1, s, d), regs, undefined=undefined(count))
            regs = self.regs()
            regs[RCX] = 3
            d = self.operand(avoid=(RSP, RCX))
            self.add(f"{mnemonic} %cl, %rcx, {REG64[d]}", reg_op(opcode, 1, RCX, d), regs,
                     undefined=AF | OF)

    def bit_cases(self) -> None:
        """BSWAP, and TZCNT, LZCNT and POPCNT, which are defined on 0."""
        for reg in (RAX, RCX, RSP, RDI, 8, 13, 15):
            self.add(f"bswapq {REG64[reg]}", rex(1, 0, 0, reg) + bytes([0x0F, 0xC8 + (reg & 7)]))
        for opcode, mnemonic in [(b"\x0f\xbc", "tzcntq"), (b"\x0f\xbd", "lzcntq"),
                                 (b"\x0f\xb8", "popcntq")]:
            for i, value in enumerate([0, 1, 1 << 63, MASK64, 0x00F0000000000F00, None, None]):
                regs = self.regs()
                d = self.operand()
                s = d if i == 6 else self.operand()
                if value is not None:
                    regs[s] = value
                self.add(f"{mnemonic} {REG64[s]}, {REG64[d]} #{i}",
                         b"\xf3" + reg_op(opcode, 1, d, s), regs,
                         undefined=0 if mnemonic == "popcntq" else AF | OF | SF | PF)
            # Each REX: 48, 49 (REX.B), 4C (REX.R) and 4D.
            for d, s in [(RDX, RSI), (RBX, 9), (10, RDI), (14, 11)]:
                self.add(f"{mnemonic} {REG64[s]}, {REG64[d]}", b"\xf3" + reg_op(opcode, 1, d, s),
                         undefined=0 if mnemonic == "popcntq" else AF | OF | SF | PF)

    def widened_cases(self) -> None:
        """64-bit ADC, SBB, SUB and OR, carry chains, ADC with an immediate,
        IMUL from memory, MOVZX from a byte register, SETB to r8b..r15b, and
        SHL and SHR by CL or an immediate at 64 bits."""
        r = self.random
        CF = 1
        for opcode, mnemonic in [(0x11, "adcq"), (0x19, "sbbq"), (0x29, "subq"), (0x09, "orq")]:
            for i in range(6):
                regs = self.regs()
                d = self.operand()
                s = d if i == 5 else self.operand()
                if i == 0:  # all ones plus zero, carrying only with the carry-in
                    regs[d], regs[s] = MASK64, 0
                if i == 1:
                    regs[s] = regs[d]
                self.add(f"{mnemonic} {REG64[s]}, {REG64[d]} #{i}", reg_reg(opcode, 1, d, s), regs,
                         flags=self.flags() | (CF if i < 3 else 0),
                         undefined=AF if mnemonic == "orq" else 0)
        for imm, value in [(0, MASK64), (0, 5), (0xFF, 0), (0x7F, None), (0x80, None)]:
            regs = self.regs()
            d = self.operand()
            if value is not None:
                regs[d] = value
            for carry in (0, CF):
                self.add(f"adcq ${imm:#x}, {REG64[d]} CF={carry}", reg_imm8(2, 1, d, imm), regs,
                         flags=self.flags() & ~CF | carry)
        # A 192-bit add and a 192-bit subtract, ending in setb.
        for first, then, mnemonic in [(0x01, 0x11, "add"), (0x29, 0x19, "sub")]:
            regs = self.regs()
            # A carry, or a borrow, out of every limb, which setb then reads.
            regs[8], regs[9], regs[10] = (MASK64,) * 3 if first == 0x01 else (0, 0, 0)
            regs[RAX], regs[RBX], regs[RCX] = 1, 0, 0
            code = (reg_reg(first, 1, 8, RAX) + reg_reg(then, 1, 9, RBX)
                    + reg_reg(then, 1, 10, RCX) + reg_op(b"\x0f\x92", 0, 0, 11))
            self.add(f"192-bit {mnemonic} chain, then setb r11b", code, regs, single=False)
        for i, a in enumerate([Address(RSI), Address(RSI, disp=0x18), Address(RDI, 1, 3, 8),
                               Address(13, disp=-8), Address(None, rip=True)]):
            regs = self.regs()
            regs[1] = r.randrange(0, 8)
            g = self.operand(avoid=(RSP, a.base, a.index))
            target = DATA_BASE + r.randrange(0, DATA_SIZE - 8)
            code = self.point(a, regs, target, lambda a: mem_op(b"\x0f\xaf", 1, g, a))
            self.add(f"imulq m64, {REG64[g]} ({a}) #{i}", code, regs, data=self.data(),
                     undefined=AF | SF | ZF | PF)
        for i in range(10):
            d, s = r.randrange(16), (RAX, RCX, RSP, RDI, 8, 15, None, None, None, None)[i]
            s = r.randrange(16) if s is None else s
            self.add(f"movzbl {REG8[s]}, {REG32[d]} #{i}",
                     reg_op(b"\x0f\xb6", 0, d, s, 4 <= s < 8))
        for reg in (8, 9, 12, 15):
            self.add(f"setb {REG8[reg]}", reg_op(b"\x0f\x92", 0, 0, reg))

        def undefined(count: int) -> int:
            masked = count & 63
            return 0 if masked == 0 else AF if masked == 1 else AF | OF

        for count in (0, 1, 2, 32, 63, 64, 65):
            d = self.operand()
            self.add(f"shrq ${count}, {REG64[d]}", reg_op(b"\xc1", 1, 5, d) + bytes([count]),
                     undefined=undefined(count))
        for digit, mnemonic in [(4, "shlq"), (5, "shrq")]:
            for count in (0, 1, 2, 63, 64, 0xFF):
                regs = self.regs()
                regs[RCX] = r.getrandbits(56) << 8 | count
                d = self.operand(avoid=(RSP, RCX))
                self.add(f"{mnemonic} %cl={count}, {REG64[d]}", reg_op(b"\xd3", 1, digit, d), regs,
                         undefined=undefined(count))

    def rotate_and_memory_cases(self) -> None:
        self.rotate_cases()
        self.xor_memory_cases()
        self.read_only_cases()

    def rotate_cases(self) -> None:
        """ROL r32, imm8 and ROR r64, CL. OF is defined only for a masked
        count of 1, and a masked count of 0 leaves every flag unchanged."""
        r = self.random

        def undefined(count: int, wide: bool) -> int:
            return OF if count & (63 if wide else 31) > 1 else 0

        for count in (0, 1, 2, 7, 8, 12, 16, 31, 32, 33, 0xFF, r.getrandbits(8)):
            d = self.operand()
            self.add(f"roll ${count}, {REG32[d]}", reg_op(b"\xc1", 0, 0, d) + bytes([count]),
                     undefined=undefined(count, False))
        for count in (0, 1, 2, 31, 63, 64, 65, 0xFF, r.getrandbits(8)):
            regs = self.regs()
            regs[RCX] = r.getrandbits(56) << 8 | count
            d = self.operand(avoid=(RSP, RCX))
            self.add(f"rorq %cl={count}, {REG64[d]}", reg_op(b"\xd3", 1, 1, d), regs,
                     undefined=undefined(count, True))
        regs = self.regs()
        regs[RCX] = r.getrandbits(56) << 8 | 9
        self.add("rorq %cl, %rcx", reg_op(b"\xd3", 1, 1, RCX), regs, undefined=OF)

    def xor_memory_cases(self) -> None:
        """XOR r32, m32, as in a table lookup."""
        r = self.random
        shapes = [Address(RDI, 8, 2), Address(RDI, 9, 2), Address(RSI, disp=4),
                  Address(13, disp=-8), Address(None, rip=True)]
        for i, a in enumerate(shapes):
            regs = self.regs()
            for index in (8, 9):
                regs[index] = r.randrange(0, 16)
            g = self.operand(avoid=(RSP, a.base, a.index))
            target = DATA_BASE + r.randrange(0, DATA_SIZE - 4)
            code = self.point(a, regs, target, lambda a: mem_op(b"\x33", 0, g, a))
            self.add(f"xorl m32, {REG32[g]} ({a}) #{i}", code, regs, data=self.data(),
                     undefined=AF)

    def read_only_cases(self) -> None:
        """A read-only data page, as .rodata is mapped: loads succeed, and
        stores and fetches fault."""
        r = self.random
        for i, a in enumerate([Address(RDI, 8, 2), Address(None, rip=True)]):
            regs = self.regs()
            regs[8] = r.randrange(0, 16)
            target = DATA_BASE + r.randrange(0, DATA_SIZE - 4)
            code = self.point(a, regs, target, lambda a: mem_op(b"\x33", 0, RAX, a))
            self.add(f"xorl from read-only data ({a}) #{i}", code, regs, data=self.data(),
                     data_prot="r", undefined=AF)
        regs = self.regs()
        regs[RDI] = DATA_BASE + 8
        self.add("store to read-only data", mem_op(b"\x89", 0, RAX, Address(RDI)), regs,
                 data=self.data(), data_prot="r")
        self.add("fetch from read-only data", b"", entry=DATA_BASE,
                 data=b"\x31\xc0\xcc", data_prot="r", single=False)

    def byte_and_mask_cases(self) -> None:
        self.byte_compare_cases()
        self.aligned_load_cases()
        self.scalar_byte_and_mask_cases()

    def near_branch_cases(self) -> None:
        """Near conditional jumps, the two-byte NOP and SUB with an imm8."""
        r = self.random
        for i, disp in enumerate((0x40, -0x80, 0, 0x40)):
            self.add(f"jne rel32 {disp:+#x} #{i}", rel32(b"\x0f\x85", disp))
        self.add("nop 6690", b"\x66\x90")
        for i, imm in enumerate((0x48, 0x7F, 0x80, 0xFF, 0x01, r.getrandbits(8))):
            regs = self.regs()
            d = [RSP, RAX, 9, 15, RBX, self.operand()][i]
            if i == 4:
                regs[d] = 0
            self.add(f"subq ${imm:#x}, {REG64[d]} #{i}", reg_op(b"\x83", 1, 5, d) + bytes([imm]))

    def compare_and_extend_cases(self) -> None:
        """Comparison, conditional and sign-extension forms."""
        r = self.random
        CF = 1
        for cc, mnemonic in [(6, "jbe"), (9, "jns")]:
            for i, flags in enumerate([0, CF, ZF, CF | ZF, SF, SF | ZF, None, None]):
                disp = r.choice([d for d in range(-100, 101) if d not in (-2, -1)])
                self.add(f"{mnemonic} {disp:+} #{i}", jcc8(cc, disp), flags=flags)
        byte_regs = [0, 1, 2, 3] + list(range(8, 16))  # SETcc takes no plain REX
        for opcode, mnemonic in [(b"\x0f\x93", "setae"), (b"\x0f\x9c", "setl"),
                                 (b"\x0f\x9f", "setg")]:
            for i, reg in enumerate(byte_regs):
                flags = [0, CF, ZF, SF, OF, SF | OF, ZF | SF, None][i % 8]
                self.add(f"{mnemonic} {REG8[reg]}", reg_op(opcode, 0, 0, reg), flags=flags)
        for opcode, mnemonic in [(b"\x0f\x42", "cmovbq"), (b"\x0f\x4c", "cmovlq")]:
            for i, flags in enumerate([0, CF, SF, OF, SF | OF, None]):
                d, s = self.operand(), self.operand()
                self.add(f"{mnemonic} {REG64[s]}, {REG64[d]} #{i}", reg_op(opcode, 1, d, s),
                         flags=flags)
        for flags in (0, CF):
            d, s = self.operand(), self.operand()
            self.add(f"cmovbw {REG16[s]}, {REG16[d]} cf={flags}",
                     b"\x66" + reg_op(b"\x0f\x42", 0, d, s), flags=flags)
            for prefix, w, size in [(b"\x66", 0, "w"), (b"", 0, "l"), (b"", 1, "q")]:
                self.add(f"cmovb{size} m, r cf={flags}",
                         mem_op(b"\x0f\x42", w, self.operand(avoid=(RSP, RDI)), Address(RDI), prefix),
                         self.at_data(), data=self.data(), flags=flags)
        shapes = [Address(RDI, RAX), Address(RDI, RAX, 3), Address(RSI, disp=8),
                  Address(9, 10, 3, -8), Address(None, rip=True), Address(13, disp=0x10)]
        for k, (mnemonic, width) in enumerate([("cmpb", 1), ("cmpq", 8)]):
            for i, a in enumerate(shapes + shapes):
                regs = self.regs()
                for index in (RAX, 10):
                    regs[index] = r.randrange(0, 16)
                g = self.operand(avoid=(RSP, a.base, a.index))
                if width == 1 and i % 3 == 0:
                    g = [4, 7][i % 2] if 4 not in (a.base, a.index) else 7
                target = DATA_BASE + r.randrange(0, DATA_SIZE - 8)
                data = self.data()
                if i % 2:  # equal operands
                    regs[g] = (regs[g] & ~(256 ** width - 1) |
                               int.from_bytes(data[target - DATA_BASE:][:width], "little"))
                encode = (lambda a: mem_op(b"\x38", 0, g, a, byte_reg=True)) if width == 1 \
                    else (lambda a: mem_op(b"\x39", 1, g, a))
                code = self.point(a, regs, target, encode)
                reg = REG8[g] if width == 1 else REG64[g]
                self.add(f"{mnemonic} {reg}, m ({a}) #{i}", code, regs, data=data)
        for opcode, mnemonic, undefined in [(b"\x84", "testb", AF), (b"\x28", "subb", 0)]:
            for i in range(10):
                d, s = r.randrange(16), r.randrange(16)
                if i < 2:
                    d, s = [(4, 7), (12, 5)][i]
                regs = self.regs()
                if i == 2:
                    regs[d] = regs[s]
                byte = 4 <= d < 8 or 4 <= s < 8
                self.add(f"{mnemonic} {REG8[s]}, {REG8[d]} #{i}", reg_op(opcode, 0, s, d, byte),
                         regs, undefined=undefined)
        for i, imm in enumerate([0x02, 0x00, 0x7F, 0x80, 0xFF, 0x01, r.getrandbits(8), 0x02]):
            regs = self.regs()
            d = [RAX, 9, RCX, 15, 4, 7, RBX, 9][i]
            if i == 7:
                regs[d] = regs[d] & ~0xFF | 0x02
            self.add(f"cmpb ${imm:#x}, {REG8[d]} #{i}",
                     reg_op(b"\x80", 0, 7, d, 4 <= d < 8) + bytes([imm]), regs)
        for i, value in enumerate([0, 1, MASK64, 1 << 63, None, None]):
            regs = self.regs()
            d = self.operand()
            if value is not None:
                regs[d] = value
            self.add(f"shrq {REG64[d]} #{i}", reg_op(b"\xd1", 1, 5, d), regs, undefined=AF)
            self.add(f"notq {REG64[d]} #{i}", reg_op(b"\xf7", 1, 2, d), regs)
        for i, imm in enumerate([0xFFFFFFFF, 0x7FFFFFFF, 0x80000000, 0, r.getrandbits(32)]):
            d = [RAX, 9, RSI, 15, self.operand()][i]
            self.add(f"movq ${imm:#x}, {REG64[d]}",
                     reg_op(b"\xc7", 1, 0, d) + imm.to_bytes(4, "little"))
        for i in range(10):
            d, s = self.operand(), r.randrange(16)
            if i < 3:
                s = [4, 7, 12][i]
            regs = self.regs()
            regs[s] = regs[s] & ~0xFF | [0x80, 0x7F, 0xFF][i % 3]
            self.add(f"movsbl {REG8[s]}, {REG32[d]} #{i}",
                     reg_op(b"\x0f\xbe", 0, d, s, 4 <= s < 8), regs)

    def bmi_and_compare_cases(self) -> None:
        """Memory comparisons, SETcc with a bare REX, and VEX-encoded BMI forms."""
        self.compare_memory_cases()
        for opcode, mnemonic in [(b"\x0f\x92", "setb"), (b"\x0f\x94", "sete")]:
            for reg in range(8):
                flags = [0, 1, ZF, 1 | ZF, None][reg % 5]
                self.add(f"{mnemonic} {REG8[reg]} (REX 40)", reg_op(opcode, 0, 0, reg, True),
                         flags=flags)
        self.mulx_cases()
        self.vex_shift_cases()
        self.bmi1_cases()
        for opcode, mnemonic in [(b"\x0f\x93", "setae"), (b"\x0f\x9c", "setl"),
                                 (b"\x0f\x9f", "setg")]:
            for reg in range(4, 8):
                self.add(f"{mnemonic} {REG8[reg]} (REX 40)", reg_op(opcode, 0, 0, reg, True),
                         flags=[0, SF, ZF | OF, None][reg % 4])

    def indirect_dispatch_cases(self) -> None:
        """The forms used in indirect dispatch: JA, MOVSXD and JMP r64."""
        r = self.random
        CF = 1
        for i, flags in enumerate([0, CF, ZF, CF | ZF, SF, OF, None, None]):
            disp = r.choice([d for d in range(-100, 101) if d not in (-2, -1)])
            self.add(f"ja {disp:+} #{i}", jcc8(7, disp), flags=flags)
        shapes = [Address(RDX, RCX, 2), Address(RDX, 8, 2), Address(10, RAX, 2),
                  Address(RSI, disp=8), Address(None, rip=True), Address(13, disp=0x10)]
        for i, a in enumerate(shapes + shapes):
            regs = self.regs()
            for index in (RCX, RAX, 8):
                regs[index] = r.randrange(0, 16)
            d = self.operand(avoid=(RSP, a.base, a.index)) if i % 3 else a.base or RAX
            target = DATA_BASE + r.randrange(0, DATA_SIZE - 4)
            code = self.point(a, regs, target, lambda a: mem_op(b"\x63", 1, d, a))
            self.add(f"movslq m ({a}), {REG64[d]} #{i}", code, regs, data=self.data(),
                     data_prot="r" if i % 4 == 1 else "rw")
        regs = self.regs()
        regs[RDX] = DATA_BASE + 4
        self.add("movslq from unreadable data", mem_op(b"\x63", 1, RCX, Address(RDX)), regs,
                 data_prot="")
        # Each register's jump lands on an int3 of the code page; RSP's, on
        # the stack page, which is not executable.
        for reg in range(16):
            regs = self.regs()
            if reg != RSP:
                regs[reg] = CODE_BASE + r.randrange(0, 0xF0)
            self.add(f"jmpq *{REG64[reg]}", reg_op(b"\xff", 0, 4, reg), regs)
        for target, place in [(DATA_BASE + 8, "data"), (0x400000, "unmapped memory")]:
            regs = self.regs()
            regs[RAX] = target
            self.add(f"jmpq *%rax to {place}", reg_op(b"\xff", 0, 4, RAX), regs)

    def compare_memory_cases(self) -> None:
        r = self.random
        for mnemonic, encode in [("cmpb", lambda g, a: mem_op(b"\x38", 0, g, a, byte_reg=True)),
                                 ("cmpq", lambda g, a: mem_op(b"\x39", 1, g, a))]:
            for i, a in enumerate([Address(None, RAX), Address(None, 10, 3), Address(None, RSI, 2)]):
                regs = self.regs()
                regs[a.index] = r.randrange(0, 16)
                g = self.operand(avoid=(RSP, a.index))
                code = self.point(a, regs, DATA_BASE + r.randrange(0, DATA_SIZE - 8),
                                  lambda a: encode(g, a))
                self.add(f"{mnemonic} {REG64[g]}, m ({a}) #{i}", code, regs, data=self.data())
            regs = self.regs()
            regs[RDI] = DATA_BASE + 40
            self.add(f"{mnemonic} with read-only data", encode(RCX, Address(RDI)), regs,
                     data=self.data(), data_prot="r")
            self.add(f"{mnemonic} with unreadable data", encode(RCX, Address(RDI)), regs,
                     data_prot="")
        # A byte just past the stack page, and 8 bytes of which the last 4 are.
        self.add("cmpb past the stack page end",
                 mem_op(b"\x38", 0, RCX, Address(RSP, disp=8), byte_reg=True), stack_watch=16)
        self.add("cmpq crossing the stack page end", mem_op(b"\x39", 1, RCX, Address(RSP, disp=4)),
                 stack_watch=16)

    def mulx_cases(self) -> None:
        """MULX takes rdx times its source; the high half goes to the ModRM
        register and the low half to vvvv, and with both the same register
        it holds the high half."""
        r = self.random
        pairs = [(RAX, RCX), (RCX, RCX), (RDX, RBX), (RBX, RDX), (RDX, RDX), (9, 14), (15, 8)]
        for i, (hi, lo) in enumerate(pairs + pairs):
            src = [RDX, RSI, 11][i % 3]
            regs = self.regs()
            if i >= len(pairs):
                regs[RDX] = r.choice([MASK64, 1 << 63, 0, 1])
            self.add(f"mulxq {REG64[src]}, {REG64[lo]}, {REG64[hi]} #{i}",
                     vex_reg(2, 3, 1, 0xF6, hi, lo, src), regs)
        shapes = [Address(RDI), Address(RSI, disp=8), Address(RDI, RAX, 3), Address(9, 10, 3, -8),
                  Address(None, RCX, 2), Address(None, rip=True), Address(13, disp=0x10)]
        for i, a in enumerate(shapes):
            regs = self.regs()
            for index in (RAX, RCX, 10):
                regs[index] = r.randrange(0, 16)
            hi, lo = self.operand(avoid=(RSP, a.base, a.index)), self.operand()
            code = self.point(a, regs, DATA_BASE + r.randrange(0, DATA_SIZE - 8),
                              lambda a: vex_mem(2, 3, 1, 0xF6, hi, lo, a))
            self.add(f"mulxq m ({a}), {REG64[lo]}, {REG64[hi]} #{i}", code, regs,
                     data=self.data())
        regs = self.regs()
        regs[RDI] = DATA_BASE + 24
        mulx = vex_mem(2, 3, 1, 0xF6, RAX, RCX, Address(RDI))
        self.add("mulxq from read-only data", mulx, regs, data=self.data(), data_prot="r")
        self.add("mulxq from unreadable data", mulx, regs, data_prot="")
        self.add("mulxq crossing the stack page end",
                 vex_mem(2, 3, 1, 0xF6, RAX, RCX, Address(RSP, disp=4)), stack_watch=16)

    def vex_shift_cases(self) -> None:
        """RORX by an immediate masked to the width; SHLX, SHRX and SARX by a
        register masked to 6 bits. None of them changes the flags."""
        r = self.random
        for w, width in [(0, 32), (1, 64)]:
            for i, imm in enumerate([0, 1, width - 1, width, width + 1, 0xFF, r.getrandbits(8)]):
                d, src = self.operand(), self.operand()
                self.add(f"rorx{'q' if w else 'l'} ${imm:#x}, {REG64[src]}, {REG64[d]} #{i}",
                         vex_reg(3, 3, w, 0xF0, d, 0, src) + bytes([imm]))
        for pp, mnemonic in [(1, "shlxq"), (3, "shrxq"), (2, "sarxq")]:
            counts = [0, 1, 63, 64, 65, 127, 1 << 63 | 5, None]
            for i, count in enumerate(counts):
                d, src, cnt = self.operand(), self.operand(), self.operand()
                if i == 6:
                    cnt = src
                regs = self.regs()
                if i % 2:
                    regs[src] |= 1 << 63
                if count is not None:
                    regs[cnt] = count
                self.add(f"{mnemonic} {REG64[cnt]}, {REG64[src]}, {REG64[d]} #{i}",
                         vex_reg(2, pp, 1, 0xF7, d, cnt, src), regs)

    def bmi1_cases(self) -> None:
        """ANDN, BZHI, BLSR, BLSI and BLSMSK, which leave AF and PF undefined."""
        for i in range(8):
            d, a, b = self.operand(), self.operand(), self.operand()
            if i == 0:
                b = a
            regs = self.regs()
            if i in (1, 2):
                regs[a], regs[b] = [(MASK64, MASK64), (0, 1 << 63)][i - 1]
            self.add(f"andnq {REG64[b]}, {REG64[a]}, {REG64[d]} #{i}",
                     vex_reg(2, 0, 1, 0xF2, d, a, b), regs, undefined=AF | PF)
        for i, index in enumerate([0, 1, 63, 64, 255, 256 + 5, 1 << 63 | 3, None, None]):
            d, a, n = self.operand(), self.operand(), self.operand()
            regs = self.regs()
            if index is not None:
                regs[n] = index
            if i == 7:
                n = a
            self.add(f"bzhiq {REG64[n]}, {REG64[a]}, {REG64[d]} #{i}",
                     vex_reg(2, 0, 1, 0xF5, d, n, a), regs, undefined=AF | PF)
        for digit, mnemonic in [(1, "blsrq"), (3, "blsiq"), (2, "blsmskq")]:
            for i, value in enumerate([0, 1, 1 << 63, MASK64, 6, None, None]):
                d, src = self.operand(), self.operand()
                regs = self.regs()
                if value is not None:
                    regs[src] = value
                if i == 6:
                    d = src
                self.add(f"{mnemonic} {REG64[src]}, {REG64[d]} #{i}",
                         vex_reg(2, 0, 1, 0xF3, digit, d, src), regs, undefined=AF | PF)

    def byte_compare_cases(self) -> None:
        """PCMPEQB, PAND, POR and PADDQ on every register pair shape, PMOVMSKB
        on boundary masks, and MOVQ r64, xmm from every XMM register."""
        r = self.random

        def mixed(a: int, b: int) -> int:
            """b with a random half of its bytes replaced by a's."""
            keep = [r.random() < 0.5 for _ in range(16)]
            return sum((a if k else b) & 0xFF << 8 * i for i, k in enumerate(keep))

        ops = [("pcmpeqb", b"\x0f\x74"), ("pand", b"\x0f\xdb"), ("por", b"\x0f\xeb"),
               ("paddq", b"\x0f\xd4")]
        pairs = [(d, (5 * d + 3) % 16) for d in range(16)] + [(0, 0), (9, 9)]
        for name, opcode in ops:
            for d, x in pairs:
                xmm = self.xmm()
                if name == "pcmpeqb":
                    xmm[x] = mixed(xmm[d], xmm[x])
                self.add(f"{name} xmm{x}, xmm{d}", b"\x66" + reg_op(opcode, 0, d, x), xmm=xmm)
            for value in (0x40, 0x42):  # a bare REX and REX.X, which these ignore
                d, x = r.randrange(8), r.randrange(8)
                self.add(f"{name} with REX {value:#x} (reg {d}, rm {x})",
                         b"\x66" + bytes([value]) + opcode + bytes([0xC0 | d << 3 | x]),
                         xmm=self.xmm())
        # Carries out of each 64-bit lane are dropped.
        xmm = self.xmm()
        xmm[1], xmm[2] = (1 << 128) - 1, 1 << 64 | 1
        self.add("paddq lane carries", b"\x66" + reg_op(b"\x0f\xd4", 0, 1, 2), xmm=xmm)
        masks = [0, (1 << 128) - 1, 0x80, 0x80 << 120, 0x7F7F7F7F7F7F7F7F7F7F7F7F7F7F7F7F,
                 0x8000FF007F80017F8000FF007F80017F, None, None]
        gprs = [g for g in range(16) if g != RSP]
        for x in range(16):
            xmm = self.xmm()
            if masks[x % 8] is not None:
                xmm[x] = masks[x % 8]
            g = gprs[(7 * x + 2) % 15]
            self.add(f"pmovmskb xmm{x}, {REG32[g]}", b"\x66" + reg_op(b"\x0f\xd7", 0, g, x),
                     xmm=xmm)
        for x in range(16):
            g = gprs[(4 * x + 1) % 15]
            self.add(f"movq xmm{x}, {REG64[g]}", b"\x66" + reg_op(b"\x0f\x7e", 1, x, g),
                     xmm=self.xmm())

    def aligned_load_cases(self) -> None:
        """MOVDQA loads from aligned addresses, including RIP-relative and
        read-only data, and its faults: a misaligned address raises #GP
        before any page check."""
        r = self.random
        shapes = [Address(RSI), Address(RDI, 1, 2), Address(RDI, 10, 3, 0x10),
                  Address(13, disp=0x40), Address(9, 10, 1, -0x10), Address(None, rip=True),
                  Address(14, 11, 0), Address(RBX)]
        movdqa = lambda x, a: mem_op(b"\x0f\x6f", 0, x, a, b"\x66")
        for i, a in enumerate(shapes):
            for x in (i, i + 8):
                regs = self.regs()
                for index in (1, 10, 11):
                    regs[index] = 16 * r.randrange(0, 4)
                target = DATA_BASE + 16 * r.randrange(0, DATA_SIZE // 16 - 4)
                code = self.point(a, regs, target, lambda a: movdqa(x, a))
                self.add(f"movdqa m128 -> xmm{x} ({a})", code, regs, data=self.data(),
                         xmm=self.xmm(), data_prot="r" if i % 4 == 3 else "rw")
        for offset, prot in [(1, "rw"), (8, "rw"), (15, "r"), (4, ""), (0, "")]:
            regs = self.regs()
            regs[RDI] = DATA_BASE + 32 + offset
            fault = "unreadable" if not prot else "read-only" if prot == "r" else "readable"
            self.add(f"movdqa from {fault} data at offset {offset}",
                     movdqa(3, Address(RDI)), regs, data=self.data(), data_prot=prot,
                     xmm=self.xmm())
        regs = self.regs()
        regs[RDI] = DATA_BASE + 0x1000 - 8
        self.add("movdqa misaligned across the data page end", movdqa(5, Address(RDI)), regs,
                 data=self.data(), xmm=self.xmm())

    def scalar_byte_and_mask_cases(self) -> None:
        """OR EAX, imm32, XOR r32, imm32, SETE, and TZCNT and POPCNT on 32-bit
        registers, which ignore the source's upper half and zero the
        destination's."""
        r = self.random
        for i, imm in enumerate([0x10000, 0, 0x80000000, 0xFFFFFFFF, r.getrandbits(32)]):
            self.add(f"orl ${imm:#x}, %eax #{i}", b"\x0d" + imm.to_bytes(4, "little"),
                     undefined=AF)
        for d in range(16):
            imm = [0xFFFF, 0x80000000, 0xFFFFFFFF, 0, r.getrandbits(32)][d % 5]
            self.add(f"xorl ${imm:#x}, {REG32[d]}",
                     reg_op(b"\x81", 0, 6, d) + imm.to_bytes(4, "little"), undefined=AF)
        for reg in (RAX, RCX, RDX, RBX, 8, 11, 15):
            for zf in (0, ZF):
                self.add(f"sete {REG8[reg]} (ZF={int(bool(zf))})", reg_op(b"\x0f\x94", 0, 0, reg),
                         flags=self.flags() & ~ZF | zf)
        for opcode, mnemonic in [(b"\x0f\xbc", "tzcntl"), (b"\x0f\xb8", "popcntl")]:
            values = [0, 1, 1 << 31, 0xFFFFFFFF, 1 << 32, MASK64, 0xF0000000F0000F00, None]
            for i, value in enumerate(values):
                regs = self.regs()
                d = self.operand()
                s = d if i == 7 else self.operand()
                if value is not None:
                    regs[s] = value
                self.add(f"{mnemonic} {REG32[s]}, {REG32[d]} #{i}",
                         b"\xf3" + reg_op(opcode, 0, d, s), regs,
                         undefined=0 if mnemonic == "popcntl" else AF | OF | SF | PF)
            for d, s in [(RBX, 9), (10, RDI), (14, 11)]:
                self.add(f"{mnemonic} {REG32[s]}, {REG32[d]}", b"\xf3" + reg_op(opcode, 0, d, s),
                         undefined=0 if mnemonic == "popcntl" else AF | OF | SF | PF)

    def adx_cases(self) -> None:
        adcx = b"\x66" + reg_op(b"\x0f\x38\xf6", 1, RAX, 8)
        adox = b"\xf3" + reg_op(b"\x0f\x38\xf6", 1, RCX, 9)
        adcx_next = b"\x66" + reg_op(b"\x0f\x38\xf6", 1, 10, 12)
        adox_next = b"\xf3" + reg_op(b"\x0f\x38\xf6", 1, 11, 13)
        for carry_in in (1, OF):
            regs = self.regs()
            regs[RAX], regs[RCX] = MASK64, MASK64
            regs[8] = regs[9] = regs[12] = regs[13] = 0
            regs[10] = regs[11] = 17
            flags = carry_in | AF | PF | ZF | SF
            self.add(f"adcx, incoming flags {flags:#x}", adcx, regs, flags=flags)
            self.add(f"adox, incoming flags {flags:#x}", adox, regs, flags=flags)
            self.add(f"interleaved ADX, incoming flags {flags:#x}",
                     adcx + adox + adcx_next + adox_next, regs, flags=flags, single=False)

        load = mem_op(b"\x0f\x38\xf0", 1, RAX, Address(RDI))
        store = mem_op(b"\x0f\x38\xf1", 1, RSI, Address(RDI))
        regs = self.regs()
        regs[RDI], regs[RSI] = DATA_BASE + 3, 0xFEDCBA9876543210
        data = b"\x00\x00\x00\x01\x23\x45\x67\x89\xab\xcd\xef"
        self.add("movbe unaligned big-endian load", load, regs, data=data, data_prot="r")
        self.add("movbe unaligned big-endian store", store, regs, data=data)
        self.add("movbe load from unreadable data", load, regs, data=data, data_prot="")
        for prot in ("r", "rx"):
            self.add(f"movbe store to {prot} data", store, regs, data=data, data_prot=prot)
        self.add("movbe store to code", mem_op(b"\x0f\x38\xf1", 1, RSI, Address(None, rip=True)))

    def ssse3_cases(self) -> None:
        self.pshufb_cases()
        self.lane_shift_cases()
        self.xmm_move_cases()

    def pshufb_cases(self) -> None:
        """PSHUFB on every register as destination and as control, with
        controls that permute, repeat an index, set bit 7 or set bits 4..6;
        and from memory, aligned and not, including read-only data."""
        r = self.random
        pshufb = lambda d, x: b"\x66" + reg_op(b"\x0f\x38\x00", 0, d, x)
        controls = [int.from_bytes(bytes(range(15, -1, -1)), "little"),  # reversal
                    int.from_bytes(bytes([5] * 16), "little"),  # one byte everywhere
                    int.from_bytes(bytes([0x80 | i for i in range(16)]), "little"),  # all zeroed
                    int.from_bytes(bytes([0x7F, 0x10, 0x23, 0x8F, 0xF0, 0x4A, 0x00, 0xFF] * 2),
                                   "little")]  # bits 4..6 ignored, bit 7 zeroes
        pairs = [(d, (5 * d + 3) % 16) for d in range(16)] + [(0, 0), (9, 9), (12, 12)]
        for i, (d, x) in enumerate(pairs):
            xmm = self.xmm()
            if i < len(controls) * 2:
                xmm[x] = controls[i % len(controls)]
            self.add(f"pshufb xmm{x}, xmm{d} #{i}", pshufb(d, x), xmm=xmm)
        for value in (0x40, 0x41, 0x44, 0x45, 0x42):  # REX.X is ignored
            d, x = r.randrange(8) | (value & 4) << 1, r.randrange(8) | (value & 1) << 3
            self.add(f"pshufb with REX {value:#x} (reg {d}, rm {x})",
                     b"\x66" + bytes([value]) + b"\x0f\x38\x00" + bytes([0xC0 | (d & 7) << 3 | x & 7]),
                     xmm=self.xmm())
        pshufb_mem = lambda d, a: mem_op(b"\x0f\x38\x00", 0, d, a, b"\x66")
        shapes = [Address(RSI), Address(RDI, 1, 2), Address(13, disp=0x40), Address(None, rip=True),
                  Address(9, 10, 3, -0x10), Address(RBX)]
        for i, a in enumerate(shapes):
            for d in (i, i + 9):
                regs = self.regs()
                for index in (1, 10):
                    regs[index] = 16 * r.randrange(0, 4)
                target = DATA_BASE + 16 * r.randrange(0, DATA_SIZE // 16 - 4)
                code = self.point(a, regs, target, lambda a: pshufb_mem(d, a))
                self.add(f"pshufb m128, xmm{d} ({a})", code, regs, data=self.data(),
                         xmm=self.xmm(), data_prot="r" if i % 3 == 2 else "rw")
        for offset, prot in [(1, "rw"), (8, "r"), (15, ""), (0, "")]:
            regs = self.regs()
            regs[RDI] = DATA_BASE + 32 + offset
            fault = "unreadable" if not prot else "read-only" if prot == "r" else "readable"
            self.add(f"pshufb from {fault} data at offset {offset}",
                     pshufb_mem(11, Address(RDI)), regs, data=self.data(), data_prot=prot,
                     xmm=self.xmm())

    def lane_shift_cases(self) -> None:
        """PSLLD, PSRLD, PSLLQ and PSRLQ by 0, counts within a lane, the lane
        width and more, on low and high registers."""
        r = self.random
        forms = [("pslld", 0x72, 6), ("psrld", 0x72, 2), ("psllq", 0x73, 6), ("psrlq", 0x73, 2)]
        counts = [0, 1, 7, 12, 25, 31, 32, 33, 51, 63, 64, 65, 0x80, 0xFF]
        for name, opcode, digit in forms:
            for i, count in enumerate(counts + [r.getrandbits(8)]):
                x = (3 * i + opcode) % 16
                self.add(f"{name} ${count:#x}, xmm{x}",
                         b"\x66" + reg_op(bytes([0x0F, opcode]), 0, digit, x) + bytes([count]),
                         xmm=self.xmm())

    def xmm_move_cases(self) -> None:
        """MOVDQA between registers, PSHUFLW and PSHUFHW, and MOVDQU stores
        at aligned and unaligned addresses and to read-only data."""
        r = self.random
        pairs = [(d, (7 * d + 5) % 16) for d in range(16)] + [(4, 4)]
        for d, x in pairs:
            self.add(f"movdqa xmm{x}, xmm{d}", b"\x66" + reg_op(b"\x0f\x6f", 0, d, x),
                     xmm=self.xmm())
        for prefix, name in [(b"\xf2", "pshuflw"), (b"\xf3", "pshufhw")]:
            for i, (d, x) in enumerate(pairs):
                imm = [0xB1, 0x1B, 0x00, 0xFF, 0xE4][i] if i < 5 else r.getrandbits(8)
                self.add(f"{name} ${imm:#x}, xmm{x}, xmm{d}",
                         prefix + reg_op(b"\x0f\x70", 0, d, x) + bytes([imm]), xmm=self.xmm())
        movdqu = lambda x, a: mem_op(b"\x0f\x7f", 0, x, a, b"\xf3")
        shapes = [Address(RDI), Address(RDI, 1, 2, 0x10), Address(12, RCX, 3), Address(14, 11, 0),
                  Address(None, 2, 3)]
        for i, a in enumerate(shapes):
            for aligned in (True, False):
                regs = self.regs()
                for index in (1, 2, 11):
                    regs[index] = r.randrange(0, 8)
                x = (3 * i + aligned * 8 + 1) % 16
                target = DATA_BASE + 16 * r.randrange(0, DATA_SIZE // 16 - 4)
                if not aligned:
                    target += r.randrange(1, 16)
                code = self.point(a, regs, target, lambda a: movdqu(x, a))
                self.add(f"movdqu xmm{x} -> m128 ({a}, {'aligned' if aligned else 'unaligned'})",
                         code, regs, data=self.data(), xmm=self.xmm())
        regs = self.regs()
        regs[RDI] = DATA_BASE + 16
        self.add("movdqu to read-only data", movdqu(6, Address(RDI)), regs, data=self.data(),
                 data_prot="r", xmm=self.xmm())
        self.add("movdqu store crossing the stack page end", movdqu(13, Address(RSP, disp=-3)),
                 stack_watch=32, xmm=self.xmm())

    def sse4_cases(self) -> None:
        """CRC32 zero extension and flag preservation, all PTEST flag
        combinations, and wrapping unsigned lane arithmetic."""
        crc_byte, crc_word = b"\x0f\x38\xf0", b"\x0f\x38\xf1"
        for d, src in [(RAX, RSI), (2, 1), (8, 9), (13, 7), (11, 11)]:
            for opcode, wide in [(crc_byte, 0), (crc_word, 1)]:
                regs = self.regs()
                regs[src] = 0x8877665544332291
                regs[d] |= 0x8000000000000000
                self.add(f"crc32{'q' if wide else 'b'} to register {d} from {src}",
                         b"\xf2" + reg_op(opcode, wide, d, src, force_rex=not wide and 4 <= src < 8),
                         regs, flags=FLAG_MASK)
        for prot in ("r", ""):
            regs = self.regs()
            regs[9] = DATA_BASE + 3
            regs[12] = 0x12345678FFFFFFFF
            self.add(f"crc32b from {'readable' if prot else 'unreadable'} memory",
                     mem_op(crc_byte, 0, 12, Address(9), b"\xf2"),
                     regs, flags=FLAG_MASK, data=bytes(range(DATA_SIZE)), data_prot=prot)

        regs[10] = 3
        self.add("crc32b from base-index memory",
                 mem_op(crc_byte, 0, 12, Address(9, 10, scale=1, disp=1), b"\xf2"),
                 regs, flags=FLAG_MASK, data=bytes(range(DATA_SIZE)), data_prot="r")

        top = 1 << 127
        for d, src, flags in [(0, 1, FLAG_MASK), (12, 8, FLAG_MASK ^ ZF)]:
            for a, b in [(0, 0), (0, top), (top, top), (top, top | 1)]:
                xmm = self.xmm()
                xmm[d], xmm[src] = a, b
                self.add(f"ptest xmm{src}, xmm{d} on {a:#x}, {b:#x}",
                         b"\x66" + reg_op(b"\x0f\x38\x17", 0, d, src),
                         flags=flags, xmm=xmm)

        for name, opcode in [("pmulld", 0x40), ("pminud", 0x3B), ("pmaxud", 0x3F)]:
            for d, src in [(0, 1), (3, 12), (15, 2), (9, 10), (11, 11)]:
                xmm = self.xmm()
                xmm[d] = 0xFFFFFFFF800000000000000300000000
                if d != src:
                    # Lane 2 keeps bit 31 after multiplying by 3 and wrapping.
                    xmm[src] = 0xFFFFFFFF0000000300000004FFFFFFFF
                self.add(f"{name} xmm{src}, xmm{d}",
                         b"\x66" + reg_op(bytes([0x0F, 0x38, opcode]), 0, d, src),
                         flags=FLAG_MASK, xmm=xmm)

    def pclmul_cases(self) -> None:
        """PCLMULQDQ on every selector, with the other immediate bits set
        and clear, carries cancelling, the degree-126 product, and high and
        equal registers; PSLLDQ and PSRLDQ by 0 to past 16 bytes; MOVQ to an
        XMM register."""
        r = self.random
        ones, top = (1 << 64) - 1, 1 << 63
        pairs = [(0, 1), (2, 9), (12, 3), (15, 8), (5, 5), (10, 14), (13, 10)]
        imms = [0x00, 0x01, 0x10, 0x11, 0xEE, 0xFF, 0x5A, 0xA5]
        for i, (d, x) in enumerate(pairs):
            for imm in imms + [r.getrandbits(8)]:
                self.add(f"pclmulqdq ${imm:#x}, xmm{x}, xmm{d} #{i}",
                         b"\x66" + reg_op(b"\x0f\x3a\x44", 0, d, x) + bytes([imm]),
                         flags=FLAG_MASK, xmm=self.xmm())
        # (low, high) qwords of the destination and source: 3 * 3 = 5 as the
        # x + 1 squares cancel; all-ones and x^63 squared reach degree 126.
        for a, b in [((3, 7), (3, 11)), ((ones, ones), (ones, ones)), ((top, 1), (top, top)),
                     ((0, ones), (ones, 0)), ((0x87, 1 << 32), (0x87, 0x1B))]:
            for imm in (0x00, 0x01, 0x10, 0x11):
                xmm = self.xmm()
                xmm[4] = a[0] | a[1] << 64
                xmm[11] = b[0] | b[1] << 64
                self.add(f"pclmulqdq ${imm:#x} on {a}, {b}",
                         b"\x66" + reg_op(b"\x0f\x3a\x44", 0, 4, 11) + bytes([imm]),
                         flags=FLAG_MASK, xmm=xmm)
        for name, digit in [("pslldq", 7), ("psrldq", 3)]:
            for i, count in enumerate([0, 1, 7, 8, 15, 16, 17, 0x80, 0xFF, r.getrandbits(8)]):
                x = (5 * i + digit) % 16
                self.add(f"{name} ${count:#x}, xmm{x}",
                         b"\x66" + reg_op(b"\x0f\x73", 0, digit, x) + bytes([count]),
                         flags=FLAG_MASK, xmm=self.xmm())
        gprs = [g for g in range(16) if g != RSP]
        for x in range(16):
            g = gprs[(3 * x + 4) % 15]
            self.add(f"movq {REG64[g]}, xmm{x}", b"\x66" + reg_op(b"\x0f\x6e", 1, x, g),
                     flags=FLAG_MASK, xmm=self.xmm())

    def aes_cases(self) -> None:
        """Exercise the legacy AES round opcodes, flags, and FIPS 197 known answers."""
        prefix = b"\x66"
        register_pairs = [(0, 1), (2, 3), (4, 8), (9, 5), (6, 7),
                          (8, 9), (10, 11), (12, 13), (14, 15), (15, 15)]
        for opcode, name in enumerate(("aesimc", "aesenc", "aesenclast", "aesdec", "aesdeclast"), 0xDB):
            op = bytes([0x0F, 0x38, opcode])
            for d, src in register_pairs:
                self.add(f"{name} xmm{src}, xmm{d}", prefix + reg_op(op, 0, d, src),
                         flags=FLAG_MASK, xmm=self.xmm())
            if name != "aesimc":
                regs = self.regs()
                regs[13] = DATA_BASE
                self.add(f"{name} aligned memory key to xmm14",
                         mem_op(op, 0, 14, Address(13, disp=160), prefix),
                         regs, flags=FLAG_MASK, data=self.data(), xmm=self.xmm())

        for op, name in [(b"\x0f\x38\xdc", "aesenc"), (b"\x0f\xef", "pxor")]:
            code = mem_op(op, 0, 8, Address(RDX), prefix)
            for offset, perms, label in [(1, "rw", "misaligned"), (0, "", "unreadable")]:
                regs = self.regs()
                regs[RDX] = DATA_BASE + offset
                self.add(f"{name} {label} memory", code, regs,
                         flags=FLAG_MASK, data=self.data(), data_prot=perms, xmm=self.xmm())

        def word(text: str) -> int:
            return int.from_bytes(bytes.fromhex(text), "little")

        # Original FIPS 197 Appendix B, the states after round-key XOR.
        for at, state, key, result in [
            (1, "193de3bea0f4e22b9ac68d2ae9f84808",
             "a0fafe1788542cb123a339392a6c7605", "a49c7ff2689f352b6b5bea43026a5049"),
            (2, "a49c7ff2689f352b6b5bea43026a5049",
             "f2c295f27a96b9435935807a7359f67f", "aa8f5f0361dde3ef82d24ad26832469a"),
        ]:
            xmm = self.xmm()
            xmm[:2] = [word(state), word(key)]
            self.add(f"AESENC FIPS 197 Appendix B round {at}",
                     prefix + reg_op(b"\x0f\x38\xdc", 0, 0, 1),
                     flags=FLAG_MASK, xmm=xmm, expected_xmm=(0, word(result)))

        # Appendix C.1 gives encryption and equivalent inverse round keys.
        for name, opcode, state, key, result in [
            ("aesenclast", 0xDD, "bd6e7c3df2b5779e0b61216e8b10b689", bytes.fromhex("13111d7fe3944a17f307a78b4d2b30c5"),
             "69c4e0d86a7b0430d8cdb78070b4c55a"),
            ("aesdec", 0xDE, "7ad5fda789ef4e272bca100b3d9ff59f", bytes.fromhex("13aa29be9c8faff6f770f58000f7bf03"),
             "54d990a16ba09ab596bbf40ea111702f"),
            ("aesdeclast", 0xDF, "6353e08c0960e104cd70b751bacad0e7", bytes.fromhex("000102030405060708090a0b0c0d0e0f"),
             "00112233445566778899aabbccddeeff"),
            ("aesimc", 0xDB, "549932d1f08557681093ed9cbe2c974e", bytes(16),
             "13aa29be9c8faff6f770f58000f7bf03"),
        ]:
            xmm = self.xmm()
            xmm[:2] = [word(state), int.from_bytes(key, "little")]
            if name == "aesimc":
                xmm[1] = word(state)
            self.add(f"{name} FIPS 197 Appendix C.1",
                     prefix + reg_op(bytes([0x0F, 0x38, opcode]), 0, 0, 1),
                     flags=FLAG_MASK, xmm=xmm, expected_xmm=(0, word(result)))

    def keygen_and_align_cases(self) -> None:
        """AESKEYGENASSIST on the round constants and other immediates and
        PALIGNR by 0 to past 32 bytes, with high and equal registers."""
        r = self.random
        pairs = [(0, 1), (2, 9), (12, 3), (15, 8), (5, 5), (10, 14), (13, 10)]
        for i, (d, x) in enumerate(pairs):
            for imm in [0x00, 0x01, 0x1B, 0x36, 0x80, 0xFF, r.getrandbits(8)]:
                self.add(f"aeskeygenassist ${imm:#x}, xmm{x}, xmm{d} #{i}",
                         b"\x66" + reg_op(b"\x0f\x3a\xdf", 0, d, x) + bytes([imm]),
                         flags=FLAG_MASK, xmm=self.xmm())
            for imm in [0, 1, 4, 8, 12, 15, 16, 17, 24, 31, 32, 0x80, 0xFF, r.getrandbits(8)]:
                self.add(f"palignr ${imm:#x}, xmm{x}, xmm{d} #{i}",
                         b"\x66" + reg_op(b"\x0f\x3a\x0f", 0, d, x) + bytes([imm]),
                         flags=FLAG_MASK, xmm=self.xmm())

        self.add("aeskeygenassist $0x1, xmm11, xmm4",
                 b"\x66" + reg_op(b"\x0f\x3a\xdf", 0, 4, 11) + b"\x01",
                 flags=FLAG_MASK, xmm=self.xmm())
        self.add("aeskeygenassist $0x36, xmm7, xmm11",
                 b"\x66" + reg_op(b"\x0f\x3a\xdf", 0, 11, 7) + b"\x36",
                 flags=FLAG_MASK, xmm=self.xmm())
        for imm in range(33):
            self.add(f"palignr ${imm:#x}, xmm6, xmm11",
                     b"\x66" + reg_op(b"\x0f\x3a\x0f", 0, 11, 6) + bytes([imm]),
                     flags=FLAG_MASK, xmm=self.xmm())

    def pdep_cases(self) -> None:
        """PDEP and PEXT on boundary, Morton and random masks, BEXTR on
        controls that start or run past bit 63 or set bits above 15, MOVABS
        into every register."""
        r = self.random
        morton = 0x5555555555555555
        for pp, mnemonic in [(3, "pdepq"), (2, "pextq")]:
            masks = [0, MASK64, morton, morton << 1, 1 << 63, 1, 0xFFFFFFFF, MASK64 ^ 0xFFFFFFFF,
                     r.getrandbits(64) & r.getrandbits(64), r.getrandbits(64), None, None]
            for i, mask in enumerate(masks):
                d, src, m = self.operand(), self.operand(), self.operand()
                if i == 9:
                    d = src
                elif i == 10:
                    d = m
                elif i == 11:
                    m = src
                regs = self.regs()
                if mask is not None:
                    regs[m] = mask
                self.add(f"{mnemonic} {REG64[m]}, {REG64[src]}, {REG64[d]} #{i}",
                         vex_reg(2, pp, 1, 0xF5, d, src, m), regs)
        controls = [(0, 0), (0, 1), (0, 63), (0, 64), (0, 255), (7, 13), (63, 1), (63, 2),
                    (60, 10), (64, 5), (200, 8), (5, 0), None, None]
        for i, control in enumerate(controls):
            d, src, c = self.operand(), self.operand(), self.operand()
            if i == 12:
                d = c
            elif i == 13:
                c = src
            regs = self.regs()
            if control is not None:
                start, length = control
                regs[c] = r.getrandbits(48) << 16 | length << 8 | start
            self.add(f"bextrq {REG64[c]}, {REG64[src]}, {REG64[d]} #{i}",
                     vex_reg(2, 0, 1, 0xF7, d, c, src), regs, undefined=AF | SF | PF)
        for reg in range(16):
            imm = r.choice([0, MASK64, morton, morton << 1, 1 << 63, r.getrandbits(64)])
            self.add(f"movabsq ${imm:#x}, {REG64[reg]}",
                     rex(1, 0, 0, reg) + bytes([0xB8 + (reg & 7)]) + imm.to_bytes(8, "little"))

    def qword_lane_cases(self) -> None:
        qword_mask = (1 << 64) - 1
        for imm in (0, 1, 0x80, 0xFF):
            shift = 64 * (imm & 1)
            regs, xmm = self.regs(), self.xmm()
            flags = FLAG_MASK if imm < 2 else 0
            self.add(f"pinsrq ${imm:#x}, r10, xmm13",
                     b"\x66" + reg_op(b"\x0f\x3a\x22", 1, 13, 10) + bytes([imm]),
                     regs, xmm=xmm, flags=flags,
                     expected_xmm=(13, (xmm[13] & ~(qword_mask << shift)) | (regs[10] << shift)))
            self.add(f"pextrq ${imm:#x}, xmm13, r10",
                     b"\x66" + reg_op(b"\x0f\x3a\x16", 1, 13, 10) + bytes([imm]),
                     regs, xmm=xmm, flags=flags, expected_reg=(10, (xmm[13] >> shift) & qword_mask))

            data = self.data()
            regs = regs.copy()
            regs[12], regs[9] = DATA_BASE, 7
            address = Address(base=12, index=9, scale=1, disp=3)
            mem = int.from_bytes(data[17:25], "little")
            insert = mem_op(b"\x0f\x3a\x22", 1, 13, address, prefix=b"\x66") + bytes([imm])
            extract = mem_op(b"\x0f\x3a\x16", 1, 13, address, prefix=b"\x66") + bytes([imm])
            self.add(f"pinsrq ${imm:#x}, m64, xmm13", insert, regs, xmm=xmm, data=data, flags=flags,
                     expected_xmm=(13, (xmm[13] & ~(qword_mask << shift)) | (mem << shift)))
            self.add(f"pextrq ${imm:#x}, xmm13, m64", extract, regs, xmm=xmm, data=data, flags=flags,
                     expected_data=(17, ((xmm[13] >> shift) & qword_mask).to_bytes(8, "little")))
        self.add("pinsrq unreadable qword", insert, regs, xmm=xmm, data=data, data_prot="")
        self.add("pextrq read-only qword", extract, regs, xmm=xmm, data=data, data_prot="r")

        for dst, src in ((12, 3), (4, 4)):
            xmm = self.xmm()
            code = b"\x66" + reg_op(b"\x0f\x6c", 0, dst, src)
            self.add(f"punpcklqdq xmm{src}, xmm{dst}", code, xmm=xmm, flags=FLAG_MASK,
                     expected_xmm=(dst, (xmm[dst] & qword_mask) | ((xmm[src] & qword_mask) << 64)))

        for value in (0, 1, 1 << 63, qword_mask):
            regs = self.regs()
            regs[9] = value
            self.add(f"decq r9 input {value:#x}", reg_op(b"\xff", 1, 1, 9), regs, flags=FLAG_MASK,
                     expected_reg=(9, (value - 1) & qword_mask))

    def blend_cases(self) -> None:
        prefix = b"\x66"
        blend = b"\x0f\x38\x10"
        mask = bytes([0x00, 0x7F, 0x80, 0xFF, 0x01, 0x81, 0x55, 0xAA] * 2)
        for dst, src in ((0, 15), (8, 0), (9, 10), (11, 12), (13, 14), (15, 15)):
            xmm = self.xmm()
            xmm[0] = int.from_bytes(mask, "little")
            a, b = (xmm[r].to_bytes(16, "little") for r in (dst, src))
            expected = bytes(y if m & 0x80 else x for x, y, m in zip(a, b, mask))
            self.add(f"pblendvb xmm{src}, xmm{dst}", prefix + reg_op(blend, 0, dst, src),
                     xmm=xmm, flags=FLAG_MASK, expected_xmm=(dst, int.from_bytes(expected, "little")))

        a = [-(1 << 31), -1, 0, (1 << 31) - 1]
        b = [0, -1, -1, -(1 << 31)]
        lhs, rhs = (b"".join(v.to_bytes(4, "little", signed=True) for v in lanes)
                    for lanes in (a, b))
        xmm = self.xmm()
        xmm[0] = int.from_bytes(mask, "little")
        xmm[15], xmm[8] = int.from_bytes(lhs, "little"), int.from_bytes(rhs, "little")
        selected = bytes(y if m & 0x80 else x for x, y, m in zip(lhs, rhs, mask))
        for name, opcode, expected in (
            ("pblendvb", blend, selected),
            ("pcmpgtd", b"\x0f\x66", bytes([0] * 8 + [255] * 8)),
            ("pcmpeqd", b"\x0f\x76", bytes([0] * 4 + [255] * 4 + [0] * 8)),
        ):
            result = (15, int.from_bytes(expected, "little"))
            if name != "pblendvb":
                self.add(f"{name} xmm8, xmm15", prefix + reg_op(opcode, 0, 15, 8),
                         xmm=xmm, flags=0, expected_xmm=result)
            regs = self.regs()
            regs[12], regs[9] = DATA_BASE, 3
            address = Address(base=12, index=9, scale=2, disp=4)
            code = mem_op(opcode, 0, 15, address, prefix=prefix)
            data = bytes(16) + rhs
            self.add(f"{name} from aligned read-only m128", code, regs, xmm=xmm, data=data,
                     flags=FLAG_MASK, data_prot="r", expected_xmm=result)
            base_code = mem_op(opcode, 0, 15, Address(12, disp=16), prefix=prefix)
            self.add(f"{name} from aligned base-displacement memory", base_code,
                     regs, xmm=xmm, data=data, flags=FLAG_MASK, expected_xmm=result)
            self.add(f"{name} from unreadable m128", code, regs, xmm=xmm, data=data, data_prot="")
            misaligned = regs.copy()
            misaligned[12] += 1
            self.add(f"{name} from misaligned m128", code, misaligned, xmm=xmm, data=data)

        self.widen_page_end_cases(WIDEN_FORMS)

    def widen_page_end_cases(self, forms) -> None:
        """Each PMOVZX/PMOVSX form reading an operand that ends at the mapped
        page boundary, and one that crosses it."""
        prefix = b"\x66"
        samples = {(1, 4): bytes([0x00, 0x7F, 0x80, 0xFF]),
                   (4, 8): bytes.fromhex("00000080 ffffffff"),
                   (1, 2): bytes([0x00, 0x7F, 0x80, 0xFF, 0x01, 0xFE, 0x81, 0x7E])}
        for name, opcode, width, result_width, signed in forms:
            source = samples[width, result_width]
            size = len(source)
            code = mem_op(bytes([0x0F, 0x38, opcode]), 0, 13, Address(RSP, disp=8 - size),
                          prefix=prefix)
            # The operand ends exactly at the mapped page boundary. The
            # saved return address supplies its bytes without a stack write.
            ret = int.from_bytes(bytes(8 - size) + source, "little")
            expected = int.from_bytes(widen_lanes(source, width, result_width, signed), "little")
            self.add(f"{name} exact {size}-byte read at page end", code, xmm=self.xmm(),
                     flags=FLAG_MASK, ret_addr=ret, expected_xmm=(13, expected))
            crossing = mem_op(bytes([0x0F, 0x38, opcode]), 0, 13, Address(RSP, disp=9 - size),
                              prefix=prefix)
            self.add(f"{name} crossing page end", crossing, xmm=self.xmm())

    def lane_cases(self) -> None:
        """PINSRD, PEXTRD and MOVD xmm, r/m32, and the packed dword and qword
        arithmetic at the signed lane boundaries."""
        prefix = b"\x66"
        for imm in (0, 1, 2, 3, 0x81, 0xFE, 0xFF):  # bits 7..2 are ignored
            shift = 32 * (imm & 3)
            regs, xmm = self.regs(), self.xmm()
            self.add(f"pinsrd ${imm:#x}, r10d, xmm13",
                     prefix + reg_op(b"\x0f\x3a\x22", 0, 13, 10) + bytes([imm]), regs, xmm=xmm,
                     expected_xmm=(13, (xmm[13] & ~(M32 << shift)) | (regs[10] & M32) << shift))
            # The 32-bit destination clears the upper half of r10.
            self.add(f"pextrd ${imm:#x}, xmm13, r10d",
                     prefix + reg_op(b"\x0f\x3a\x16", 0, 13, 10) + bytes([imm]), regs, xmm=xmm,
                     expected_reg=(10, xmm[13] >> shift & M32))
            self.add(f"pinsrd ${imm:#x}, esi, xmm0",
                     prefix + reg_op(b"\x0f\x3a\x22", 0, 0, RSI) + bytes([imm]), regs, xmm=xmm,
                     expected_xmm=(0, (xmm[0] & ~(M32 << shift)) | (regs[RSI] & M32) << shift))

            data = self.data()
            regs = regs.copy()
            regs[12], regs[9] = DATA_BASE, 7
            address = Address(base=12, index=9, scale=1, disp=3)
            mem = int.from_bytes(data[17:21], "little")
            insert = mem_op(b"\x0f\x3a\x22", 0, 13, address, prefix=prefix) + bytes([imm])
            extract = mem_op(b"\x0f\x3a\x16", 0, 13, address, prefix=prefix) + bytes([imm])
            self.add(f"pinsrd ${imm:#x}, m32, xmm13", insert, regs, xmm=xmm, data=data,
                     expected_xmm=(13, (xmm[13] & ~(M32 << shift)) | mem << shift))
            self.add(f"pextrd ${imm:#x}, xmm13, m32", extract, regs, xmm=xmm, data=data,
                     expected_data=(17, (xmm[13] >> shift & M32).to_bytes(4, "little")))
        self.add("pinsrd unreadable dword", insert, regs, xmm=xmm, data=data, data_prot="")
        self.add("pextrd read-only dword", extract, regs, xmm=xmm, data=data, data_prot="r")

        for dst, src in ((0, RDI), (9, 10), (15, RBX)):
            regs, xmm = self.regs(), self.xmm()
            self.add(f"movd {REG32[src]}, xmm{dst}",
                     prefix + reg_op(b"\x0f\x6e", 0, dst, src), regs, xmm=xmm,
                     expected_xmm=(dst, regs[src] & M32))
        data = self.data()
        regs[12], regs[9] = DATA_BASE, 7
        address = Address(base=12, index=9, scale=1, disp=3)
        load = mem_op(b"\x0f\x6e", 0, 9, address, prefix=prefix)
        self.add("movd m32, xmm9", load, regs, xmm=xmm, data=data,
                 expected_xmm=(9, int.from_bytes(data[17:21], "little")))
        self.add("movd unreadable m32", load, regs, xmm=xmm, data=data, data_prot="")

        bounds32 = lanes32([1 << 31, M32, 0, (1 << 31) - 1])
        operands = [
            (bounds32, lanes32([0, 1, 1 << 31, M32])),
            (lanes32([5, -3 & M32, 10, 0]), bounds32),
            (lanes64([1 << 63, M64]), lanes64([M64, 1 << 63])),
            (lanes64([0, (1 << 63) - 1]), lanes64([(1 << 63) - 1, 0])),
            (lanes64([M64, 0]), lanes64([M64, 0])),
        ]
        for name, opcode, result in LANE_OPS:
            for i, (a, b) in enumerate(operands):
                for dst, src in ((15, 8), (2, 3)):
                    xmm = self.xmm()
                    xmm[dst], xmm[src] = a, b
                    self.add(f"{name} xmm{src}, xmm{dst} #{i}",
                             prefix + reg_op(opcode, 0, dst, src), xmm=xmm,
                             expected_xmm=(dst, result(a, b)))
            xmm = self.xmm()
            self.add(f"{name} xmm4, xmm4", prefix + reg_op(opcode, 0, 4, 4), xmm=xmm,
                     expected_xmm=(4, result(xmm[4], xmm[4])))

    def pack_cases(self) -> None:
        """PSRAD by immediate counts below, at and above 32, and the packed
        multiplies, signed minimum and maximum and saturating packs,
        at the signed lane and saturation boundaries."""
        prefix = b"\x66"
        bounds32 = lanes32([1 << 31, M32, 0, (1 << 31) - 1])
        for count in (0, 1, 3, 31, 32, 33, 0x80, 0xFF):
            for x, v in ((0, bounds32), (9, lanes32([-9, 100, 1 << 30, -(1 << 30)])),
                         (15, self.random.getrandbits(128))):
                xmm = self.xmm()
                xmm[x] = v
                self.add(f"psrad ${count:#x}, xmm{x} #{v:#x}",
                         prefix + reg_op(b"\x0f\x72", 0, 4, x) + bytes([count]), xmm=xmm,
                         expected_xmm=(x, psrad(v, count)))

        operands = [
            (bounds32, lanes32([0, 1, 1 << 31, M32])),
            (lanes32([M32, 0x12345678, 1 << 31, 0xDEADBEEF]), lanes32([M32, 9, -2, 7])),
            (lanes32([0xFFFF, 0x10000, -1, -0x8000]), lanes32([0x7FFF, 0x8000, -0x8001, 0])),
            (lanes32([-0x10000, 0xFFFE, 1, -0x7FFF]), bounds32),
        ]
        for name, opcode, result in PACK_OPS:
            for i, (a, b) in enumerate(operands):
                for dst, src in ((15, 8), (2, 3)):
                    xmm = self.xmm()
                    xmm[dst], xmm[src] = a, b
                    self.add(f"{name} xmm{src}, xmm{dst} #{i}",
                             prefix + reg_op(opcode, 0, dst, src), xmm=xmm,
                             expected_xmm=(dst, result(a, b)))
            xmm = self.xmm()
            self.add(f"{name} xmm4, xmm4", prefix + reg_op(opcode, 0, 4, 4), xmm=xmm,
                     expected_xmm=(4, result(xmm[4], xmm[4])))


    def madd_cases(self) -> None:
        """The pairwise multiply-adds and the unsigned byte pack at
        the signed word and byte boundaries and their saturation bounds, and
        PMOVZXBW and PMOVSXBW at the page boundary."""
        prefix = b"\x66"
        bounds16 = lanes16([-0x8000, -0x8000, 0x7FFF, 0x7FFF, -0x8000, 0x7FFF, 0, -1])
        bytes_ = lambda bs: int.from_bytes(bytes(bs), "little")
        operands = [
            (bounds16, bounds16),
            (bounds16, lanes16([-0x8000, -0x8000, -0x8000, -0x8000, 0x7FFF, 0x7FFF, 1, 1])),
            (bytes_([0xFF] * 16), bytes_([0x7F, 0x7F, 0x80, 0x80, 0x7F, 0x80, 0x80, 0x7F] * 2)),
            (bytes_([0xFF, 1, 0x80, 0x80, 0, 0, 1, 2] * 2), bytes_([0x80] * 4 + [0x7F] * 4 + [3, 4] * 4)),
            (lanes16([-1, 0, 0xFF, 0x100, -0x8000, 0x7FFF, 1, -0x80]),
             lanes16([0x80, 0xFE, 0x101, -1, 0x7F, -0x7FFF, 0xFF, 2])),
            (self.random.getrandbits(128), self.random.getrandbits(128)),
        ]
        for name, opcode, result in MADD_OPS:
            for i, (a, b) in enumerate(operands):
                for dst, src in ((15, 8), (2, 3)):
                    xmm = self.xmm()
                    xmm[dst], xmm[src] = a, b
                    self.add(f"{name} xmm{src}, xmm{dst} #{i}",
                             prefix + reg_op(opcode, 0, dst, src), xmm=xmm, flags=FLAG_MASK,
                             expected_xmm=(dst, result(a, b)))
            xmm = self.xmm()
            self.add(f"{name} xmm4, xmm4", prefix + reg_op(opcode, 0, 4, 4), xmm=xmm,
                     expected_xmm=(4, result(xmm[4], xmm[4])))
        self.widen_page_end_cases(WIDEN16_FORMS)

        source = bytes.fromhex("00 7f 80 ff 01 fe 81 7e")
        regs = [0] * 16
        regs[RSP] = STACK_TOP
        regs[12] = DATA_BASE - 3
        for name, opcode, width, result_width, signed in WIDEN16_FORMS:
            code = mem_op(bytes([0x0F, 0x38, opcode]), 0, 15, Address(12, disp=3),
                          prefix=prefix)
            expected = int.from_bytes(widen_lanes(source, width, result_width, signed), "little")
            self.add(f"{name} with high base and disp8", code, regs, data=source,
                     flags=FLAG_MASK, expected_xmm=(15, expected))

    def sad_cases(self) -> None:
        """The byte and word operations at their bounds: PSADBW's
        largest sums, the averages and saturating sums at 0 and the top, and
        PHMINPOSUW's ties and a minimum in the last lane."""
        prefix = b"\x66"
        bytes_ = lambda bs: int.from_bytes(bytes(bs), "little")
        operands = [
            (bytes_([0xFF] * 16), bytes_([0] * 16)),
            (bytes_([0] * 16), bytes_([0xFF] * 16)),
            (bytes_([0xFF] * 16), bytes_([0xFF] * 16)),
            (bytes_([1, 10, 0, 0xFF, 0x80, 7, 3, 200, 0, 0, 0, 0, 0, 0, 0, 9]),
             bytes_([10, 1, 0xFF, 0, 0x7F, 7, 4, 100, 0, 0, 0, 0, 0, 0, 0, 0])),
            (lanes16([0xFFFF, 0, 0x8000, 0x7FFF, 1, 2, 0xFFFE, 3]),
             lanes16([5, 3, 9, 3, 7, 3, 8, 4])),
            (lanes16([9, 9, 9, 9, 9, 9, 9, 9]), lanes16([9, 9, 0xFFFF, 9, 9, 9, 9, 2])),
            (self.random.getrandbits(128), self.random.getrandbits(128)),
        ]
        for name, opcode, result in SAD_OPS:
            for i, (a, b) in enumerate(operands):
                for dst, src in ((15, 8), (2, 3)):
                    xmm = self.xmm()
                    xmm[dst], xmm[src] = a, b
                    self.add(f"{name} xmm{src}, xmm{dst} #{i}",
                             prefix + reg_op(opcode, 0, dst, src), xmm=xmm, flags=FLAG_MASK,
                             expected_xmm=(dst, result(a, b)))
            xmm = self.xmm()
            self.add(f"{name} xmm4, xmm4", prefix + reg_op(opcode, 0, 4, 4), xmm=xmm,
                     expected_xmm=(4, result(xmm[4], xmm[4])))


    # The general-purpose integer forms at every operand size, the stack,
    # flag, control-transfer and string instructions.

    def tier1_cases(self) -> None:
        self.sized_alu_cases()
        self.sized_move_cases()
        self.extension_cases()
        self.sized_unary_cases()
        self.sized_shift_cases()
        self.sized_rotate_cases()
        self.sized_mul_div_cases()
        self.sized_double_shift_cases()
        self.exchange_cases()
        self.bit_test_cases()
        self.sized_extension_isa_cases()
        self.sized_stack_cases()
        self.flag_cases()
        self.control_cases()
        self.string_cases()
        self.prefix_cases()

    def byte_reg(self, high: bool) -> int:
        """A byte register: without REX, 4..7 are AH, CH, DH and BH; with
        REX (forced by the caller), any of the sixteen low bytes."""
        return self.random.randrange(8 if high else 16)

    def at_data(self, reg: int = RDI, offset: int = 64) -> list[int]:
        regs = self.regs()
        regs[reg] = DATA_BASE + offset
        return regs

    def sized_alu_cases(self) -> None:
        r = self.random
        for k, mnemonic in enumerate(["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"]):
            undefined = AF if mnemonic in ("or", "and", "xor") else 0
            base = 8 * k
            for high in (True, False):
                d, s = self.byte_reg(high), self.byte_reg(high)
                self.add(f"{mnemonic}b r8, r8 ({'no REX' if high else 'REX'})",
                         reg_op(bytes([base]), 0, s, d, force_rex=not high), undefined=undefined)
            d, s = self.operand(), self.operand()
            self.add(f"{mnemonic}w r16, r16", b"\x66" + reg_op(bytes([base + 1]), 0, s, d),
                     undefined=undefined)
            self.add(f"{mnemonic}l r32, r32 (reversed)", reg_op(bytes([base + 3]), 0, d, s),
                     undefined=undefined)
            g = self.operand(avoid=(RSP, RDI))
            for name, code in [
                    ("b m8, r8", mem_op(bytes([base + 2]), 0, g, Address(RDI), byte_reg=True)),
                    ("b r8, m8", mem_op(bytes([base]), 0, g & 7, Address(RDI))),
                    ("w m16, r16", mem_op(bytes([base + 3]), 0, g, Address(RDI), b"\x66")),
                    ("w r16, m16", mem_op(bytes([base + 1]), 0, g, Address(RDI), b"\x66")),
                    ("l r32, m32", mem_op(bytes([base + 1]), 0, g, Address(RDI)))]:
                self.add(f"{mnemonic}{name}", code, self.at_data(), data=self.data(),
                         undefined=undefined)
            imm8, imm16 = r.getrandbits(8), r.getrandbits(16)
            for high in (True, False):
                d = self.byte_reg(high)
                self.add(f"{mnemonic}b ${imm8:#x}, r8 ({'no REX' if high else 'REX'})",
                         rex(0, 0, 0, d, not high) + bytes([0x80, 0xC0 | k << 3 | d & 7, imm8]),
                         undefined=undefined)
            d = self.operand()
            self.add(f"{mnemonic}w ${imm16:#x}, r16",
                     b"\x66" + reg_op(b"\x81", 0, k, d) + imm16.to_bytes(2, "little"),
                     undefined=undefined)
            self.add(f"{mnemonic}w ${imm8:#x} (sign-extended), r16",
                     b"\x66" + reg_op(b"\x83", 0, k, d) + bytes([imm8]), undefined=undefined)
            self.add(f"{mnemonic}b ${imm8:#x}, al", bytes([base + 4, imm8]), undefined=undefined)
            self.add(f"{mnemonic}w ${imm16:#x}, ax",
                     bytes([0x66, base + 5]) + imm16.to_bytes(2, "little"), undefined=undefined)
            self.add(f"{mnemonic}l $imm32, m32",
                     mem_op(b"\x81", 0, k, Address(RDI)) + r.getrandbits(32).to_bytes(4, "little"),
                     self.at_data(), data=self.data(), undefined=undefined)
            self.add(f"{mnemonic}b ${imm8:#x}, m8", mem_op(b"\x80", 0, k, Address(RDI)) + bytes([imm8]),
                     self.at_data(), data=self.data(), undefined=undefined)
        for high in (True, False):
            d, s = self.byte_reg(high), self.byte_reg(high)
            self.add(f"testb r8, r8 ({'no REX' if high else 'REX'})",
                     reg_op(b"\x84", 0, s, d, force_rex=not high), undefined=AF)
            self.add(f"testb $imm8, r8 ({'no REX' if high else 'REX'})",
                     rex(0, 0, 0, d, not high) + bytes([0xF6, 0xC0 | d & 7, r.getrandbits(8)]),
                     undefined=AF)
        d, s = self.operand(), self.operand()
        self.add("testw r16, r16", b"\x66" + reg_op(b"\x85", 0, s, d), undefined=AF)
        self.add("testw $imm16, r16",
                 b"\x66" + reg_op(b"\xf7", 0, 0, d) + r.getrandbits(16).to_bytes(2, "little"),
                 undefined=AF)
        self.add("testb $imm8, al", bytes([0xA8, r.getrandbits(8)]), undefined=AF)
        self.add("testw $imm16, ax", b"\x66\xa9" + r.getrandbits(16).to_bytes(2, "little"),
                 undefined=AF)
        self.add("testl $imm32, eax", b"\xa9" + r.getrandbits(32).to_bytes(4, "little"),
                 undefined=AF)
        self.add("testq r64, m64", mem_op(b"\x85", 1, RAX, Address(RDI)), self.at_data(),
                 data=self.data(), undefined=AF)

    def sized_move_cases(self) -> None:
        r = self.random
        for high in (True, False):
            d, s = self.byte_reg(high), self.byte_reg(high)
            self.add(f"movb r8, r8 ({'no REX' if high else 'REX'})",
                     reg_op(b"\x88", 0, s, d, force_rex=not high))
            self.add(f"movb m8, r8 ({'no REX' if high else 'REX'})",
                     mem_op(b"\x8a", 0, s, Address(RDI), force_rex=not high), self.at_data(),
                     data=self.data())
            self.add(f"movb r8, m8 ({'no REX' if high else 'REX'})",
                     mem_op(b"\x88", 0, s, Address(RDI), force_rex=not high), self.at_data(),
                     data=self.data())
            self.add(f"movb $imm8, r8 ({'no REX' if high else 'REX'})",
                     rex(0, 0, 0, d, not high) + bytes([0xB0 | d & 7, r.getrandbits(8)]))
            self.add(f"movb $imm8, r8 (C6, {'no REX' if high else 'REX'})",
                     rex(0, 0, 0, d, not high) + bytes([0xC6, 0xC0 | d & 7, r.getrandbits(8)]))
        d, s = self.operand(), self.operand()
        self.add("movw r16, r16", b"\x66" + reg_op(b"\x89", 0, s, d))
        self.add("movw m16, r16", mem_op(b"\x8b", 0, s, Address(RDI), b"\x66"), self.at_data(),
                 data=self.data())
        self.add("movw $imm16, r16",
                 b"\x66" + rex(0, 0, 0, d) + bytes([0xB8 | d & 7]) + r.getrandbits(16).to_bytes(2, "little"))
        self.add("movw $imm16, r16 (C7)",
                 b"\x66" + reg_op(b"\xc7", 0, 0, d) + r.getrandbits(16).to_bytes(2, "little"))
        self.add("movw $imm16, m16", mem_op(b"\xc7", 0, 0, Address(RDI), b"\x66")
                 + r.getrandbits(16).to_bytes(2, "little"), self.at_data(), data=self.data())
        self.add("movb $imm8, m8", mem_op(b"\xc6", 0, 0, Address(RDI)) + bytes([r.getrandbits(8)]),
                 self.at_data(), data=self.data())
        self.add("movl $imm32, m32", mem_op(b"\xc7", 0, 0, Address(RDI))
                 + r.getrandbits(32).to_bytes(4, "little"), self.at_data(), data=self.data())
        self.add("movl $imm32, r32 (C7)", reg_op(b"\xc7", 0, 0, d) + r.getrandbits(32).to_bytes(4, "little"))
        for i in range(3):
            d = self.operand()
            self.add(f"movabsq $imm64, {REG64[d]} #{i}",
                     rex(1, 0, 0, d) + bytes([0xB8 | d & 7]) + self.value().to_bytes(8, "little"))
        address = (DATA_BASE + 40).to_bytes(8, "little")
        for prefix, w, size in [(b"", 0, "b"), (b"\x66", 0, "w"), (b"", 0, "l"), (b"", 1, "q")]:
            opcode = 0xA0 if size == "b" else 0xA1
            self.add(f"movabs{size} moffs, accumulator",
                     prefix + rex(w, 0, 0, 0) + bytes([opcode]) + address, data=self.data())
            self.add(f"movabs{size} accumulator, moffs",
                     prefix + rex(w, 0, 0, 0) + bytes([opcode + 2]) + address, data=self.data())

    def extension_cases(self) -> None:
        """MOVZX and MOVSX at each destination size, MOVSXD without REX.W,
        CBW, CWD and their wider forms, and LEA at 16 and 32 bits."""
        for opcode, mnemonic in [(0xB6, "movzb"), (0xB7, "movzw"), (0xBE, "movsb"), (0xBF, "movsw")]:
            for prefix, w, size in [(b"\x66", 0, "w"), (b"", 0, "l"), (b"", 1, "q")]:
                if opcode in (0xB7, 0xBF) and size == "w":
                    continue
                d, s = self.operand(), self.operand()
                regs = self.regs()
                regs[s] = self.value() | 0x80
                self.add(f"{mnemonic}{size} r, r", prefix + reg_op(bytes([0x0F, opcode]), w, d, s),
                         regs)
                self.add(f"{mnemonic}{size} m, r",
                         mem_op(bytes([0x0F, opcode]), w, d, Address(RDI), prefix), self.at_data(),
                         data=self.data())
            if opcode in (0xB6, 0xBE):
                self.add(f"{mnemonic}l from a high byte", bytes([0x0F, opcode, 0xC0 | 2 << 3 | 5]))
        for prefix, mnemonic in [(b"", "movsxd r32"), (b"\x66", "movsxd r16")]:
            d, s = self.operand(), self.operand()
            self.add(f"{mnemonic}, r32", prefix + reg_op(b"\x63", 0, d, s))
            self.add(f"{mnemonic}, m32", mem_op(b"\x63", 0, d, Address(RDI), prefix),
                     self.at_data(), data=self.data())
        for code, name in [(b"\x66\x98", "cbtw"), (b"\x98", "cwtl"), (b"\x48\x98", "cltq"),
                           (b"\x66\x99", "cwtd"), (b"\x99", "cltd")]:
            for i in range(3):
                regs = self.regs()
                regs[RAX] = self.value() ^ (self.random.getrandbits(1) << 7 | 1 << 15) * i
                self.add(f"{name} #{i}", code, regs)
        for prefix, mnemonic in [(b"\x66", "leaw"), (b"", "leal")]:
            d = self.operand()
            self.add(f"{mnemonic} m, r", mem_op(b"\x8d", 0, d, Address(RSI, RCX, 3, -0x40), prefix))

    def sized_unary_cases(self) -> None:
        for digit, mnemonic, opcode8, opcode in [(2, "not", 0xF6, 0xF7), (3, "neg", 0xF6, 0xF7),
                                                 (0, "inc", 0xFE, 0xFF), (1, "dec", 0xFE, 0xFF)]:
            for high in (True, False):
                d = self.byte_reg(high)
                regs = self.regs()
                if high is False:
                    regs[d] = self.random.choice([0, 0x7F, 0x80, 0xFF]) | self.value() & ~0xFF
                self.add(f"{mnemonic}b r8 ({'no REX' if high else 'REX'})",
                         rex(0, 0, 0, d, not high) + bytes([opcode8, 0xC0 | digit << 3 | d & 7]), regs)
            d = self.operand()
            regs = self.regs()
            regs[d] = self.random.choice([0, 0x7FFF, 0x8000, 0xFFFF]) | self.value() & ~0xFFFF
            self.add(f"{mnemonic}w r16", b"\x66" + reg_op(bytes([opcode]), 0, digit, d), regs)
            self.add(f"{mnemonic}l r32", reg_op(bytes([opcode]), 0, digit, d))
            self.add(f"{mnemonic}q r64", reg_op(bytes([opcode]), 1, digit, d))
            for prefix, w, size, op in [(b"", 0, "b", opcode8), (b"\x66", 0, "w", opcode),
                                        (b"", 0, "l", opcode), (b"", 1, "q", opcode)]:
                self.add(f"{mnemonic}{size} m", mem_op(bytes([op]), w, digit, Address(RDI), prefix),
                         self.at_data(), data=self.data())

    def sized_shift_cases(self) -> None:
        """SHL, SHR and SAR at 8 and 16 bits: counts masked to 5 bits, past
        the width too, where SHL and SHR leave CF undefined."""
        r = self.random
        for digit, mnemonic in [(4, "shl"), (5, "shr"), (7, "sar")]:
            for prefix, size, bits, op8 in [(b"", "b", 8, True), (b"\x66", "w", 16, False)]:
                base = 0xC0 if op8 else 0xC1

                def undefined(count: int) -> int:
                    m = count & 31
                    if m == 0:
                        return 0
                    return (AF | (OF if m != 1 else 0)
                            | (CF if digit != 7 and m >= bits else 0))

                for count in (0, 1, 3, bits - 1, bits, bits + 1, 31, 32 + 2):
                    d = self.operand()
                    self.add(f"{mnemonic}{size} ${count}, r{bits}",
                             prefix + reg_op(bytes([base]), 0, digit, d, force_rex=op8) + bytes([count]),
                             undefined=undefined(count))
                d = self.operand()
                self.add(f"{mnemonic}{size} r{bits} (by 1)",
                         prefix + reg_op(bytes([base + 0x10]), 0, digit, d, force_rex=op8),
                         undefined=undefined(1))
                for count in (r.randrange(1, bits), bits + 2):
                    regs = self.regs()
                    regs[RCX] = r.getrandbits(56) << 8 | count
                    d = self.operand(avoid=(RSP, RCX))
                    self.add(f"{mnemonic}{size} %cl={count}, r{bits}",
                             prefix + reg_op(bytes([base + 0x12]), 0, digit, d, force_rex=op8), regs,
                             undefined=undefined(count))
            self.add(f"{mnemonic}w $3, m16",
                     mem_op(b"\xc1", 0, digit, Address(RDI), b"\x66") + b"\x03", self.at_data(),
                     data=self.data(), undefined=AF | OF)
        self.add("shlb $2, ah", b"\xc0\xe4\x02", undefined=AF | OF)

    def sized_rotate_cases(self) -> None:
        """ROL, ROR, RCL and RCR at every width; RCL and RCR rotate through
        CF, by the masked count modulo the width + 1."""
        r = self.random
        for digit, mnemonic in [(0, "rol"), (1, "ror"), (2, "rcl"), (3, "rcr")]:
            for prefix, w, size, bits in [(b"", 0, "b", 8), (b"\x66", 0, "w", 16),
                                          (b"", 0, "l", 32), (b"", 1, "q", 64)]:
                base = 0xC0 if bits == 8 else 0xC1

                def undefined(count: int) -> int:
                    return OF if count & (63 if bits == 64 else 31) > 1 else 0

                counts = (0, 1, 2, bits - 1, bits, bits + 1, 31) if digit >= 2 or bits < 32 \
                    else (1, bits + 1)
                for count in counts:
                    d = self.operand()
                    self.add(f"{mnemonic}{size} ${count}, r{bits}",
                             prefix + reg_op(bytes([base]), w, digit, d, force_rex=bits == 8)
                             + bytes([count]), undefined=undefined(count))
                d = self.operand()
                self.add(f"{mnemonic}{size} r{bits} (by 1)",
                         prefix + reg_op(bytes([base + 0x10]), w, digit, d, force_rex=bits == 8))
                count = r.getrandbits(8)
                regs = self.regs()
                regs[RCX] = r.getrandbits(56) << 8 | count
                d = self.operand(avoid=(RSP, RCX))
                self.add(f"{mnemonic}{size} %cl={count}, r{bits}",
                         prefix + reg_op(bytes([base + 0x12]), w, digit, d, force_rex=bits == 8),
                         regs, undefined=undefined(count))
            self.add(f"{mnemonic}w $5, m16",
                     mem_op(b"\xc1", 0, digit, Address(RDI), b"\x66") + b"\x05", self.at_data(),
                     data=self.data(), undefined=OF)
        self.add("rclb $1, ch", b"\xd0\xd5")

    def sized_mul_div_cases(self) -> None:
        """MUL and IMUL into AX, DX:AX and EDX:EAX, the two- and three-operand
        IMUL at each size, and DIV and IDIV at 8, 16 and 32 bits."""
        r = self.random
        mul_undefined = AF | SF | ZF | PF
        for digit, mnemonic in [(4, "mul"), (5, "imul")]:
            for high in (True, False):
                s = self.byte_reg(high)
                self.add(f"{mnemonic}b r8 ({'no REX' if high else 'REX'})",
                         rex(0, 0, 0, s, not high) + bytes([0xF6, 0xC0 | digit << 3 | s & 7]),
                         undefined=mul_undefined)
            for prefix, w, size in [(b"\x66", 0, "w"), (b"", 0, "l")]:
                for i in range(2):
                    s = self.operand()
                    self.add(f"{mnemonic}{size} {REG64[s]} #{i}", prefix + reg_op(b"\xf7", w, digit, s),
                             undefined=mul_undefined)
            self.add(f"{mnemonic}b m8", mem_op(b"\xf6", 0, digit, Address(RDI)), self.at_data(),
                     data=self.data(), undefined=mul_undefined)
        for prefix, w, size in [(b"\x66", 0, "w"), (b"", 0, "l"), (b"", 1, "q")]:
            d, s = self.operand(), self.operand()
            self.add(f"imul{size} r, r", prefix + reg_op(b"\x0f\xaf", w, d, s), undefined=mul_undefined)
            self.add(f"imul{size} m, r", mem_op(b"\x0f\xaf", w, d, Address(RDI), prefix),
                     self.at_data(), data=self.data(), undefined=mul_undefined)
            imm = r.getrandbits(16 if size == "w" else 32).to_bytes(2 if size == "w" else 4, "little")
            self.add(f"imul{size} $imm, r, r", prefix + reg_op(b"\x69", w, d, s) + imm,
                     undefined=mul_undefined)
            self.add(f"imul{size} $imm8, r, r", prefix + reg_op(b"\x6b", w, d, s)
                     + bytes([r.getrandbits(8)]), undefined=mul_undefined)
        # DIV and IDIV with quotients in range, out of range and a zero divisor.
        for digit, mnemonic, signed_ in [(6, "div", False), (7, "idiv", True)]:
            for prefix, w, size, bits in [(b"", 0, "b", 8), (b"\x66", 0, "w", 16),
                                          (b"", 0, "l", 32)]:
                for i, (q, rem, d) in enumerate([(None, None, None), (5, 2, 7), (1 << bits, 0, 3),
                                                 (3, 0, 0)]):
                    regs = self.regs()
                    s = self.operand(avoid=(RSP, RAX, RDX))
                    if d is None:
                        d = r.randrange(1, 1 << bits)
                        q, rem = r.randrange(0, 1 << bits - 1), r.randrange(0, d)
                    if signed_ and i == 1:
                        q, d = -q, d  # a negative quotient
                    dividend = (q * d + rem) & ((1 << 2 * bits) - 1)
                    regs[s] = r.getrandbits(64 - bits) << bits | d
                    if bits == 8:
                        regs[RAX] = r.getrandbits(48) << 16 | dividend
                        code = rex(0, 0, 0, s, True) + bytes([0xF6, 0xC0 | digit << 3 | s & 7])
                    else:
                        regs[RAX] = r.getrandbits(64 - bits) << bits | dividend & ((1 << bits) - 1)
                        regs[RDX] = r.getrandbits(64 - bits) << bits | dividend >> bits
                        code = prefix + reg_op(b"\xf7", w, digit, s)
                    self.add(f"{mnemonic}{size} {REG64[s]} #{i}", code, regs, undefined=FLAG_MASK)
            self.add(f"{mnemonic}l m32", mem_op(b"\xf7", 0, digit, Address(RDI)),
                     self.at_data(), data=bytes([0x10] * DATA_SIZE), undefined=FLAG_MASK)

    def sized_double_shift_cases(self) -> None:
        """SHLD and SHRD at 16 and 32 bits by an immediate and by CL; 16-bit
        counts above 16 are undefined and left out."""
        r = self.random
        for opcode, mnemonic in [(0xA4, "shld"), (0xAC, "shrd")]:
            for prefix, size, counts in [(b"\x66", "w", (0, 1, 5, 15, 16, 32 + 3)),
                                         (b"", "l", (0, 1, 5, 31, 32, 33))]:
                def undefined(count: int) -> int:
                    m = count & 31
                    return 0 if m == 0 else AF if m == 1 else AF | OF

                for count in counts:
                    d, s = self.operand(), self.operand()
                    self.add(f"{mnemonic}{size} ${count}, r, r",
                             prefix + reg_op(bytes([0x0F, opcode]), 0, s, d) + bytes([count]),
                             undefined=undefined(count))
                count = r.choice(counts)
                regs = self.regs()
                regs[RCX] = r.getrandbits(56) << 8 | count
                d, s = self.operand(avoid=(RSP, RCX)), self.operand(avoid=(RSP, RCX))
                self.add(f"{mnemonic}{size} %cl={count}, r, r",
                         prefix + reg_op(bytes([0x0F, opcode + 1]), 0, s, d), regs,
                         undefined=undefined(count))
                self.add(f"{mnemonic}{size} $3, r, m",
                         mem_op(bytes([0x0F, opcode]), 0, RAX, Address(RDI), prefix) + b"\x03",
                         self.at_data(), data=self.data(), undefined=AF | OF)
        for reg in (RAX, RSP, 9, 15):
            self.add(f"bswapl {REG32[reg]}", rex(0, 0, 0, reg) + bytes([0x0F, 0xC8 + (reg & 7)]))

    def exchange_cases(self) -> None:
        """XCHG, XADD, CMPXCHG at each size, CMPXCHG8B and CMPXCHG16B, each
        compare both equal and unequal."""
        r = self.random
        for high in (True, False):
            d, s = self.byte_reg(high), self.byte_reg(high)
            self.add(f"xchgb r8, r8 ({'no REX' if high else 'REX'})",
                     reg_op(b"\x86", 0, s, d, force_rex=not high))
            self.add(f"xaddb r8, r8 ({'no REX' if high else 'REX'})",
                     reg_op(b"\x0f\xc0", 0, s, d, force_rex=not high))
        for prefix, w, size in [(b"\x66", 0, "w"), (b"", 0, "l"), (b"", 1, "q")]:
            d, s = self.operand(), self.operand()
            self.add(f"xchg{size} r, r", prefix + reg_op(b"\x87", w, s, d))
            self.add(f"xchg{size} r, m", mem_op(b"\x87", w, s, Address(RDI), prefix),
                     self.at_data(), data=self.data())
            self.add(f"xadd{size} r, r", prefix + reg_op(b"\x0f\xc1", w, s, d))
            self.add(f"xadd{size} r, m", mem_op(b"\x0f\xc1", w, s, Address(RDI), prefix),
                     self.at_data(), data=self.data())
            for reg in (RCX, RSP, 8, 15):
                self.add(f"xchg{size} {REG64[reg]}, accumulator",
                         prefix + rex(w, 0, 0, reg) + bytes([0x90 + (reg & 7)]))
        self.add("xchgb r8, m8", mem_op(b"\x86", 0, 5, Address(RDI)), self.at_data(),
                 data=self.data())
        # The source register is the address register: the sum is stored
        # through the old address before the register takes the old value.
        self.add("xaddq %rdi, (%rdi)", mem_op(b"\x0f\xc1", 1, RDI, Address(RDI)),
                 self.at_data(), data=self.data())
        for prefix, w, size, bits, opcode in [(b"", 0, "b", 8, 0xB0), (b"\x66", 0, "w", 16, 0xB1),
                                              (b"", 0, "l", 32, 0xB1), (b"", 1, "q", 64, 0xB1)]:
            for equal in (True, False):
                regs = self.regs()
                d, s = self.operand(avoid=(RSP, RAX)), self.operand()
                if equal:
                    regs[RAX] = r.getrandbits(64 - bits) << bits | regs[d] & ((1 << bits) - 1) \
                        if bits < 64 else regs[d]
                    if bits == 32:
                        # QEMU writes EAX back on success, clearing RAX's upper
                        # half, where the SDM leaves the accumulator alone.
                        regs[RAX] &= M32
                self.add(f"cmpxchg{size} r, r ({'equal' if equal else 'unequal'})",
                         prefix + reg_op(bytes([0x0F, opcode]), w, s, d, force_rex=bits == 8), regs)
                regs = self.at_data()
                data = self.data()
                if equal:
                    regs[RAX] = int.from_bytes(data[64:72], "little")
                    if bits == 32:
                        regs[RAX] &= M32
                self.add(f"cmpxchg{size} r, m ({'equal' if equal else 'unequal'})",
                         mem_op(bytes([0x0F, opcode]), w, s, Address(RDI), prefix), regs, data=data)
        for w, name, width in [(0, "cmpxchg8b", 8), (1, "cmpxchg16b", 16)]:
            for equal in (True, False):
                regs = self.at_data()
                data = self.data()
                if equal:
                    half = width // 2
                    regs[RAX] = int.from_bytes(data[64:64 + half], "little")
                    regs[RDX] = int.from_bytes(data[64 + half:64 + width], "little")
                    if w == 0:
                        regs[RAX] |= r.getrandbits(32) << 32
                        regs[RDX] |= r.getrandbits(32) << 32
                self.add(f"{name} m ({'equal' if equal else 'unequal'})",
                         mem_op(b"\x0f\xc7", w, 1, Address(RDI)), regs, data=data)

    def bit_test_cases(self) -> None:
        """BT, BTS, BTR and BTC by a register and by an immediate, on
        registers and on memory, where a register offset reaches the bit
        string's other bytes; BSF and BSR of nonzero sources."""
        r = self.random
        bt_undefined = OF | SF | AF | PF
        for k, mnemonic in enumerate(["bt", "bts", "btr", "btc"]):
            opcode = 0xA3 + 8 * k
            for prefix, w, size, bits in [(b"\x66", 0, "w", 16), (b"", 0, "l", 32),
                                          (b"", 1, "q", 64)]:
                d, s = self.operand(), self.operand()
                self.add(f"{mnemonic}{size} r, r", prefix + reg_op(bytes([0x0F, opcode]), w, s, d),
                         undefined=bt_undefined)
                for offset in (r.randrange(-700, 700), -1, bits):
                    regs = self.at_data(offset=128)
                    s = self.operand(avoid=(RSP, RDI))
                    regs[s] = r.getrandbits(64 - bits) << bits | offset & ((1 << bits) - 1) \
                        if bits < 64 else offset & MASK64
                    self.add(f"{mnemonic}{size} r={offset}, m",
                             mem_op(bytes([0x0F, opcode]), w, s, Address(RDI), prefix), regs,
                             data=self.data(), undefined=bt_undefined)
                imm = r.getrandbits(8)
                self.add(f"{mnemonic}{size} ${imm}, r",
                         prefix + reg_op(b"\x0f\xba", w, 4 + k, d) + bytes([imm]),
                         undefined=bt_undefined)
                self.add(f"{mnemonic}{size} ${imm}, m",
                         mem_op(b"\x0f\xba", w, 4 + k, Address(RDI), prefix) + bytes([imm]),
                         self.at_data(), data=self.data(), undefined=bt_undefined)
        for opcode, mnemonic in [(0xBC, "bsf"), (0xBD, "bsr")]:
            for prefix, w, size, bits in [(b"\x66", 0, "w", 16), (b"", 0, "l", 32),
                                          (b"", 1, "q", 64)]:
                for value in (1, 1 << bits - 1, r.getrandbits(bits) | 1 << r.randrange(bits)):
                    regs = self.regs()
                    d, s = self.operand(), self.operand()
                    regs[s] = r.getrandbits(64 - bits) << bits | value if bits < 64 else value
                    self.add(f"{mnemonic}{size} {value:#x}",
                             prefix + reg_op(bytes([0x0F, opcode]), w, d, s), regs,
                             undefined=CF | OF | SF | AF | PF)
                data = bytes([r.getrandbits(8) | 1 for _ in range(DATA_SIZE)])
                self.add(f"{mnemonic}{size} m, r",
                         mem_op(bytes([0x0F, opcode]), w, RAX, Address(RDI), prefix),
                         self.at_data(), data=data, undefined=CF | OF | SF | AF | PF)
        for opcode, mnemonic in [(0xBC, "tzcnt"), (0xBD, "lzcnt"), (0xB8, "popcnt")]:
            undefined = 0 if mnemonic == "popcnt" else AF | OF | SF | PF
            for prefix, size in [(b"\x66\xf3", "w"), (b"\xf3", "l")]:
                for value in (0, 1, r.getrandbits(16)):
                    regs = self.regs()
                    d, s = self.operand(), self.operand()
                    regs[s] = self.value() & ~0xFFFF | value
                    self.add(f"{mnemonic}{size} {value:#x}",
                             prefix + reg_op(bytes([0x0F, opcode]), 0, d, s), regs,
                             undefined=undefined)
                self.add(f"{mnemonic}{size} m, r",
                         prefix + mem_op(bytes([0x0F, opcode]), 0, RDX, Address(RDI)),
                         self.at_data(), data=self.data(), undefined=undefined)

    def sized_extension_isa_cases(self) -> None:
        """CRC32 from 8-, 16- and 32-bit sources, MOVBE at 16 and 32 bits,
        ADCX and ADOX at 32 bits, and the BMI1 and BMI2 forms at 32 bits."""
        r = self.random
        for prefix, w, opcode, name in [(b"\xf2", 0, 0xF0, "crc32b from a high byte"),
                                        (b"\xf2", 1, 0xF0, "crc32b to a qword"),
                                        (b"\x66\xf2", 0, 0xF1, "crc32w"),
                                        (b"\xf2", 0, 0xF1, "crc32l")]:
            d = self.operand()
            s = r.randrange(4, 8) if "high" in name else self.operand()
            self.add(f"{name} r", prefix + reg_op(bytes([0x0F, 0x38, opcode]), w, d, s))
            self.add(f"{name} m", prefix + mem_op(bytes([0x0F, 0x38, opcode]), w, d & 7, Address(RDI)),
                     self.at_data(), data=self.data())
        for prefix, w, size in [(b"\x66", 0, "w"), (b"", 0, "l")]:
            d = self.operand(avoid=(RSP, RDI))
            self.add(f"movbe{size} m, r", mem_op(b"\x0f\x38\xf0", w, d, Address(RDI), prefix),
                     self.at_data(), data=self.data())
            self.add(f"movbe{size} r, m", mem_op(b"\x0f\x38\xf1", w, d, Address(RDI), prefix),
                     self.at_data(), data=self.data())
        for prefix, mnemonic in [(b"\x66", "adcxl"), (b"\xf3", "adoxl")]:
            for flags in (0, FLAG_MASK):
                d, s = self.operand(), self.operand()
                self.add(f"{mnemonic} r, r, flags {flags:#x}",
                         prefix + reg_op(b"\x0f\x38\xf6", 0, d, s), flags=flags)
            for w, size in [(0, "l"), (1, "q")]:
                self.add(f"{mnemonic[:4]}{size} m, r",
                         prefix + mem_op(b"\x0f\x38\xf6", w, RAX, Address(RDI)),
                         self.at_data(), data=self.data())
        for w in (0, 1):
            size = "q" if w else "l"
            d, a, b = self.operand(), self.operand(), self.operand()
            for name, mmmmm, pp, opcode, reg, v, undefined in [
                    ("andn", 2, 0, 0xF2, d, a, AF | PF),
                    ("bzhi", 2, 0, 0xF5, d, a, AF | PF),
                    ("pdep", 2, 3, 0xF5, d, a, 0),
                    ("pext", 2, 2, 0xF5, d, a, 0),
                    ("bextr", 2, 0, 0xF7, d, a, AF | PF | SF),
                    ("mulx", 2, 3, 0xF6, d, a, 0),
                    ("shlx", 2, 1, 0xF7, d, a, 0),
                    ("sarx", 2, 2, 0xF7, d, a, 0),
                    ("shrx", 2, 3, 0xF7, d, a, 0),
                    ("blsr", 2, 0, 0xF3, 1, d, AF | PF),
                    ("blsmsk", 2, 0, 0xF3, 2, d, AF | PF),
                    ("blsi", 2, 0, 0xF3, 3, d, AF | PF)]:
                if w == 0:
                    self.add(f"{name}{size} r", vex_reg(mmmmm, pp, w, opcode, reg, v, b),
                             undefined=undefined)
                self.add(f"{name}{size} m", vex_mem(mmmmm, pp, w, opcode, reg, v, Address(RDI)),
                         self.at_data(), data=self.data(), undefined=undefined)
            if w == 0:
                self.add("rorxl r", vex_reg(3, 3, 0, 0xF0, d, 0, b) + bytes([r.getrandbits(8)]))
            self.add(f"rorx{size} m", vex_mem(3, 3, w, 0xF0, d, 0, Address(RDI))
                     + bytes([r.getrandbits(8)]), self.at_data(), data=self.data())

    def sized_stack_cases(self) -> None:
        """PUSH and POP of words, memory and immediates, PUSHF and POPF, and
        LEAVE and ENTER at every nesting level the tests reach."""
        r = self.random
        for reg in (RAX, RSP, 12):
            self.add(f"pushw {REG16[reg]}", b"\x66" + rex(0, 0, 0, reg) + bytes([0x50 + (reg & 7)]),
                     stack_watch=16)
            self.add(f"popw {REG16[reg]}", b"\x66" + rex(0, 0, 0, reg) + bytes([0x58 + (reg & 7)]),
                     ret_addr=r.getrandbits(64), stack_watch=16)
        self.add("pushq with REX.W", b"\x48\x53", stack_watch=16)
        for prefix, size in [(b"", "q"), (b"\x66", "w")]:
            d = self.operand()
            self.add(f"push{size} r (FF /6)", prefix + reg_op(b"\xff", 0, 6, d), stack_watch=16)
            self.add(f"push{size} m", mem_op(b"\xff", 0, 6, Address(RDI), prefix), self.at_data(),
                     data=self.data(), stack_watch=16)
            self.add(f"pop{size} r (8F /0)", prefix + reg_op(b"\x8f", 0, 0, d),
                     ret_addr=r.getrandbits(64), stack_watch=16)
            self.add(f"pop{size} m", mem_op(b"\x8f", 0, 0, Address(RDI), prefix), self.at_data(),
                     data=self.data(), ret_addr=r.getrandbits(64), stack_watch=16)
        for imm in (0x7F, 0x80, r.getrandbits(8)):
            self.add(f"pushq ${imm:#x} (6A)", bytes([0x6A, imm]), stack_watch=16)
            self.add(f"pushw ${imm:#x} (66 6A)", bytes([0x66, 0x6A, imm]), stack_watch=16)
        imm = r.getrandbits(32)
        self.add(f"pushq ${imm:#x} (68)", b"\x68" + imm.to_bytes(4, "little"), stack_watch=16)
        self.add("pushw $imm16 (66 68)", b"\x66\x68" + imm.to_bytes(4, "little")[:2], stack_watch=16)
        for i in range(3):
            self.add(f"pushfq #{i}", b"\x9c", stack_watch=16)
        self.add("pushfw", b"\x66\x9c", stack_watch=16)
        # TF, NT, AC and ID stay clear: the model leaves them out.
        for i in range(4):
            value = r.getrandbits(64) & (FLAG_MASK | 1 << 10 | 1 << 9) | 2
            self.add(f"popfq {value:#x}", b"\x9d", ret_addr=value, stack_watch=16)
        self.add("popfw", b"\x66\x9d", ret_addr=r.getrandbits(64) & ~0xFFFF | FLAG_MASK | 2,
                 stack_watch=16)
        for prefix, size in [(b"", "q"), (b"\x66", "w"), (b"\x66\x48", "q (66 REX.W)"),
                             (b"\x2e\x66", "w (2E 66)")]:
            regs = self.regs()
            regs[RBP] = STACK_TOP - 0x20
            self.add(f"leave{size}", prefix + b"\xc9", regs, stack_watch=64)
        for size, level, prefix in [(0x20, 0, b""), (0x18, 1, b""), (0x08, 2, b""), (0, 3, b""),
                                    (0x10, 0, b"\x66"), (0x10, 1, b"\x66"), (0x10, 0x21, b"")]:
            regs = self.regs()
            regs[RBP] = STACK_TOP - 0x20
            self.add(f"enter ${size:#x}, ${level}{' (66)' if prefix else ''}",
                     prefix + b"\xc8" + size.to_bytes(2, "little") + bytes([level]), regs,
                     stack_watch=128)

    def flag_cases(self) -> None:
        for code, name in [(b"\x9f", "lahf"), (b"\x9e", "sahf"), (b"\xf8", "clc"), (b"\xf9", "stc"),
                           (b"\xf5", "cmc"), (b"\xfc", "cld"), (b"\xfd", "std")]:
            for i in range(2):
                self.add(f"{name} #{i}", code)

    def control_cases(self) -> None:
        """CALL and JMP through registers and memory, LOOP, LOOPE, LOOPNE
        and JRCXZ, RET imm16, and XLAT."""
        r = self.random
        target = CODE_BASE + 0x40
        regs = self.regs()
        d = self.operand(avoid=(RSP,))
        regs[d] = target
        self.add(f"callq *{REG64[d]}", reg_op(b"\xff", 0, 2, d), regs, stack_watch=16)
        data = target.to_bytes(8, "little") * (DATA_SIZE // 8)
        for digit, name in [(2, "callq"), (4, "jmpq")]:
            self.add(f"{name} *m", mem_op(b"\xff", 0, digit, Address(RDI)), self.at_data(), data=data,
                     stack_watch=16)
        for opcode, name in [(0xE2, "loop"), (0xE1, "loope"), (0xE0, "loopne"), (0xE3, "jrcxz")]:
            for count in (0, 1, 2):
                for zf in (0, ZF):
                    regs = self.regs()
                    regs[RCX] = count
                    self.add(f"{name} rcx={count} zf={zf >> 6}", bytes([opcode, r.choice([-20, 4, 30]) & 0xFF]),
                             regs, flags=self.flags() & ~ZF | zf)
        for disp in (0x200, -0x80):
            self.add(f"jmp rel32 {disp:+}", rel32(b"\xe9", disp))
        for imm in (0, 8, 0x100):
            self.add(f"retq ${imm:#x}", b"\xc2" + imm.to_bytes(2, "little"),
                     ret_addr=CODE_BASE + r.randrange(0, 0x200, 3), stack_watch=16)
        for i in range(3):
            regs = self.regs()
            regs[RBX] = DATA_BASE
            regs[RAX] = self.value() & ~0xFF | r.randrange(DATA_SIZE)
            self.add(f"xlatb #{i}", b"\xd7", regs, data=self.data())

    def string_cases(self) -> None:
        """MOVS, CMPS, STOS, LODS and SCAS at each size, alone, with REP,
        REPE and REPNE prefixes, and backwards with DF set."""
        r = self.random
        for opcode, name in [(0xA4, "movs"), (0xA6, "cmps"), (0xAA, "stos"), (0xAC, "lods"),
                             (0xAE, "scas")]:
            compares = name in ("cmps", "scas")
            for prefix, w, size, width in [(b"", 0, "b", 1), (b"\x66", 0, "w", 2),
                                           (b"", 0, "l", 4), (b"", 1, "q", 8)]:
                op = prefix + rex(w, 0, 0, 0) + bytes([opcode + (width > 1)])
                for rep, count in [(b"", None), (b"\xf3", 0), (b"\xf3", 3), (b"\xf2", 3)]:
                    for backwards in ((False, True) if rep == b"\xf3" and count else (False,)):
                        data = bytearray(self.data())
                        data[160:200] = data[40:80]  # matching runs for CMPS
                        data[r.randrange(40, 80) + 120] ^= 0x5A
                        regs = self.regs()
                        regs[RSI] = DATA_BASE + (64 if backwards else 40)
                        regs[RDI] = DATA_BASE + (184 if backwards else 160)
                        if count is not None:
                            regs[RCX] = count
                        if name == "scas":
                            regs[RAX] = int.from_bytes(data[160:168], "little")
                        code = rep + op
                        label = f"{(rep.hex() + ' ') if rep else ''}{name}{size}"
                        if backwards:
                            self.add(f"std; {label}; cld", b"\xfd" + code + b"\xfc", regs,
                                     data=bytes(data), single=False)
                        else:
                            self.add(f"{label} rcx={count}", code, regs, data=bytes(data))
        regs = self.regs()
        regs[RSI], regs[RDI], regs[RCX] = DATA_BASE, DATA_BASE + 16, 5
        self.add("rep movsq overlapping forwards", b"\xf3\x48\xa5", regs, data=self.data())

    def prefix_cases(self) -> None:
        """Null segment prefixes, repeat prefixes the opcode ignores, REX
        prefixes on forms without register fields, and the NOP forms."""
        load = mem_op(b"\x8b", 0, RAX, Address(RDI))
        for segment in (b"\x2e", b"\x3e", b"\x26", b"\x36"):
            self.add(f"{segment.hex()} movl m32, r32", segment + load, self.at_data(),
                     data=self.data())
        self.add("66 2e movw r16, m16", b"\x66\x2e" + mem_op(b"\x89", 0, RCX, Address(RDI)),
                 self.at_data(), data=self.data())
        for rep in (b"\xf2", b"\xf3"):
            self.add(f"{rep.hex()} addl r32, r32", rep + reg_op(b"\x01", 0, RCX, RAX))
        self.add("REX ret", b"\x48\xc3", ret_addr=CODE_BASE + 0x30)
        self.add("REX call rel32", b"\x48" + rel32(b"\xe8", 0x20), stack_watch=16)
        self.add("REX jne rel8", b"\x40\x75\x10")
        self.add("jmpq *%rax with REX.R", b"\x44\xff\xe0",
                 [CODE_BASE + 0x40 if i == RAX else v for i, v in enumerate(self.regs())])
        # A REX byte counts only right before the opcode.
        self.add("REX.W before 66: movb %ah, %al", bytes.fromhex("486688e0"))
        self.add("two REX bytes: movq %rcx, %rax", bytes.fromhex("414889c8"))
        self.add("REX before the mandatory prefix: pxor", bytes.fromhex("41660fefc1"))
        self.add("REX before 66: nopw", bytes.fromhex("48660f1f00"))
        for nop in ["f390", "0f1fc0", "0f1f08", "0f1f0500000000", "0f1f042500000000", "66f20f1f00",
                    "f30f1efa", "4890", "f30f1efb", "0f1820", "0f1838"]:
            self.add(f"nop {nop}", bytes.fromhex(nop))
        # VEX.R is ignored where ModRM.reg is an opcode extension, and so is
        # ModRM.reg in SETcc. (ADOX with a 66 prefix too is ADOX, but QEMU
        # runs it as ADCX, so it has no case here.)
        self.add("blsr with VEX.R set", bytes.fromhex("c462f0f3c8"))
        self.add("setb with ModRM.reg 3", bytes.fromhex("0f92d8"))


def exec_cases() -> list[ExecCase]:
    return CaseBuilder(seed=8469).build()
