#!/usr/bin/env python3
"""Measure x86-hol's decoder against Intel XED and llvm-objdump.

The inventory is every instruction form (XED iform) reached by a sweep of
the 64-bit encoding space: each opcode of the one-byte, 0F, 0F 38 and
0F 3A maps, under sets of legacy prefixes and REX bytes, followed by all
256 values of the next byte (ModRM for most opcodes) and seeded random
bytes; and the VEX opcode space under a sample of VEX prefixes, bare and
after a few legacy prefix and REX byte orders. XED
decodes the words for a Sapphire Rapids chip, so hint encodings that
chip defines (CLDEMOTE, RDSSP) are those instructions and not NOPs.

Each iform is put in a tier by its XED ISA set and instruction class:

  1    64-bit user-mode integer: x86-64-v2 without SSE, plus BMI1, BMI2,
       ADX, MOVBE and CRC32, and the NOP, PAUSE and ENDBR64 hints
  2    128-bit SSE to SSE4.2, AES and PCLMULQDQ
  3    256-bit AVX, AVX2 and FMA; LOCK forms, fences, FS/GS base, SYSCALL
  out  system and I/O, x87 and MMX, AVX-512, and everything newer

Words with a LOCK, FS or GS segment, or 67 address-size prefix are
reported in rows of their own and do not count towards their iform, as are
VEX words after a REX, 66, F2 or F3 byte, which the SDM makes #UD (XED
reads some of them, such as 40 2E C4 ..., as the VEX instruction).

Up to --samples words per tier-1 iform (an eighth of that per other iform
and per prefix row), drawn from distinct prefix, REX and ModRM.mod
groups, are decoded by `decode` in HOL4 (`cv_eval`, through `holbuild
run`) and disassembled by llvm-objdump, as is a random sample of words
XED rejects. A word XED reads is in scope unless it is a near branch
with a 66 prefix, which Intel and AMD CPUs execute differently. An iform
is covered when HOL4 decodes every in-scope sample at XED's length as an
instruction the iform's class allows (the HOL_FORMS table). A word HOL4 decodes is a mismatch when
either reference rejects it or reads another length, when XED reads an
instruction class the decoded instruction does not allow, or when it is a
66-prefixed near branch. A word XED and HOL4 read alike, at XED's length
and as an allowed class, is instead a reference disagreement when only
llvm-objdump rejects it or reads another length: llvm-objdump rejects some
legacy prefix orders the SDM allows (a segment prefix after 66) and splits
off F2 and F3 as XACQUIRE and XRELEASE.

XED is fetched at a pinned commit and built into a cache directory unless
--xed names an installed XED kit; llvm-objcopy and llvm-objdump come from
PATH or --llvm.

Usage: x86_coverage.py [--xed DIR] [--llvm DIR] [--samples N] [--json FILE]
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

XED_COMMIT = "0bcb6237345c5066726dcc08b3d87928df3b5b26"
MBUILD_COMMIT = "1b437e409221a2b5703b4d8896baa20d43e4ba1a"
REPO = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Tiers.

TIER1_ISA_SETS = {"I86", "I186", "I386", "I486REAL", "LONGMODE", "CMOV", "CMPXCHG16B",
                  "PENTIUMREAL", "LAHF", "POPCNT", "LZCNT", "BMI1", "BMI2", "ADOX_ADCX",
                  "MOVBE", "FAT_NOP", "PPRO", "PREFETCH_NOP", "PAUSE"}
TIER2_ISA_SETS = {"SSE", "SSE2", "SSE3", "SSSE3", "SSE4", "SSE42", "AES", "PCLMULQDQ",
                  "SSEMXCSR", "SSE_PREFETCH"}
TIER3_ISA_SETS = {"AVX", "AVX2", "AVX2GATHER", "FMA", "F16C", "AVXAES", "RDWRFSGS"}

# Classes placed by name, before the ISA set is consulted; CRC32 is tier 1 in
# its SSE4.2 forms only (TIER1_FORMS).
TIER1_FORMS = {("CRC32", "SSE42")}
CLASS_TIERS = {
    "ENDBR64": "1",
    "LFENCE": "3", "MFENCE": "3", "SFENCE": "3", "SYSCALL": "3",
}

# Classes of the tier-1 ISA sets that are outside tier 1, with the reason.
EXCLUDED = {
    "privileged": "CLI STI HLT RDMSR WRMSR INVD INVLPG WBINVD MOV_CR MOV_DR SWAPGS "
                  "SYSRET SYSRET64 IRET IRETD IRETQ",
    "I/O": "IN OUT INSB INSW INSD OUTSB OUTSW OUTSD REP_INSB REP_INSW REP_INSD "
           "REP_OUTSB REP_OUTSW REP_OUTSD",
    "raises an exception by design": "INT INT1 INT3 INTO UD0 UD1 UD2 UDB",
    "reads processor identity or time": "CPUID RDTSC",
    "far transfer or segment load": "CALL_FAR JMP_FAR RET_FAR LDS LES LFS LGS LSS",
    "invalid in 64-bit mode": "AAA AAD AAM AAS DAA DAS SALC BOUND PUSHA PUSHAD POPA POPAD",
    "cache hint": "PREFETCHW PREFETCH_EXCLUSIVE PREFETCH_RESERVED",
}
EXCLUDED_CLASSES = {c: why for why, names in EXCLUDED.items() for c in names.split()}
# Opcode digits the SDM leaves undocumented that CPUs run as SHL and TEST.
UNDOCUMENTED_ALIASES = {("SHL", "r6"), ("TEST", "r1")}
SEGMENT_IFORMS = {"MOV_GPRv_SEG", "MOV_MEMw_SEG", "MOV_SEG_GPR16", "MOV_SEG_MEMw",
                  "POP_DS", "POP_ES", "POP_FS", "POP_GS", "POP_SS",
                  "PUSH_CS", "PUSH_DS", "PUSH_ES", "PUSH_FS", "PUSH_GS", "PUSH_SS"}


def tier_of(iform: str, iclass: str, isa_set: str, category: str) -> tuple[str, str]:
    """The tier of an iform, and why it is outside tier 1 if a tier-1 set has it."""
    if category == "MMX":
        return "out", "MMX"
    if (iclass, isa_set) in TIER1_FORMS:
        return "1", ""
    if iclass in CLASS_TIERS:
        return CLASS_TIERS[iclass], ""
    if iclass.endswith("_LOCK"):
        return "3", "LOCK form"
    if isa_set in TIER1_ISA_SETS:
        if iform in SEGMENT_IFORMS:
            return "out", "segment register"
        if (iclass, iform[-2:]) in UNDOCUMENTED_ALIASES:
            return "out", "undocumented alias"
        if iclass in EXCLUDED_CLASSES:
            return "out", EXCLUDED_CLASSES[iclass]
        return "1", ""
    if isa_set in TIER2_ISA_SETS:
        return "2", ""
    if isa_set in TIER3_ISA_SETS:
        return "3", ""
    return "out", ""


# ---------------------------------------------------------------------------
# What each HOL instruction may be. A key is the constructor, followed by
# its first argument for the constructors in KEYED, and for StringOp its
# width and repeat mode too.

CONDITIONS = ["O", "NO", "B", "NB", "Z", "NZ", "BE", "NBE", "S", "NS", "P", "NP",
              "L", "NL", "LE", "NLE"]
BINOPS = ["ADD", "OR", "ADC", "SBB", "AND", "SUB", "XOR", "CMP", "TEST"]
PBINOPS = ["PXOR", "PADDD", "PADDQ", "PAND", "POR", "PCMPEQB", "PMULLD", "PMINUD", "PMAXUD",
           "PSUBD", "PSUBQ", "PABSD", "PHADDD", "PCMPGTQ", "PMULUDQ", "PMULDQ", "PMINSD",
           "PMAXSD", "PACKUSDW", "PACKSSDW", "PMADDWD", "PMADDUBSW", "PACKUSWB", "PSADBW",
           "PAVGB", "PAVGW", "PADDUSB", "PSUBUSB", "PHMINPOSUW"]
BT_OPS = ["BT", "BTS", "BTR", "BTC"]
FLAG_OPS = ["CLC", "STC", "CMC", "CLD", "STD"]
LOOPS = ["LOOP", "LOOPE", "LOOPNE", "JRCXZ"]
STRING_OPS = ["MOVS", "CMPS", "STOS", "LODS", "SCAS"]
KEYED = {"Binop", "BinopImm", "Shift", "Rotate", "MulWide", "Div", "ShiftDouble", "Adx",
         "BitCount", "ShiftX", "Bls", "Pdep", "Jcc", "Cmov", "Setcc", "Pbinop", "Pcmpd",
         "Pshufw", "Pshift", "Pshiftdq", "AesRound", "Movx", "Bt", "BtImm", "BitScan",
         "Cmpxchg2", "FlagOp", "Loop"}

HOL_FORMS: dict[str, set[str]] = {
    "MovImm": {"MOV"}, "Mov": {"MOV"}, "Movx T": {"MOVSX", "MOVSXD"}, "Movx F": {"MOVZX"},
    "Cbw": {"CBW", "CWDE", "CDQE"}, "Cwd": {"CWD", "CDQ", "CQO"}, "Lea": {"LEA"},
    "Not": {"NOT"}, "Neg": {"NEG"}, "Inc": {"INC"}, "Dec": {"DEC"},
    "Shift SHL": {"SHL"}, "Shift SHR": {"SHR"}, "Shift SAR": {"SAR"},
    "Rotate ROL": {"ROL"}, "Rotate ROR": {"ROR"}, "Rotate RCL": {"RCL"},
    "Rotate RCR": {"RCR"}, "Imul": {"IMUL"},
    "MulWide T": {"IMUL"}, "MulWide F": {"MUL"}, "Div T": {"IDIV"}, "Div F": {"DIV"},
    "ShiftDouble T": {"SHLD"}, "ShiftDouble F": {"SHRD"}, "Bswap": {"BSWAP"},
    "Adx F": {"ADCX"}, "Adx T": {"ADOX"}, "Movbe": {"MOVBE"},
    "Crc32": {"CRC32"}, "BitCount TZCNT": {"TZCNT"}, "BitCount LZCNT": {"LZCNT"},
    "BitCount POPCNT": {"POPCNT"}, "Mulx": {"MULX"}, "Rorx": {"RORX"},
    "ShiftX SHL": {"SHLX"}, "ShiftX SHR": {"SHRX"}, "ShiftX SAR": {"SARX"},
    "Andn": {"ANDN"}, "Bzhi": {"BZHI"}, "Bls BLSR": {"BLSR"}, "Bls BLSI": {"BLSI"},
    "Bls BLSMSK": {"BLSMSK"}, "Pdep PDEP": {"PDEP"}, "Pdep PEXT": {"PEXT"},
    "Bextr": {"BEXTR"}, "Push": {"PUSH"}, "PushImm": {"PUSH"}, "Pop": {"POP"},
    "Pushf": {"PUSHF", "PUSHFQ"}, "Popf": {"POPF", "POPFQ"}, "Lahf": {"LAHF"},
    "Sahf": {"SAHF"}, "Call": {"CALL_NEAR"}, "CallInd": {"CALL_NEAR"}, "Jmp": {"JMP"},
    "JmpInd": {"JMP"}, "Ret": {"RET_NEAR"}, "Leave": {"LEAVE"}, "Enter": {"ENTER"},
    "Xchg": {"XCHG"}, "Xadd": {"XADD"}, "Cmpxchg": {"CMPXCHG"},
    "Cmpxchg2 F": {"CMPXCHG8B"}, "Cmpxchg2 T": {"CMPXCHG16B"}, "BitScan F": {"BSF"},
    "BitScan T": {"BSR"}, "Xlat": {"XLAT"},
    "Nop": {"NOP", "PAUSE", "ENDBR64", "ENDBR32"},
    "VecLoad": {"MOVUPS", "MOVDQU", "MOVDQA"}, "VecStore": {"MOVUPS", "MOVDQU"},
    "VecMov": {"MOVDQA"}, "Pblendvb": {"PBLENDVB"}, "Pcmpd T": {"PCMPGTD"},
    "Pcmpd F": {"PCMPEQD"},
    "Pwiden": {"PMOVSXBD", "PMOVZXBD", "PMOVSXDQ", "PMOVZXDQ", "PMOVSXBW", "PMOVZXBW"},
    "Ptest": {"PTEST"}, "Pshufd": {"PSHUFD"}, "Pshufw T": {"PSHUFHW"},
    "Pshufw F": {"PSHUFLW"}, "Pshufb": {"PSHUFB"}, "Pshift T": {"PSLLD", "PSLLQ"},
    "Pshift F": {"PSRLD", "PSRLQ"}, "Psrad": {"PSRAD"}, "Pshiftdq T": {"PSLLDQ"},
    "Pshiftdq F": {"PSRLDQ"}, "PxorMem": {"PXOR"},
    "AesRound AESENC": {"AESENC"}, "AesRound AESENCLAST": {"AESENCLAST"},
    "AesRound AESDEC": {"AESDEC"}, "AesRound AESDECLAST": {"AESDECLAST"}, "AesImc": {"AESIMC"},
    "Pclmul": {"PCLMULQDQ"}, "AesKeygen": {"AESKEYGENASSIST"}, "Palignr": {"PALIGNR"},
    "Pinsrq": {"PINSRQ"}, "Pextrq": {"PEXTRQ"}, "Punpcklqdq": {"PUNPCKLQDQ"},
    "Pmovmskb": {"PMOVMSKB"}, "Movd": {"MOVD", "MOVQ"}, "MovqXmm": {"MOVQ"},
    "Pinsrd": {"PINSRD"}, "Pextrd": {"PEXTRD"}, "MovdXmm": {"MOVD"},
    # Constructors the decoder had before tier 1, for measuring older commits.
    "MovImm64": {"MOV"}, "Movzx": {"MOVZX"}, "Movsx": {"MOVSX"}, "Movsxd": {"MOVSXD"},
    "Cdqe": {"CDQE"}, "Cqo": {"CQO"}, "Dec64": {"DEC"}, "MovbeLoad": {"MOVBE"},
    "MovbeStore": {"MOVBE"}, "JmpReg": {"JMP"}, "Rotate T": {"ROL"}, "Rotate F": {"ROR"},
}
for _b in BINOPS:
    HOL_FORMS[f"Binop {_b}"] = HOL_FORMS[f"BinopImm {_b}"] = {_b}
for _n, _c in enumerate(CONDITIONS):
    HOL_FORMS[f"Jcc {_n}w"] = {f"J{_c}"}
    HOL_FORMS[f"Cmov {_n}w"] = {f"CMOV{_c}"}
    HOL_FORMS[f"Setcc {_n}w"] = {f"SET{_c}"}
for _o in BT_OPS:
    HOL_FORMS[f"Bt {_o}"] = HOL_FORMS[f"BtImm {_o}"] = {_o}
for _o in FLAG_OPS:
    HOL_FORMS[f"FlagOp {_o}"] = {_o}
for _o in LOOPS:
    HOL_FORMS[f"Loop {_o}"] = {_o}
for _o in STRING_OPS:
    for _size, _w in zip(("S8", "S16", "S32", "S64"), "BWDQ"):
        for _rep, _r in (("NoRep", ""), ("RepE", "REP_" if _o in ("MOVS", "STOS", "LODS")
                                         else "REPE_"), ("RepNE", "REPNE_")):
            HOL_FORMS[f"StringOp {_o} {_size} {_rep}"] = {f"{_r}{_o}{_w}"}
for _p in PBINOPS:
    HOL_FORMS[f"Pbinop {_p}"] = {_p} | ({"XORPS"} if _p == "PXOR" else set())


def hol_key(instruction: str) -> str:
    words = instruction.split()
    if words[0] == "StringOp":  # the width and repeat mode name XED's class
        return " ".join(words[:4])
    return " ".join(words[:2]) if words[0] in KEYED else words[0]


# ---------------------------------------------------------------------------
# The encoding space.

ESCAPES = {0x0F, 0xC4, 0xC5}
LEGACY = {0x66, 0x67, 0xF2, 0xF3, 0xF0, 0x2E, 0x3E, 0x26, 0x36, 0x64, 0x65}
# Every order of at most one each of 66, F2 or F3, and a null segment
# override; the prefixes of the rows below are swept alone.
PREFIX_SETS = [list(order)
               for choice in itertools.product([None, 0x66], [None, 0xF2, 0xF3],
                                               [None, 0x2E, 0x3E, 0x26, 0x36])
               for order in itertools.permutations(b for b in choice if b is not None)]
PREFIX_SETS += [[0xF0], [0x64], [0x65], [0x67]]
REXES = [None, *range(0x40, 0x50)]
# A word's row: the prefixes that keep it from counting towards its iform.
ROWS = {0xF0: "LOCK", 0x64: "FS/GS segment", 0x65: "FS/GS segment", 0x67: "address size"}
BEFORE_VEX = "REX, 66, F2 or F3 before VEX"
# Prefix orders swept before VEX words: segment prefixes are allowed there,
# REX, 66, F2 and F3 make the word #UD.
VEX_PREFIXES = [[0x2E], [0x40], [0x48], [0x66], [0xF2], [0xF3], [0x40, 0x2E], [0x2E, 0x40],
                [0x2E, 0x66]]


def heads() -> list[bytes]:
    """Every encoding up to the byte the sweep varies (ModRM for most opcodes)."""
    out = []
    for prefixes in PREFIX_SETS:
        for rex in REXES:
            pre = bytes(prefixes + ([rex] if rex is not None else []))
            for op in range(256):
                if op not in LEGACY and op not in ESCAPES and op & 0xF0 != 0x40:
                    out.append(pre + bytes([op]))
            for escape in (b"\x0f", b"\x0f\x38", b"\x0f\x3a"):
                for op in range(256):
                    if escape != b"\x0f" or op not in (0x38, 0x3A):
                        out.append(pre + escape + bytes([op]))
    for prefixes in VEX_PREFIXES:
        for pp in range(4):
            for op in range(256):
                for mmmmm in (2, 3):
                    for w in (0, 1):
                        out.append(bytes(prefixes + [0xC4, 0xE0 | mmmmm, w << 7 | 0xF << 3 | pp,
                                                     op]))
    for rxb in range(8):
        for vvvv in (0xF, 0x0, 0x5):
            for length in (0, 1):
                for pp in range(4):
                    for op in range(256):
                        if rxb in (7, 0):  # C5 has only VEX.R
                            out.append(bytes([0xC5, rxb >> 2 << 7 | vvvv << 3 | length << 2 | pp,
                                              op]))
                        for mmmmm in (1, 2, 3):
                            for w in (0, 1):
                                out.append(bytes([0xC4, rxb << 5 | mmmmm,
                                                  w << 7 | vvvv << 3 | length << 2 | pp, op]))
    return out


def row_of(word: bytes) -> str:
    for i, b in enumerate(word):
        if b in ROWS:
            return ROWS[b]
        if b in (0xC4, 0xC5):
            return BEFORE_VEX if any(p in (0x66, 0xF2, 0xF3) or p & 0xF0 == 0x40
                                     for p in word[:i]) else ""
        if b not in LEGACY and b & 0xF0 != 0x40:
            return ""
    return ""


# Intel ignores a 66 prefix on near branches in 64-bit mode; AMD truncates
# the target to 16 bits.
NEAR_BRANCHES = {"JMP", "CALL_NEAR", "RET_NEAR", "JRCXZ", "LOOP", "LOOPE", "LOOPNE"} | {
    f"J{c}" for c in CONDITIONS}


def vendor_defined(iclass: str, word: bytes) -> bool:
    """Whether Intel and AMD CPUs execute the word differently."""
    prefixes = word[:next(i for i, b in enumerate(word) if b not in LEGACY)]
    return iclass in NEAR_BRANCHES and 0x66 in prefixes


# ---------------------------------------------------------------------------
# XED.

def xed_kit(cache: Path) -> Path:
    """An installed XED kit at XED_COMMIT, built into cache on first use."""
    kit = cache / f"xed-{XED_COMMIT[:12]}"
    if (kit / "lib" / "libxed.a").exists():
        return kit
    src = Path(tempfile.mkdtemp(prefix="xed-src-", dir=cache))
    for name, commit in (("xed", XED_COMMIT), ("mbuild", MBUILD_COMMIT)):
        repo = src / name
        repo.mkdir()
        for cmd in (["init", "-q"], ["fetch", "-q", "--depth", "1",
                                     f"https://github.com/intelxed/{name}.git", commit],
                    ["checkout", "-q", "FETCH_HEAD"]):
            subprocess.run(["git", "-C", str(repo), *cmd], check=True)
    # Install beside the kit and rename it into place, so that an interrupted
    # or concurrent install never leaves a partial kit at its path.
    staged = Path(tempfile.mkdtemp(prefix="xed-kit-", dir=cache))
    subprocess.run([sys.executable, "mfile.py", f"--jobs={os.cpu_count() or 4}", "--static",
                    f"--install-dir={staged}", "install"], cwd=src / "xed", check=True,
                   stdout=subprocess.DEVNULL)
    shutil.rmtree(src)
    try:
        staged.rename(kit)
    except OSError:
        if not (kit / "lib" / "libxed.a").exists():
            raise
        shutil.rmtree(staged)  # another run installed the kit first
    return kit


def build_probe(kit: Path, out: Path) -> Path:
    probe = out / "xed_probe"
    subprocess.run(["cc", "-O2", f"-I{kit / 'include'}", "-o", str(probe),
                    str(REPO / "tools" / "xed_probe.c"), str(kit / "lib" / "libxed.a")],
                   check=True)
    return probe


@dataclass
class Iform:
    name: str
    iclass: str
    isa_set: str
    tier: str
    why: str
    words: int = 0
    groups: dict[tuple, list[bytes]] = field(default_factory=dict)
    seen: Counter = field(default_factory=Counter)


GROUP_SAMPLES = 4


def sweep(probe: Path, rng: random.Random, iforms: dict[str, Iform]) -> None:
    """Decode the encoding space, keeping a few words per (iform, row, group)."""
    hs = heads()
    tails = [rng.randbytes(14) for _ in hs]
    text = "".join(f"{h.hex()} {t.hex()}\n" for h, t in zip(hs, tails))
    with tempfile.TemporaryFile("w+") as feed:
        feed.write(text)
        feed.seek(0)
        with subprocess.Popen([str(probe), "sweep"], stdin=feed, stdout=subprocess.PIPE,
                              text=True) as proc:
            for line in proc.stdout:
                index, byte, length, name = line.split()
                head = hs[int(index)]
                if int(length) <= len(head) and byte != "00":
                    continue  # the same word as with byte 00
                word = (head + bytes([int(byte, 16)]) + tails[int(index)])[:int(length)]
                iform = iforms[name]
                row = row_of(word)
                iform.words += not row
                group = (row, head[:-1], int(byte, 16) >> 6)
                n = iform.seen[group]
                iform.seen[group] += 1
                kept = iform.groups.setdefault(group, [])
                if len(kept) < GROUP_SAMPLES:
                    kept.append(word)
                elif (k := rng.randrange(n + 1)) < GROUP_SAMPLES:
                    kept[k] = word
    if proc.returncode != 0:
        raise SystemExit(f"xed_probe sweep exited with {proc.returncode}")


def samples(iform: Iform, row: str, count: int, rng: random.Random) -> list[bytes]:
    """Up to count words of iform in row, one group at a time."""
    pools = [list(words) for group, words in iform.groups.items() if group[0] == row]
    rng.shuffle(pools)
    out: list[bytes] = []
    while pools and len(out) < count:
        out += [pool.pop() for pool in pools[:count - len(out)]]
        pools = [pool for pool in pools if pool]
    return out


def rejected_words(probe: Path, rng: random.Random, count: int) -> list[bytes]:
    """Up to count random words of the swept space that XED rejects."""
    hs = heads()
    candidates = [(rng.choice(hs) + rng.randbytes(15))[:15] for _ in range(8 * count)]
    run = subprocess.run([str(probe), "decode"], input="".join(w.hex() + "\n" for w in candidates),
                         capture_output=True, text=True, check=True)
    verdicts = run.stdout.splitlines()
    return [w for w, v in zip(candidates, verdicts) if v.startswith("- ")][:count]


# ---------------------------------------------------------------------------
# HOL4 and llvm-objdump.

HOL_SCRIPT = r"""
val _ = app load ["x86IsaCvTheory", "cv_transLib", "wordsLib"];
open HolKernel boolLib bossLib wordsLib x86IsaTheory x86IsaCvTheory cv_transLib;
val _ = new_theory "x86_coverage";
(* Words arrive as numbers, least significant byte first: cv_eval reads
   numerals faster than byte lists. *)
Definition word_bytes_def:
  word_bytes 0 (n:num) = [] : word8 list ∧
  word_bytes (SUC k) n = n2w (n MOD 256) :: word_bytes k (n DIV 256)
End
Definition x86_decodes_def:
  x86_decodes [] = [] ∧
  x86_decodes (n::ns) = decode (word_bytes 15 n) :: x86_decodes ns
End
val _ = cv_trans word_bytes_def;
val _ = cv_trans x86_decodes_def;
val _ = Globals.linewidth := 1000000;
val words = map (fn s => numSyntax.mk_numeral (Arbnum.fromString s))
  (String.tokens Char.isSpace (TextIO.inputAll (TextIO.openIn "WORDS")));
val out = TextIO.openOut "RESULT";
fun show t =
  case strip_comb t of
    (_, [i, n]) => Int.toString (numSyntax.int_of_term n) ^ " " ^ term_to_string i
  | (c, _) => fst (dest_const c);
fun chunks [] = ()
  | chunks ws =
      let val (now, later) = (List.take (ws, 256), List.drop (ws, 256))
            handle Subscript => (ws, [])
          val result = cv_eval ``x86_decodes ^(listSyntax.mk_list (now, ``:num``))``
      in app (fn t => TextIO.output (out, show t ^ "\n"))
           (fst (listSyntax.dest_list (rhs (concl result))));
         chunks later
      end;
val _ = chunks words;
val _ = TextIO.closeOut out;
"""

WINDOW = 15


@dataclass(frozen=True)
class Reading:
    """A decoder's reading of a word: its length, or None if it rejects it."""
    length: int | None
    text: str


def hol_decodes(words: list[bytes]) -> list[Reading]:
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        padded = (w + b"\xcc" * (WINDOW - len(w)) for w in words)
        (tmp / "words").write_text("".join(f"{int.from_bytes(p, 'little')}\n" for p in padded))
        script = (HOL_SCRIPT.replace("WORDS", str(tmp / "words"))
                  .replace("RESULT", str(tmp / "result")))
        (tmp / "decodes.sml").write_text(script)
        run = subprocess.run(["holbuild", "run", str(tmp / "decodes.sml")], cwd=REPO,
                             stdin=subprocess.DEVNULL, capture_output=True, text=True)
        if run.returncode != 0:
            raise SystemExit("holbuild run failed:\n" + (run.stdout + run.stderr)[-3000:])
        lines = (tmp / "result").read_text().splitlines()
    if len(lines) != len(words):
        raise SystemExit(f"HOL4 returned {len(lines)} results for {len(words)} words")
    readings = []
    for line in lines:
        length, _, text = line.partition(" ")
        readings.append(Reading(int(length), text) if text else Reading(None, line))
    return readings


SLOT = 32
LISTING = re.compile(r"^\s*([0-9a-f]+):\s+(.*)$")


def llvm_decodes(words: list[bytes], llvm: Path | None) -> list[Reading]:
    """llvm-objdump's reading of each word, padded with INT3 to resynchronize."""
    tool = (lambda name: str(llvm / name)) if llvm else (lambda name: name)
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        (tmp / "words.bin").write_bytes(b"".join(w + b"\xcc" * (SLOT - len(w)) for w in words))
        subprocess.run([tool("llvm-objcopy"), "-I", "binary", "-O", "elf64-x86-64",
                        str(tmp / "words.bin"), str(tmp / "words.o")], check=True)
        listing = subprocess.run([tool("llvm-objdump"), "-D", "-j", ".data", "--no-show-raw-insn",
                                  str(tmp / "words.o")], capture_output=True, text=True,
                                 check=True).stdout
    starts: dict[int, str] = {}
    order: list[int] = []
    for line in listing.splitlines():
        m = LISTING.match(line)
        if m:
            address = int(m[1], 16)
            starts[address] = m[2].strip()
            order.append(address)
    following = dict(zip(order, order[1:] + [len(words) * SLOT]))
    readings = []
    for k in range(len(words)):
        text = starts.get(k * SLOT)
        if text is None:
            raise SystemExit(f"llvm-objdump does not start an instruction at word {k}")
        length = following[k * SLOT] - k * SLOT
        readings.append(Reading(None if text == "<unknown>" else length, text))
    return readings


# ---------------------------------------------------------------------------

STATES = ("covered", "partial", "missing", "unsampled", "unreached")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--xed", type=Path, help="installed XED kit (default: build the pinned one)")
    parser.add_argument("--cache", type=Path,
                        default=Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
                        / "x86-hol", help="where the pinned XED is built")
    parser.add_argument("--llvm", type=Path, help="directory of llvm-objcopy and llvm-objdump")
    parser.add_argument("--samples", type=int, default=64,
                        help="words per tier-1 iform (an eighth of that for the others)")
    parser.add_argument("--rejected", type=int, default=4096,
                        help="random words XED rejects, checked to be rejected by HOL4")
    parser.add_argument("--json", type=Path, help="write the per-iform report here")
    args = parser.parse_args()

    if args.xed:
        kit = args.xed
    else:
        args.cache = args.cache.resolve()
        args.cache.mkdir(parents=True, exist_ok=True)
        kit = xed_kit(args.cache)
    rng = random.Random(1)
    with tempfile.TemporaryDirectory() as tmp:
        probe = build_probe(kit, Path(tmp))
        iforms = {}
        for line in subprocess.run([str(probe), "iforms"], capture_output=True, text=True,
                                   check=True).stdout.splitlines():
            name, iclass, isa_set, category = line.split()
            iforms[name] = Iform(name, iclass, isa_set, *tier_of(name, iclass, isa_set, category))
        sweep(probe, rng, iforms)
        rejected = rejected_words(probe, rng, args.rejected)

    rows = sorted({"", BEFORE_VEX} | set(ROWS.values()))
    # HOL4 decodes about 150 words a second, so iforms outside tier 1, and
    # the prefix rows, get an eighth of the samples.
    picked = [(iform, row, word) for iform in iforms.values() for row in rows
              for word in samples(iform, row, args.samples if iform.tier == "1" and not row
                                  else max(1, args.samples // 8), rng)]
    picked += [(None, "", word) for word in rejected]
    words = [word for _, _, word in picked]
    hol = hol_decodes(words)
    llvm = llvm_decodes(words, args.llvm)

    per_iform: dict[str, Counter] = defaultdict(Counter)
    per_row: dict[str, Counter] = defaultdict(Counter)
    mismatches = []
    disagreements = []
    for (iform, row, word), h, l in zip(picked, hol, llvm):
        xed_length = len(word) if iform else None
        allowed = HOL_FORMS.get(hol_key(h.text), set()) if h.length else set()
        if h.length is not None:
            reasons = [why for why, bad in (
                ("XED rejects", xed_length is None),
                ("llvm-objdump rejects", l.length is None),
                ("XED length", xed_length is not None and h.length != xed_length),
                ("llvm-objdump length", l.length is not None and h.length != l.length),
                ("class", iform is not None and iform.iclass not in allowed),
                ("vendor-defined", iform is not None and vendor_defined(iform.iclass, word)))
                if bad]
            llvm_only = {"llvm-objdump rejects", "llvm-objdump length"}
            if reasons and set(reasons) <= llvm_only:
                disagreements.append({"word": word.hex(), "hol": h.text, "xed": iform and iform.name,
                                      "llvm": l.text})
            elif reasons:
                mismatches.append({"word": word.hex(), "hol": h.text, "length": h.length,
                                   "xed": iform and iform.name, "llvm": l.text,
                                   "reasons": reasons})
        if iform is None:
            continue
        if row:
            per_row[row]["words"] += 1
            per_row[row]["decoded"] += h.length is not None
            continue
        counts = per_iform[iform.name]
        counts["samples"] += 1
        if not vendor_defined(iform.iclass, word):
            counts["in scope"] += 1
            counts["decoded"] += h.length == xed_length and iform.iclass in allowed

    report = []
    for iform in iforms.values():
        c = per_iform[iform.name]
        state = ("unreached" if not iform.words else "unsampled" if not c["in scope"] else "covered" if c["decoded"] == c["in scope"]
                 else "partial" if c["decoded"] else "missing")
        report.append({"iform": iform.name, "iclass": iform.iclass, "isa_set": iform.isa_set,
                       "tier": iform.tier, "excluded": iform.why, "words": iform.words,
                       "samples": c["samples"], "in_scope": c["in scope"],
                       "decoded": c["decoded"], "state": state})

    reached = sum(r["state"] != "unreached" for r in report)
    xed_commit = None if args.xed else XED_COMMIT
    xed = f"XED @ {xed_commit[:12]}" if xed_commit else f"XED from {args.xed} (unpinned)"
    print(f"{xed}: {reached} of {len(iforms)} iforms reached, "
          f"{len(words)} words decoded by HOL4 and llvm-objdump")
    tiers = {tier: Counter(r["state"] for r in report if r["tier"] == tier)
             for tier in ("1", "2", "3", "out")}
    print(f"{'tier':6} {'iforms':>7}" + "".join(f" {s:>9}" for s in STATES))
    for tier, t in tiers.items():
        print(f"{tier:6} {sum(t.values()):7}" + "".join(f" {t[s]:9}" for s in STATES))
    gaps = [r for r in report if r["tier"] == "1" and r["state"] not in ("covered", "unreached")]
    if gaps:
        print(f"tier 1 iforms not covered: {len(gaps)}")
        for r in gaps:
            print(f"  {r['iform']} ({r['state']}, {r['decoded']}/{r['in_scope']})")
    for row in rows[1:]:
        print(f"{row if row == BEFORE_VEX else row + ' prefix'}: {per_row[row]['words']} words, "
              f"{per_row[row]['decoded']} decoded by HOL4")
    print(f"words HOL4 decodes that the references reject or read otherwise: {len(mismatches)}")
    for m in mismatches[:20]:
        print(f"  {m['word']} {m['hol']} ({m['length']} bytes): {', '.join(m['reasons'])}; "
              f"XED {m['xed']}, llvm-objdump {m['llvm']}")
    print(f"words XED and HOL4 read alike that llvm-objdump rejects or reads otherwise: "
          f"{len(disagreements)}")
    for d in disagreements[:5]:
        print(f"  {d['word']} {d['hol']}: XED {d['xed']}, llvm-objdump {d['llvm']}")
    if args.json:
        args.json.write_text(json.dumps({"xed_commit": xed_commit,
                                         "tiers": {t: {s: c[s] for s in STATES}
                                                   for t, c in tiers.items()},
                                         "iforms": report,
                                         "rows": per_row, "mismatches": mismatches,
                                         "reference_disagreements": disagreements},
                                        indent=1) + "\n")


if __name__ == "__main__":
    main()
