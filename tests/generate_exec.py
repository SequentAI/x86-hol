#!/usr/bin/env python3
"""Run the execution cases of cases.py on an x86-64 CPU or under unicorn and
write the observed outcomes to x86ExecCasesScript.sml.

--backend native compiles native_harness.c with cc and runs the cases on the
host (x86-64 Linux only). --backend unicorn runs them under unicorn (QEMU's
TCG engine; `pip install unicorn==2.1.4`) on any host. Both must give the
same file; CI checks the committed one against native hardware. Flags are
recorded only where the architecture defines them. Where a case stops, at
an int3 or a fault, its data window and the watched bytes at the top of the
stack page are recorded too.
"""
import argparse
from dataclasses import dataclass
from pathlib import Path
import struct
import subprocess
import tempfile

from cases import (CODE_BASE, DATA_BASE, DATA_SIZE, ENTRY, FLAG_MASK, M32, STACK_BASE,
                   STACK_TOP, STACK_WINDOW, ExecCase, exec_cases)

PAGE = 4096
TIMEOUT = 60  # seconds for all native cases; each takes microseconds
PROT_BITS = {"r": 1, "w": 2, "x": 4}  # PROT_READ, PROT_WRITE, PROT_EXEC
FAULTS = {"fetch": "Fetch", "load": "Load", "store": "Store", "divide": "Divide",
          "alignment": "Alignment"}


@dataclass
class Outcome:
    fault: str | None  # a key of FAULTS
    data: bytes  # the DATA_SIZE bytes at DATA_BASE
    stack: bytes  # the STACK_WINDOW bytes at the top of the stack page
    rip: int = 0
    regs: tuple[int, ...] = ()
    xmm: tuple[int, ...] = ()
    flags: int = 0


def prot(permissions: str) -> int:
    return sum(PROT_BITS[c] for c in permissions)


def pages(case: ExecCase) -> tuple[bytes, bytes, bytes]:
    code = bytearray(b"\xcc" * PAGE)
    start = ENTRY - CODE_BASE
    code[start:start + len(case.code)] = case.code
    data = bytearray(PAGE)
    data[:len(case.data)] = case.data
    stack = bytearray(PAGE)
    stack[STACK_TOP - STACK_BASE:STACK_TOP - STACK_BASE + 8] = case.ret_addr.to_bytes(8, "little")
    return bytes(code), bytes(data), bytes(stack)


def run_native(cases: list[ExecCase], cc: str) -> list[Outcome]:
    harness = Path(__file__).resolve().parent / "native_harness.c"
    with tempfile.TemporaryDirectory(prefix="x86-native-") as temporary:
        binary = Path(temporary) / "native_harness"
        subprocess.run([cc, "-O1", "-o", str(binary), str(harness)], check=True)
        payload = bytearray()
        for case in cases:
            code, data, stack = pages(case)
            payload += code + data + stack
            payload += struct.pack("<16Q", *case.regs)
            payload += struct.pack("<QQII", case.flags, case.entry, prot(case.data_prot),
                                   prot(case.stack_prot))
            payload += b"".join(x.to_bytes(16, "little") for x in case.xmm)
        try:
            output = subprocess.run([str(binary)], input=bytes(payload), capture_output=True,
                                    check=True, timeout=TIMEOUT).stdout.decode()
        except subprocess.TimeoutExpired as error:
            stalled = cases[(error.stdout or b"").decode().count("\n")]
            raise SystemExit(f"{stalled.name}: no int3 or fault within {TIMEOUT} s") from None
    outcomes = []
    for line in output.splitlines():
        words = line.split()
        data, stack = bytes.fromhex(words[-2]), bytes.fromhex(words[-1])
        if words[0] == "fault":
            outcomes.append(Outcome(words[1], data, stack))
        else:
            values = [int(w, 16) for w in words[1:-2]]
            outcomes.append(Outcome(None, data, stack, values[0], tuple(values[1:17]),
                                    tuple(values[18:34]), values[17]))
    if len(outcomes) != len(cases):
        raise SystemExit(f"harness reported {len(outcomes)} outcomes for {len(cases)} cases")
    return outcomes


def run_unicorn(cases: list[ExecCase]) -> list[Outcome]:
    import unicorn
    from unicorn import x86_const as x86

    order = [x86.UC_X86_REG_RAX, x86.UC_X86_REG_RCX, x86.UC_X86_REG_RDX, x86.UC_X86_REG_RBX,
             x86.UC_X86_REG_RSP, x86.UC_X86_REG_RBP, x86.UC_X86_REG_RSI, x86.UC_X86_REG_RDI,
             x86.UC_X86_REG_R8, x86.UC_X86_REG_R9, x86.UC_X86_REG_R10, x86.UC_X86_REG_R11,
             x86.UC_X86_REG_R12, x86.UC_X86_REG_R13, x86.UC_X86_REG_R14, x86.UC_X86_REG_R15]
    xmm = [getattr(x86, f"UC_X86_REG_XMM{i}") for i in range(16)]
    bits = {"r": unicorn.UC_PROT_READ, "w": unicorn.UC_PROT_WRITE, "x": unicorn.UC_PROT_EXEC}
    outcomes = []
    for case in cases:
        # A fresh engine per case: unicorn keeps translated blocks across runs.
        uc = unicorn.Uc(unicorn.UC_ARCH_X86, unicorn.UC_MODE_64)
        # The default QEMU64 model does not expose ADX.
        uc.ctl_set_cpu_model(x86.UC_CPU_X86_BROADWELL)
        code, data, stack = pages(case)
        for base, content, prot in [
                (CODE_BASE, code, unicorn.UC_PROT_READ | unicorn.UC_PROT_EXEC),
                (DATA_BASE, data, sum(bits[c] for c in case.data_prot)),
                (STACK_BASE, stack, sum(bits[c] for c in case.stack_prot))]:
            uc.mem_map(base, PAGE, prot)
            uc.mem_write(base, content)
        for reg, value in zip(order, case.regs):
            uc.reg_write(reg, value)
        for reg, value in zip(xmm, case.xmm):
            uc.reg_write(reg, value)
        uc.reg_write(x86.UC_X86_REG_EFLAGS, 0x202 | case.flags)
        trapped = []
        uc.hook_add(unicorn.UC_HOOK_INTR, lambda uc, number, _: (trapped.append(number), uc.emu_stop()))

        def windows() -> tuple[bytes, bytes]:
            return (bytes(uc.mem_read(DATA_BASE, DATA_SIZE)),
                    bytes(uc.mem_read(STACK_BASE + PAGE - STACK_WINDOW, STACK_WINDOW)))

        # Unicorn writes the bytes of a page-crossing store that fall in a
        # writable page before faulting on the rest, and splits a 16-byte
        # store into two 8-byte writes; hardware writes none. So the windows
        # of a store fault are those before the faulting instruction.
        writable = [base for base, permissions in [(DATA_BASE, case.data_prot),
                                                   (STACK_BASE, case.stack_prot)]
                    if "w" in permissions]
        before_instruction: list[tuple[bytes, bytes]] = []
        before_store_fault: list[tuple[bytes, bytes]] = []

        def on_write(uc, access, address, size, value, _) -> None:
            if not all((a & ~(PAGE - 1)) in writable for a in (address, address + size - 1)):
                before_store_fault.append(before_instruction[-1])

        # Unicorn omits the #GP of some misaligned legacy SIMD reads.
        # Stop before access, as hardware does.
        aligned_read = [False]
        misaligned = []

        # Unicorn's QEMU 5 core sets CF at BZHI index 63 and clears bit 63
        # above it, and inverts BLSI's CF; the SDM sets CF only past index
        # 63, keeps the source there (ZF and SF from it), and sets BLSI's
        # CF on a nonzero source. It also caps BEXTR's length at 63, where
        # the SDM keeps every bit from the start up at a length past 63. So
        # the backend corrects all three after they run: the register to
        # write, if any, its value, and CF.
        fix: list[tuple[int | None, int, bool]] = []
        # It also adds PHADDD's source pairs after writing the destination's,
        # so with one register for both, the upper two lanes come out wrong;
        # the backend writes the SDM's result instead.
        fix_xmm: list[tuple[int, int]] = []

        def on_instruction(uc, address, size, _) -> None:
            if fix_xmm:
                reg, value = fix_xmm.pop()
                uc.reg_write(xmm[reg], value)
            if fix:
                dest, value, cf = fix.pop()
                eflags = uc.reg_read(x86.UC_X86_REG_EFLAGS) & ~1 | cf
                if dest is not None:
                    uc.reg_write(order[dest], value)
                    eflags = eflags & ~0xC0 | (value == 0) << 6 | (value >> 63) << 7
                uc.reg_write(x86.UC_X86_REG_EFLAGS, eflags)
            before_instruction[:] = [windows()]
            b = bytes(uc.mem_read(address, size))
            if size == 5 and b[0] == 0xC4 and b[1] & 0x1F == 2 and b[2] & 0x83 == 0x80 \
                    and b[4] >> 6 == 3:
                reg = (b[4] >> 3 & 7) | (~b[1] >> 4 & 8)
                src = uc.reg_read(order[(b[4] & 7) | (~b[1] >> 2 & 8)])
                vvvv = ~b[2] >> 3 & 15
                if b[3] == 0xF5:
                    index = uc.reg_read(order[vvvv]) & 0xFF
                    if index >= 63:
                        fix.append((reg if index > 63 else None, src, index > 63))
                elif b[3] == 0xF3 and reg == 3:
                    fix.append((None, 0, src != 0))
                elif b[3] == 0xF7:
                    control = uc.reg_read(order[vvvv])
                    start = control & 0xFF
                    if control >> 8 & 0xFF > 63 and start < 64:
                        fix.append((reg, src >> start, False))
            rest = b[2:] if len(b) > 1 and 0x40 <= b[1] <= 0x4F else b[1:]
            if b[:1] == b"\x66" and rest[:3] == b"\x0f\x38\x02" and len(rest) == 4 \
                    and rest[3] >> 6 == 3:
                rex = b[1] if len(b) == 6 else 0
                reg = (rest[3] >> 3 & 7) | (rex & 4) << 1
                if reg == (rest[3] & 7) | (rex & 1) << 3:
                    v = uc.reg_read(xmm[reg])
                    sums = [(v >> 64 * i & M32) + (v >> 64 * i + 32 & M32) & M32 for i in (0, 1)]
                    fix_xmm.append((reg, sum(x << 32 * i for i, x in enumerate(sums * 2))))
            aligned_read[0] = b[:1] == b"\x66" and (
                rest[:2] in (b"\x0f\x6f", b"\x0f\xef", b"\x0f\x6c", b"\x0f\x66", b"\x0f\x76")
                or rest[:3] in (b"\x0f\x38\x00", b"\x0f\x38\x10")
                or (rest[:2] == b"\x0f\x38" and len(rest) >= 4 and 0xDC <= rest[2] <= 0xDF))

        def on_read(uc, access, address, size, value, _) -> bool:
            """Check the address on the first half of the 16-byte read."""
            if aligned_read[0] and address % 16:
                misaligned.append(address)
                uc.emu_stop()
            aligned_read[0] = False
            return False

        uc.hook_add(unicorn.UC_HOOK_CODE, on_instruction)
        uc.hook_add(unicorn.UC_HOOK_MEM_WRITE, on_write)
        uc.hook_add(unicorn.UC_HOOK_MEM_READ, on_read)
        uc.hook_add(unicorn.UC_HOOK_MEM_READ_INVALID, on_read)
        fault = None
        try:
            uc.emu_start(case.entry, -1, count=100000)
        except unicorn.UcError as error:
            kinds = {unicorn.UC_ERR_FETCH_PROT: "fetch", unicorn.UC_ERR_FETCH_UNMAPPED: "fetch",
                     unicorn.UC_ERR_READ_PROT: "load", unicorn.UC_ERR_READ_UNMAPPED: "load",
                     unicorn.UC_ERR_WRITE_PROT: "store", unicorn.UC_ERR_WRITE_UNMAPPED: "store"}
            if error.errno not in kinds:
                raise SystemExit(f"{case.name}: unexpected unicorn error {error}")
            fault = kinds[error.errno]
        if trapped == [0]:  # interrupt 0: the divide error (#DE)
            fault = "divide"
        if misaligned:
            fault = "alignment"
        if fault:
            outcomes.append(Outcome(fault, *(before_store_fault[0] if fault == "store"
                                             else windows())))
            continue
        if trapped != [3]:
            raise SystemExit(f"{case.name}: stopped without reaching int3 ({trapped})")
        outcomes.append(Outcome(None, *windows(), uc.reg_read(x86.UC_X86_REG_RIP) - 1,
                                tuple(uc.reg_read(r) for r in order),
                                tuple(uc.reg_read(r) for r in xmm),
                                uc.reg_read(x86.UC_X86_REG_EFLAGS) & FLAG_MASK))
    return outcomes


def words(values, width: int = 0) -> str:
    return "[" + "; ".join(f"0x{v:0{width}x}w" for v in values) + "]"


def perm(permissions: str) -> str:
    return "perm " + " ".join("T" if c in permissions else "F" for c in "rwx")


def render(cases: list[ExecCase], outcomes: list[Outcome]) -> str:
    lines = ["(* Generated by generate_exec.py from cases.py. *)", "Theory x86ExecCases",
             "Ancestors x86Isa", "",
             "(* entry, RAX..R15, XMM0..XMM15, flags, data window at DATA_BASE, return",
             "   address at STACK_TOP, data page permissions, stack page permissions *)",
             "Type exec_input = ``:word64 # word64 list # word128 list # word64 # word8 list #",
             "                     word64 # perm # perm``",
             "",
             "(* The int3 reached, with RAX..R15, XMM0..XMM15 and the flags there (CF PF",
             "   AF ZF SF OF bits, those outside the mask cleared), and the mask of flags",
             "   compared: all but the undefined ones. Or the fault raised. *)",
             "Datatype:",
             "  outcome = Reached word64 (word64 list) (word128 list) word64 word64",
             "          | Faulted fault_kind",
             "End", "",
             "(* Bytes at ENTRY in a code page of int3s, inputs, observed outcome, and the",
             "   bytes observed where the case stopped in the data window and at the top",
             "   of the stack page. *)",
             "Type exec_case = ``:word8 list # exec_input # outcome # word8 list # word8 list``",
             ""]
    for number, (case, outcome) in enumerate(zip(cases, outcomes)):
        if outcome.fault:
            result = "Faulted " + FAULTS[outcome.fault]
        else:
            mask = FLAG_MASK & ~case.undefined
            result = (f"Reached 0x{outcome.rip:x}w\n       {words(outcome.regs, 16)}\n"
                      f"       {words(outcome.xmm)}\n"
                      f"       0x{outcome.flags & mask:x}w 0x{mask:x}w")
        lines += [f"(* {case.name} *)", f"Definition exec_case_{number}_def:",
                  f"  exec_case_{number} : exec_case =",
                  f"    ({words(case.code, 2)},",
                  f"     (0x{case.entry:x}w, {words(case.regs, 16)},",
                  f"      {words(case.xmm)},",
                  f"      0x{case.flags:x}w, {words(case.data, 2)},",
                  f"      0x{case.ret_addr:x}w, {perm(case.data_prot)}, {perm(case.stack_prot)}),",
                  f"     {result},",
                  f"     {words(outcome.data[:len(case.data)], 2)},",
                  f"     {words(outcome.stack[STACK_WINDOW - case.stack_watch:], 2)})",
                  "End", ""]
    lines += ["Definition exec_case_count_def:", f"  exec_case_count = {len(cases)}n", "End", ""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", choices=["native", "unicorn"], default="native")
    parser.add_argument("--cc", default="cc", help="C compiler for the native harness")
    parser.add_argument("--check", action="store_true",
                        help="fail if the committed theory differs instead of writing it")
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    cases = exec_cases()
    outcomes = run_native(cases, args.cc) if args.backend == "native" else run_unicorn(cases)
    for case, outcome in zip(cases, outcomes, strict=True):
        if case.expected_reg is not None:
            register, value = case.expected_reg
            if outcome.fault is not None or outcome.regs[register] != value:
                raise SystemExit(f"{case.name}: {args.backend} did not produce register {register}={value:#x}")
        if case.expected_xmm is not None:
            register, value = case.expected_xmm
            if outcome.fault is not None or outcome.xmm[register] != value:
                raise SystemExit(f"{case.name}: {args.backend} did not produce XMM{register}={value:032x}")
        if case.expected_data is not None:
            offset, expected = case.expected_data
            if outcome.fault is not None or outcome.data[offset:offset + len(expected)] != expected:
                raise SystemExit(f"{case.name}: {args.backend} did not write {expected.hex()}")
    output = directory / "x86ExecCasesScript.sml"
    rebuilt = render(cases, outcomes)
    if args.check:
        if output.read_text() != rebuilt:
            committed = output.read_text().splitlines()
            for number, (old, new) in enumerate(zip(committed, rebuilt.splitlines()), 1):
                if old != new:
                    print(f"line {number}:\n  committed: {old}\n  {args.backend}: {new}")
            raise SystemExit(f"{args.backend} outcomes differ from x86ExecCasesScript.sml")
        print(f"{len(cases)} execution cases match on {args.backend}")
    else:
        output.write_text(rebuilt)


if __name__ == "__main__":
    main()
