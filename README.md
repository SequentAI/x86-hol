# x86-hol

An executable HOL4 model of x86-64 user-space instructions. It covers
the general-purpose integer instructions of 64-bit user mode (the
x86-64-v2 base with BMI1, BMI2, ADX, MOVBE and CRC32) and a subset of
SIMD and cryptographic instructions, and rejects unsupported encodings.

`x86Isa` defines instruction decoding and execution over a storage
interface. Its state includes general-purpose and XMM registers, the
instruction pointer, six boolean status flags, the direction flag, and byte-addressed memory
with read, write and execute permissions. Each step takes its undefined
flag values from an indexed stream. `x86IsaCv` instantiates the model
with sparse trees, translates it with `cv_trans` for `cv_eval`, and
proves that the executable step refines the functional model.

The conformance theories check decoded instructions and their lengths
against `llvm-objdump`, and check execution and fault outcomes against
observations from x86-64 hardware. `x86UndefinedFlags` records an audit
of undefined flag writes against [s2n-bignum](https://github.com/awslabs/s2n-bignum/blob/main/x86/proofs/x86.ml)
and the Intel instruction set reference.

## Build

With Poly/ML and holbuild on `PATH`, run

```sh
holbuild buildhol
holbuild -j4 build x86HolTheory
holbuild check
```

To reproduce the observations, use x86-64 Linux with a C compiler and
a CPU supporting the instructions under test. Install `python-zig`
(`pipx install ziglang==0.17.0`) and put `llvm-objdump` on `PATH`.
CI uses the `llvm-tools` component of Rust 1.99.1.

```sh
python3 tests/generate_decode.py --check
python3 tests/generate_exec.py --check
```

Omit `--check` to regenerate the case theories.

## Coverage

`tools/x86_coverage.py` measures the decoder against [Intel XED](https://github.com/intelxed/xed),
independently of the test cases. It sweeps the 64-bit encoding space,
groups the words XED accepts by instruction form (iform), decodes a
sample of each form in HOL4 and with `llvm-objdump`, and reports, per
tier of the instruction set, the forms the model covers and any word it
accepts that XED or `llvm-objdump` rejects or reads differently. It
fetches and builds XED at a pinned commit on first use.

```sh
python3 tools/x86_coverage.py --json coverage.json
```

## License

[BSD 3-Clause](LICENSE).
