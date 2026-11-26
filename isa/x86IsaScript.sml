(* x86-64 64-bit-mode user-level integer and vector instructions, after the
   Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 2
   (instruction set reference). The decoder recognizes the supported forms.
   Other encodings are rejected. *)
Theory x86Isa
Ancestors words list arithmetic x86Aes
Libs wordsLib

Datatype:
  perm = <| read : bool; write : bool; execute : bool |>
End

(* The six arithmetic status flags of RFLAGS. *)
Datatype:
  eflags = <| CF : bool; PF : bool; AF : bool; ZF : bool; SF : bool; OF : bool |>
End

Datatype:
  x86_machine = <|
    regs : 'g;
    xmm : 'x;
    rip : word64;
    flags : eflags;
    mem : 'm;
    perms : 'p
  |>
End

(* Registers are numbered as in ModRM/REX: 0 RAX, 1 RCX, 2 RDX, 3 RBX,
   4 RSP, 5 RBP, 6 RSI, 7 RDI, 8..15 R8..R15; and 0..15 XMM0..XMM15, the
   REX bit giving the high half. *)
Type x86_state = ``:(word4 -> word64, word64 -> word8, word64 -> perm, word4 -> word128) x86_machine``

Datatype:
  x86_storage = <|
    get_reg : 'g -> word4 -> word64;
    put_reg : word4 -> word64 -> 'g -> 'g;
    get_xmm : 'x -> word4 -> word128;
    put_xmm : word4 -> word128 -> 'x -> 'x;
    get_byte : 'm -> word64 -> word8;
    put_byte : word64 -> word8 -> 'm -> 'm;
    get_perm : 'p -> word64 -> perm
  |>
End

Definition functional_storage_def:
  functional_storage = <|
    get_reg := (λf (r:word4). f r);
    put_reg := (λ(r:word4) (v:word64) f. (r =+ v) f);
    get_xmm := (λf (r:word4). f r);
    put_xmm := (λ(r:word4) (v:word128) f. (r =+ v) f);
    get_byte := (λf (a:word64). f a);
    put_byte := (λ(a:word64) (v:word8) f. (a =+ v) f);
    get_perm := (λf (a:word64). f a)
  |>
End

(* Operand width: byte, word (66 prefix), doubleword, quadword (REX.W). *)
Datatype:
  size = S8 | S16 | S32 | S64
End

(* CMP and TEST compute SUB and AND for their flags only. *)
Datatype:
  binop = ADD | OR | ADC | SBB | AND | SUB | XOR | CMP | TEST
End

Datatype:
  shift = SHL | SHR | SAR
End

Datatype:
  bitcount = TZCNT | LZCNT | POPCNT
End

(* BLSR resets, BLSI isolates and BLSMSK masks up to the lowest set bit. *)
Datatype:
  bls = BLSR | BLSI | BLSMSK
End

Datatype:
  pdep = PDEP | PEXT
End

(* Packed operations on two XMM registers. *)
Datatype:
  pbinop = PXOR | PADDD | PADDQ | PAND | POR | PCMPEQB | PMULLD | PMINUD | PMAXUD
         | PSUBD | PSUBQ | PABSD | PHADDD | PCMPGTQ | PMULUDQ | PMULDQ | PMINSD | PMAXSD
         | PACKUSDW | PACKSSDW | PMADDWD | PMADDUBSW | PACKUSWB | PSADBW | PAVGB | PAVGW
         | PADDUSB | PSUBUSB | PHMINPOSUW
End

(* Mem: base (if any) + index << scale (if any) + displacement. RipRel: the
   displacement from the end of the instruction. *)
Datatype:
  address = Mem (word4 option) (word4 option) word2 word64 | RipRel word64
End

Datatype:
  rm = RmReg word4 | RmMem address
End

(* Binop, Mov and Cmov take the destination first, as do the SSE2 forms
   VecLoad to Movd. Byte-register operands are the low bytes of registers
   0..15 (AH..BH are not modelled). *)
Datatype:
  x86_instr =
    MovImm word4 word32                 (* B8+r id: MOV r32, imm32 *)
  | MovImm64 word4 word64               (* REX.W C7 /0 id: MOV r64, imm32 sign-extended;
                                           REX.W B8+r io: MOV r64, imm64 *)
  | Mov size rm rm                      (* 88, 89, 8B /r *)
  | Binop binop size rm rm              (* 01 03 09 13 1B 21 28 2B 30 31 33 38 39 84 85 /r *)
  | BinopImm binop size rm word64       (* 83 /0 /3 /4 /7 ib; 0D id: OR EAX, imm32;
                                           81 /6 id: XOR r32, imm32; 80 /7 ib: CMP r8, imm8 *)
  | Movzx size word4 rm                 (* 0F B6, 0F B7 /r: MOVZX r32, r/m8 or r/m16 *)
  | Movsxd word4 rm                     (* REX.W 63 /r: MOVSXD r64, r/m32 *)
  | Movsx word4 rm                      (* 0F BE /r: MOVSX r32, r8 *)
  | Cdqe                                (* REX.W 98 *)
  | Lea word4 address                   (* REX.W 8D /r *)
  | Not size rm                         (* F7 /2, REX.W F7 /2 *)
  | Neg size rm                         (* F7 /3 *)
  | Inc size rm                         (* FF /0 *)
  | Dec64 word4                        (* REX.W FF /1: DEC r64 *)
  | Shift shift size rm (word8 option)  (* C1 /5 /7 ib, or by CL (NONE): D3 /4 /7;
                                           REX.W D1 /5: SHR r64, 1 (SOME 1w) *)
  | Rotate bool size word4 (word8 option) (* C1 /0 ib: ROL r32, imm8 (T); REX.W D3 /1: ROR r64, CL *)
  | Imul word4 rm                       (* REX.W 0F AF /r: IMUL r64, r/m64 *)
  | MulWide bool word4                  (* REX.W F7 /4, /5: MUL, IMUL r64 (signed if T) *)
  | Div bool size word4                 (* F7 /6, REX.W F7 /6, /7: DIV r32, DIV r64, IDIV r64 *)
  | Cqo                                 (* REX.W 99 *)
  | ShiftDouble bool word4 word4        (* REX.W 0F A5, 0F AD /r: SHLD (T), SHRD r64, r64, CL *)
  | Bswap word4                         (* REX.W 0F C8+r *)
  | Adx bool word4 word4                (* 66 or F3 REX.W 0F 38 F6 /r: ADCX (F), ADOX (T), r64, r64 *)
  | MovbeLoad word4 address             (* REX.W 0F 38 F0 /r: MOVBE r64, m64 *)
  | MovbeStore address word4            (* REX.W 0F 38 F1 /r: MOVBE m64, r64 *)
  | Crc32 size word4 rm                  (* F2 0F 38 F0 /r: CRC32 r32, r/m8;
                                           F2 REX.W 0F 38 F1 /r: CRC32 r64, r64 *)
  | BitCount bitcount size word4 word4  (* F3 REX.W 0F BC, BD, B8 /r: TZCNT, LZCNT, POPCNT r64, r64;
                                           F3 0F BC, B8 /r: TZCNT, POPCNT r32, r32 *)
  | Cmov word4 size word4 rm            (* 0F 4C /r: CMOVL r32; REX.W 0F 42, 4C /r: CMOVB, CMOVL r64 *)
  | Setcc word4 rm                      (* 0F 92, 93, 94, 9C, 9F /r: SETB, SETAE, SETE, SETL, SETG r8 *)
  | Mulx word4 word4 rm                 (* VEX.LZ.F2.0F38.W1 F6 /r: MULX r64 (high), r64 (low), r/m64 *)
  | Rorx size word4 word4 word8         (* VEX.LZ.F2.0F3A.W0, W1 F0 /r ib: RORX r32, r32 or r64, r64 *)
  | ShiftX shift word4 word4 word4      (* VEX.LZ.66, F2, F3.0F38.W1 F7 /r: SHLX, SHRX, SARX
                                           r64, r64, r64 (count) *)
  | Andn word4 word4 word4              (* VEX.LZ.0F38.W1 F2 /r: ANDN r64, r64 (inverted), r64 *)
  | Bzhi word4 word4 word4              (* VEX.LZ.0F38.W1 F5 /r: BZHI r64, r64, r64 (index) *)
  | Bls bls word4 word4                 (* VEX.LZ.0F38.W1 F3 /1, /3, /2: BLSR, BLSI, BLSMSK r64, r64 *)
  | Pdep pdep word4 word4 word4         (* VEX.LZ.F2, F3.0F38.W1 F5 /r: PDEP, PEXT r64, r64, r64 (mask) *)
  | Bextr word4 word4 word4             (* VEX.LZ.0F38.W1 F7 /r: BEXTR r64, r64, r64 (control) *)
  | Push word4                          (* 50+r *)
  | Pop word4                           (* 58+r *)
  | Call word64                         (* E8 cd *)
  | Jcc word4 word64                    (* 73-77, 79 cb; 0F 84, 85 cd *)
  | Jmp word64                          (* EB cb *)
  | JmpReg word4                        (* FF /4: JMP r64 *)
  | Ret                                 (* C3 *)
  | Nop                                 (* 90, 66 90, 0F 1F /0 *)
  | VecLoad bool word4 address          (* 0F 10, F3 0F 6F /r: MOVUPS, MOVDQU xmm, m128;
                                           66 0F 6F /r: MOVDQA xmm, m128 (aligned, T) *)
  | VecStore address word4              (* 0F 11, F3 0F 7F /r: MOVUPS, MOVDQU m128, xmm *)
  | VecMov word4 word4                  (* 66 0F 6F /r: MOVDQA xmm, xmm *)
  | Pbinop pbinop word4 word4           (* 0F 57, 66 0F EF /r: XORPS, PXOR; 66 0F FE, D4, DB,
                                           EB, 74, FA, FB, F4, 6B, F5, 67, F6, E0, E3, DC, D8 /r:
                                           PADDD, PADDQ, PAND, POR, PCMPEQB, PSUBD, PSUBQ, PMULUDQ,
                                           PACKSSDW, PMADDWD, PACKUSWB, PSADBW, PAVGB, PAVGW,
                                           PADDUSB, PSUBUSB; 66 0F 38 40, 3B, 3F, 1E, 02, 37, 28,
                                           39, 3D, 2B, 04, 41 /r: PMULLD, PMINUD, PMAXUD, PABSD,
                                           PHADDD, PCMPGTQ, PMULDQ, PMINSD, PMAXSD, PACKUSDW,
                                           PMADDUBSW, PHMINPOSUW xmm, xmm *)
  | Pblendvb word4 rm                  (* 66 0F 38 10 /r: PBLENDVB xmm, xmm/m128, XMM0 *)
  | Pcmpd bool word4 rm                (* 66 0F 66, 76 /r: PCMPGTD (T), PCMPEQD xmm, xmm/m128 *)
  | Pwiden bool size word4 address     (* 66 0F 38 21, 31 /r: PMOVSXBD (T), PMOVZXBD xmm, m32
                                          (S32); 25, 35 /r: PMOVSXDQ, PMOVZXDQ xmm, m64 (S64);
                                          20, 30 /r: PMOVSXBW, PMOVZXBW xmm, m64 (S16) *)
  | Ptest word4 word4                    (* 66 0F 38 17 /r: PTEST xmm, xmm *)
  | Pshufd word4 word4 word8            (* 66 0F 70 /r ib: PSHUFD xmm, xmm, imm8 *)
  | Pshufw bool word4 word4 word8       (* F2, F3 0F 70 /r ib: PSHUFLW, PSHUFHW (T) xmm, xmm, imm8 *)
  | Pshufb word4 rm                     (* 66 0F 38 00 /r: PSHUFB xmm, xmm (RmReg) or m128
                                           (aligned) *)
  | Pshift bool size word4 word8        (* 66 0F 72 /6, /2 ib: PSLLD (T), PSRLD xmm, imm8 (S32);
                                           66 0F 73 /6, /2 ib: PSLLQ (T), PSRLQ (S64) *)
  | Psrad word4 word8                   (* 66 0F 72 /4 ib: PSRAD xmm, imm8 *)
  | Pshiftdq bool word4 word8           (* 66 0F 73 /7, /3 ib: PSLLDQ (T), PSRLDQ xmm, imm8 *)
  | PxorMem word4 address              (* 66 0F EF /r: PXOR xmm, m128 (aligned) *)
  | AesRound aes_round word4 rm         (* 66 0F 38 DC..DF /r: AES round, xmm or aligned m128 *)
  | AesImc word4 word4                  (* 66 0F 38 DB /r: AESIMC xmm, xmm *)
  | Pclmul word4 word4 word8            (* 66 0F 3A 44 /r ib: PCLMULQDQ xmm, xmm, imm8 *)
  | AesKeygen word4 word4 word8         (* 66 0F 3A DF /r ib: AESKEYGENASSIST xmm, xmm, imm8 *)
  | Palignr word4 word4 word8           (* 66 0F 3A 0F /r ib: PALIGNR xmm, xmm, imm8 *)
  | Pinsrq word4 rm word8              (* 66 REX.W 0F 3A 22 /r ib: PINSRQ xmm, r/m64, imm8 *)
  | Pextrq rm word4 word8              (* 66 REX.W 0F 3A 16 /r ib: PEXTRQ r/m64, xmm, imm8 *)
  | Punpcklqdq word4 word4             (* 66 0F 6C /r: PUNPCKLQDQ xmm, xmm *)
  | Pmovmskb word4 word4                (* 66 0F D7 /r: PMOVMSKB r32, xmm *)
  | Movd size word4 word4               (* 66 0F 7E /r: MOVD r32, xmm; 66 REX.W 0F 7E /r: MOVQ r64, xmm *)
  | MovqXmm word4 word4                 (* 66 REX.W 0F 6E /r: MOVQ xmm, r64 *)
  | Pinsrd word4 rm word8              (* 66 0F 3A 22 /r ib: PINSRD xmm, r/m32, imm8 *)
  | Pextrd rm word4 word8              (* 66 0F 3A 16 /r ib: PEXTRD r/m32, xmm, imm8 *)
  | MovdXmm word4 rm                   (* 66 0F 6E /r: MOVD xmm, r/m32 *)
End

(* Divide: the divide error (#DE) of DIV and IDIV. Alignment: the general
   protection fault (#GP) of a legacy SIMD instruction requiring
   a 16-byte-aligned memory operand. *)
Datatype:
  fault_kind = Unsupported | Fetch | Load | Store | Divide | Alignment
End

Datatype:
  x86_result = Next 's | Fault fault_kind
End

(* Decoding *)

Definition reg_num_def:
  reg_num high (field:word3) : word4 = (if high then 8w else 0w) + w2w field
End

Definition le_word_def:
  le_word [] = 0w : word64 ∧
  le_word (b::bs) = w2w (b:word8) || (le_word bs << 8)
End

(* A decoder's outcome on a byte list: the value and the number of bytes it
   takes; Truncated when the list ends before the decoder has the bytes it
   needs; Rejected when the bytes it has are no modelled form. *)
Datatype:
  decoded = Decoded 'a num | Truncated | Rejected
End

(* An operand outside the forms an opcode allows. *)
Definition unmatched_def:
  unmatched (Decoded v n) = Rejected ∧
  unmatched Truncated = Truncated ∧
  unmatched Rejected = Rejected
End

(* The displacement of a ModRM memory operand of the given mod. *)
Definition displacement_def:
  displacement (md:word2) bytes =
    if md = 0w then Decoded (0w : word64) 0
    else if md = 1w then
      (case bytes of [] => Truncated | b::_ => Decoded (sw2sw (b:word8)) 1)
    else if LENGTH bytes < 4 then Truncated
    else Decoded (sw2sw (w2w (le_word (TAKE 4 bytes)) : word32)) 4
End

(* ModRM (and SIB) bytes under the REX bits r, x, b: the reg field and the
   r/m operand. *)
Definition decode_modrm_def:
  decode_modrm (r,x,b) [] = Truncated ∧
  decode_modrm (r,x,b) (modrm::rest) =
    let md = (7 >< 6) modrm : word2;
        reg = reg_num r ((5 >< 3) modrm);
        field = (2 >< 0) modrm : word3
    in
      if md = 3w then Decoded (reg, RmReg (reg_num b field)) 1
      else if field = 4w then
        (case rest of
           [] => Truncated
         | sib::rest' =>
             let base = (2 >< 0) sib : word3;
                 index = reg_num x ((5 >< 3) sib);
                 scale = (7 >< 6) sib : word2;
                 idx = if index = 4w then NONE else SOME index
             in
               if base = 5w ∧ md = 0w then
                 (case displacement 2w rest' of
                    Decoded d n => Decoded (reg, RmMem (Mem NONE idx scale d)) (2 + n)
                  | other => unmatched other)
               else
                 case displacement md rest' of
                   Decoded d n =>
                     Decoded (reg, RmMem (Mem (SOME (reg_num b base)) idx scale d)) (2 + n)
                 | other => unmatched other)
      else if field = 5w ∧ md = 0w then
        (case displacement 2w rest of
           Decoded d n => Decoded (reg, RmMem (RipRel d)) (1 + n)
         | other => unmatched other)
      else
        case displacement md rest of
          Decoded d n => Decoded (reg, RmMem (Mem (SOME (reg_num b field)) NONE 0w d)) (1 + n)
        | other => unmatched other
End

(* Legacy prefixes the targets use: 66 (operand size, and SSE2's mandatory
   prefix), F2 and F3 (SSE2's mandatory prefixes) and 2E (CS segment,
   ignored in 64-bit mode). *)
Definition split_prefixes_def:
  split_prefixes [] = ([], []) ∧
  split_prefixes (b::bs) =
    if b = 0x66w ∨ b = 0xF2w ∨ b = 0xF3w ∨ b = 0x2Ew then
      (let (ps, rest) = split_prefixes bs in (b::ps, rest))
    else ([], b::bs)
End

(* Registers 4..7 of a byte operand are AH..BH without a REX prefix. *)
Definition byte_reg_ok_def:
  byte_reg_ok (rex:word8) (r:word4) ⇔ rex ≠ 0w ∨ r <₊ 4w
End

(* The operation of an op r/m, r opcode (register operands) at REX.W w. *)
Definition rr_binop_def:
  rr_binop (op:word8) w =
    if op = 0x01w then SOME ADD
    else if op = 0x09w then SOME OR
    else if op = 0x11w ∧ w then SOME ADC
    else if op = 0x19w ∧ w then SOME SBB
    else if op = 0x21w ∧ ¬w then SOME AND
    else if op = 0x29w ∧ w then SOME SUB
    else if op = 0x31w then SOME XOR
    else if op = 0x39w then SOME CMP
    else if op = 0x85w then SOME TEST
    else NONE
End

(* The operation of an op r, m opcode (memory source) at REX.W w. *)
Definition rm_binop_def:
  rm_binop (op:word8) w =
    if op = 0x03w then SOME ADD
    else if op = 0x13w ∧ w then SOME ADC
    else if op = 0x1Bw ∧ w then SOME SBB
    else if op = 0x2Bw ∧ w then SOME SUB
    else if op = 0x33w ∧ ¬w then SOME XOR
    else NONE
End

(* 83 /digit ib at REX.W w, on a register operand if reg. *)
Definition imm_binop_def:
  imm_binop w (digit:word3) reg =
    if reg then
      (if digit = 0w then SOME ADD
       else if digit = 2w ∧ w then SOME ADC
       else if digit = 3w ∧ ¬w then SOME SBB
       else if digit = 4w then SOME AND
       else if digit = 5w ∧ w then SOME SUB
       else if digit = 7w then SOME CMP
       else NONE)
    else if digit = 7w ∧ ¬w then SOME CMP else NONE
End

(* A ModRM operand that must be a register: other operands are rejected
   from the ModRM byte, before any SIB or displacement byte. *)
Definition decode_reg_modrm_def:
  decode_reg_modrm bits [] = Truncated ∧
  decode_reg_modrm bits (modrm::rest) =
    if (7 >< 6) modrm = (3w:word2) then decode_modrm bits (modrm::rest) else Rejected
End

(* 0F 1F /0 with a memory operand with a base (multi-byte nop) after its
   0F, with the bytes from 1F on. Other group digits, RIP-relative and
   no-base operands are rejected from their ModRM and SIB bytes, before
   their displacement. *)
Definition decode_nop_def:
  decode_nop [] = Truncated ∧
  decode_nop (b::modrm) =
    if b ≠ 0x1Fw then Rejected
    else
      case modrm of
        [] => Truncated
      | m::rest =>
          if (5 >< 3) m ≠ (0w:word3) ∨
             (7 >< 6) m = (0w:word2) ∧
             ((2 >< 0) m = (5w:word3) ∨
              (2 >< 0) m = (4w:word3) ∧ (case rest of sib::_ => (2 >< 0) sib = (5w:word3) | [] => F))
          then Rejected
          else
            case decode_modrm (F,F,F) modrm of
              Decoded (_, RmMem (Mem (SOME base) index scale d)) n => Decoded Nop (2 + n)
            | other => unmatched other
End

(* The 66 0F b operations on two XMM registers. *)
Definition sse_binop_def:
  sse_binop (b:word8) =
    if b = 0xFEw then SOME PADDD
    else if b = 0xD4w then SOME PADDQ
    else if b = 0xDBw then SOME PAND
    else if b = 0xEBw then SOME POR
    else if b = 0x74w then SOME PCMPEQB
    else if b = 0xFAw then SOME PSUBD
    else if b = 0xFBw then SOME PSUBQ
    else if b = 0xF4w then SOME PMULUDQ
    else if b = 0x6Bw then SOME PACKSSDW
    else if b = 0xF5w then SOME PMADDWD
    else if b = 0x67w then SOME PACKUSWB
    else if b = 0xF6w then SOME PSADBW
    else if b = 0xE0w then SOME PAVGB
    else if b = 0xE3w then SOME PAVGW
    else if b = 0xDCw then SOME PADDUSB
    else if b = 0xD8w then SOME PSUBUSB
    else NONE
End

(* The SSSE3, SSE4.1 and SSE4.2 register operations on the 66 0F 38 map. *)
Definition sse4_binop_def:
  sse4_binop (b:word8) =
    if b = 0x40w then SOME PMULLD
    else if b = 0x3Bw then SOME PMINUD
    else if b = 0x3Fw then SOME PMAXUD
    else if b = 0x1Ew then SOME PABSD
    else if b = 0x02w then SOME PHADDD
    else if b = 0x37w then SOME PCMPGTQ
    else if b = 0x28w then SOME PMULDQ
    else if b = 0x39w then SOME PMINSD
    else if b = 0x3Dw then SOME PMAXSD
    else if b = 0x2Bw then SOME PACKUSDW
    else if b = 0x04w then SOME PMADDUBSW
    else if b = 0x41w then SOME PHMINPOSUW
    else NONE
End

(* The vector forms 0F b after the mandatory prefix p (0w when
   absent) and the REX byte, with the bytes from b on and the number of
   bytes from the 0F on. REX.R and REX.B select XMM8..XMM15 and R8..R15;
   REX.W is admitted for the 66-prefixed MOVQ, PINSRQ and PEXTRQ forms. *)
Definition aes_opcode_def:
  aes_opcode (b:word8) =
    if b = 0xDCw then SOME AESENC else
    if b = 0xDDw then SOME AESENCLAST else
    if b = 0xDEw then SOME AESDEC else
    if b = 0xDFw then SOME AESDECLAST else NONE
End

Definition decode_sse_def:
  decode_sse (p:word8) (rex:word8) [] = Truncated ∧
  decode_sse p rex (b::rest) =
    let bits = (word_bit 2 rex, word_bit 1 rex, word_bit 0 rex) in
      if word_bit 3 rex then
        (if p = 0x66w ∧ b = 0x7Ew then
           (case decode_reg_modrm bits rest of
              Decoded (x, RmReg r) n => Decoded (Movd S64 r x) (2 + n)
            | other => unmatched other)
         else if p = 0x66w ∧ b = 0x6Ew then
           (case decode_reg_modrm bits rest of
              Decoded (x, RmReg r) n => Decoded (MovqXmm x r) (2 + n)
            | other => unmatched other)
         else if p = 0x66w ∧ b = 0x3Aw then
           (case rest of
              [] => Truncated
            | op::operands =>
                if op = 0x22w ∨ op = 0x16w then
                  (case decode_modrm bits operands of
                     Decoded (x, scalar) n =>
                       (case DROP n operands of
                          imm::_ => Decoded (if op = 0x22w then Pinsrq x scalar imm
                                             else Pextrq scalar x imm) (4 + n)
                        | [] => Truncated)
                   | other => unmatched other)
                else Rejected)
         else Rejected)
      else if p = 0w ∧ b = 0x10w ∨ (p = 0xF3w ∨ p = 0x66w) ∧ b = 0x6Fw then
        (case decode_modrm bits rest of
           Decoded (x, RmMem a) n => Decoded (VecLoad (p = 0x66w) x a) (2 + n)
         | Decoded (x, RmReg y) n => if p = 0x66w then Decoded (VecMov x y) (2 + n) else Rejected
         | other => unmatched other)
      else if p = 0w ∧ b = 0x11w ∨ p = 0xF3w ∧ b = 0x7Fw then
        (case decode_modrm bits rest of
           Decoded (x, RmMem a) n => Decoded (VecStore a x) (2 + n)
         | other => unmatched other)
      else if p = 0w ∧ b = 0x57w then
        (case decode_reg_modrm bits rest of
           Decoded (d, RmReg x) n => Decoded (Pbinop PXOR d x) (2 + n)
         | other => unmatched other)
      else if p = 0x66w ∧ b = 0xEFw then
        (case decode_modrm bits rest of
           Decoded (d, RmReg x) n => Decoded (Pbinop PXOR d x) (2 + n)
         | Decoded (d, RmMem a) n => Decoded (PxorMem d a) (2 + n)
         | other => unmatched other)
      else if p = 0x66w ∧ b = 0x6Cw then
        (case decode_reg_modrm bits rest of
           Decoded (d, RmReg x) n => Decoded (Punpcklqdq d x) (2 + n)
         | other => unmatched other)
      else if p = 0x66w ∧ (b = 0x66w ∨ b = 0x76w) then
        (case decode_modrm bits rest of
           Decoded (d, src) n => Decoded (Pcmpd (b = 0x66w) d src) (2 + n)
         | other => unmatched other)
      else if p = 0x66w ∧ IS_SOME (sse_binop b) then
        (case decode_reg_modrm bits rest of
           Decoded (d, RmReg x) n => Decoded (Pbinop (THE (sse_binop b)) d x) (2 + n)
         | other => unmatched other)
      else if p = 0x66w ∧ b = 0xD7w then
        (case decode_reg_modrm bits rest of
           Decoded (r, RmReg x) n => Decoded (Pmovmskb r x) (2 + n)
         | other => unmatched other)
      else if p ≠ 0w ∧ b = 0x70w then
        (case decode_reg_modrm bits rest of
           Decoded (d, RmReg x) n =>
             (case DROP n rest of
                imm::_ =>
                  Decoded (if p = 0x66w then Pshufd d x imm else Pshufw (p = 0xF3w) d x imm)
                          (3 + n)
              | [] => Truncated)
         | other => unmatched other)
      else if p = 0x66w ∧ (b = 0x72w ∨ b = 0x73w) then
        (if word_bit 2 rex then Rejected
         else case decode_reg_modrm bits rest of
           Decoded (digit, RmReg x) n =>
             if digit ≠ 6w ∧ digit ≠ 2w ∧ (b = 0x72w ∨ digit ≠ 7w ∧ digit ≠ 3w) ∧
                (b = 0x73w ∨ digit ≠ 4w) then Rejected
             else
               (case DROP n rest of
                  imm::_ =>
                    Decoded (if digit = 7w ∨ digit = 3w then Pshiftdq (digit = 7w) x imm
                             else if digit = 4w then Psrad x imm
                             else Pshift (digit = 6w) (if b = 0x72w then S32 else S64) x imm)
                            (3 + n)
                | [] => Truncated)
         | other => unmatched other)
      else if p = 0x66w ∧ b = 0x38w then
        (case rest of
           [] => Truncated
         | op::rest' =>
             if op = 0w ∨ op = 0x10w then
               (case decode_modrm bits rest' of
                  Decoded (d, src) n =>
                    Decoded (if op = 0w then Pshufb d src else Pblendvb d src) (3 + n)
                | other => unmatched other)
             else if op = 0x21w ∨ op = 0x31w ∨ op = 0x25w ∨ op = 0x35w ∨ op = 0x20w ∨
                     op = 0x30w then
               (case decode_modrm bits rest' of
                  Decoded (d, RmMem a) n =>
                    Decoded (Pwiden (op = 0x21w ∨ op = 0x25w ∨ op = 0x20w)
                                    (if op = 0x21w ∨ op = 0x31w then S32
                                     else if op = 0x20w ∨ op = 0x30w then S16 else S64) d a)
                            (3 + n)
                | other => unmatched other)
             else if op = 0xDBw then
               (case decode_reg_modrm bits rest' of
                  Decoded (d, RmReg src) n => Decoded (AesImc d src) (3 + n)
                | other => unmatched other)
             else if IS_SOME (aes_opcode op) then
               (case decode_modrm bits rest' of
                  Decoded (d, src) n => Decoded (AesRound (THE (aes_opcode op)) d src) (3 + n)
                | other => unmatched other)
             else if op = 0x17w ∨ IS_SOME (sse4_binop op) then
               (case decode_reg_modrm bits rest' of
                  Decoded (d, RmReg src) n =>
                    Decoded (if op = 0x17w then Ptest d src else Pbinop (THE (sse4_binop op)) d src)
                            (3 + n)
                | other => unmatched other)
             else Rejected)
      else if p = 0x66w ∧ b = 0x3Aw then
        (case rest of
           [] => Truncated
         | op::rest' =>
             if op = 0x22w ∨ op = 0x16w then
               (case decode_modrm bits rest' of
                  Decoded (x, scalar) n =>
                    (case DROP n rest' of
                       imm::_ => Decoded (if op = 0x22w then Pinsrd x scalar imm
                                          else Pextrd scalar x imm) (4 + n)
                     | [] => Truncated)
                | other => unmatched other)
             else if op = 0x44w ∨ op = 0xDFw ∨ op = 0x0Fw then
               (case decode_reg_modrm bits rest' of
                  Decoded (d, RmReg src) n =>
                    (case DROP n rest' of
                       imm::_ =>
                         Decoded (if op = 0x44w then Pclmul d src imm
                                  else if op = 0xDFw then AesKeygen d src imm
                                  else Palignr d src imm) (4 + n)
                     | [] => Truncated)
                | other => unmatched other)
             else Rejected)
      else if p = 0x66w ∧ b = 0x7Ew then
        (case decode_reg_modrm bits rest of
           Decoded (x, RmReg r) n => Decoded (Movd S32 r x) (2 + n)
         | other => unmatched other)
      else if p = 0x66w ∧ b = 0x6Ew then
        (case decode_modrm bits rest of
           Decoded (x, src) n => Decoded (MovdXmm x src) (2 + n)
         | other => unmatched other)
      else Rejected
End

(* The F2 0F 38 forms, with the bytes after 0F. F0 without REX.W
   updates a dword from a byte; F1 with REX.W updates a qword from a
   qword register. The decoder excludes AH..BH, as for other byte forms. *)
Definition decode_crc32_def:
  decode_crc32 (rex:word8) [] = Truncated ∧
  decode_crc32 rex (b::rest) =
    let w = word_bit 3 rex;
        bits = (word_bit 2 rex, word_bit 1 rex, word_bit 0 rex) in
      if b ≠ 0x38w then Rejected
      else case rest of
        [] => Truncated
      | op::operands =>
          if ¬w ∧ op = 0xF0w then
            (case decode_modrm bits operands of
               Decoded (d, RmMem a) n => Decoded (Crc32 S8 d (RmMem a)) (3 + n)
             | Decoded (d, RmReg x) n =>
                 if byte_reg_ok rex x then Decoded (Crc32 S8 d (RmReg x)) (3 + n) else Rejected
             | other => unmatched other)
          else if w ∧ op = 0xF1w then
            (case decode_reg_modrm bits operands of
               Decoded (d, RmReg x) n => Decoded (Crc32 S64 d (RmReg x)) (3 + n)
             | other => unmatched other)
          else Rejected
End

(* The REX.W 0F 38 forms, with the bytes from the third opcode on. *)
Definition decode_0f38_def:
  decode_0f38 prefixes bits [] = Truncated ∧
  decode_0f38 prefixes bits (b::rest) =
    if b = 0xF6w ∧ (prefixes = [0x66w] ∨ prefixes = [0xF3w]) then
      (case decode_reg_modrm bits rest of
         Decoded (d, RmReg src) n => Decoded (Adx (prefixes = [0xF3w]) d src) (3 + n)
       | other => unmatched other)
    else if prefixes = [] ∧ (b = 0xF0w ∨ b = 0xF1w) then
      (case decode_modrm bits rest of
         Decoded (r, RmMem a) n =>
           Decoded (if b = 0xF0w then MovbeLoad r a else MovbeStore a r) (3 + n)
       | other => unmatched other)
    else Rejected
End

(* The two-byte opcodes 0F b after the REX byte, with the bytes from b on
   and the number of bytes from the 0F on. *)
Definition decode_0f_def:
  decode_0f (rex:word8) [] = Truncated ∧
  decode_0f rex (b::rest) =
    let w = word_bit 3 rex; bits = (word_bit 2 rex, word_bit 1 rex, word_bit 0 rex) in
      if b = 0x10w ∨ b = 0x11w ∨ b = 0x57w then decode_sse 0w rex (b::rest)
      else if b = 0x84w ∨ b = 0x85w then
        (if rex ≠ 0w then Rejected
         else case displacement 2w rest of
                Decoded d n => Decoded (Jcc (w2w b) d) (2 + n)
              | other => unmatched other)
      else if b = 0xB6w ∨ b = 0xB7w then
        (if w then Rejected
         else case decode_modrm bits rest of
                Decoded (dst, RmMem a) n =>
                  Decoded (Movzx (if b = 0xB6w then S8 else S16) dst (RmMem a)) (2 + n)
              | Decoded (dst, RmReg src) n =>
                  if b = 0xB6w ∧ byte_reg_ok rex src then Decoded (Movzx S8 dst (RmReg src)) (2 + n)
                  else Rejected
              | other => unmatched other)
      else if b = 0x4Cw ∨ b = 0x42w then
        (if b = 0x42w ∧ ¬w then Rejected
         else case decode_reg_modrm bits rest of
                Decoded (dst, RmReg src) n =>
                  Decoded (Cmov (w2w b) (if w then S64 else S32) dst (RmReg src)) (2 + n)
              | other => unmatched other)
      else if b = 0xBEw then
        (if w then Rejected
         else case decode_reg_modrm bits rest of
                Decoded (dst, RmReg src) n =>
                  if byte_reg_ok rex src then Decoded (Movsx dst (RmReg src)) (2 + n) else Rejected
              | other => unmatched other)
      else if b = 0x92w ∨ b = 0x93w ∨ b = 0x94w ∨ b = 0x9Cw ∨ b = 0x9Fw then
        (if rex ≠ 0w ∧ rex ≠ 0x40w ∧ rex ≠ 0x41w then Rejected
         else case decode_reg_modrm bits rest of
                Decoded (reg, RmReg dst) n =>
                  if reg = 0w ∧ byte_reg_ok rex dst then Decoded (Setcc (w2w b) (RmReg dst)) (2 + n)
                  else Rejected
              | other => unmatched other)
      else if b = 0xAFw then
        (if ¬w then Rejected
         else case decode_modrm bits rest of
                Decoded (dst, src) n => Decoded (Imul dst src) (2 + n)
              | other => unmatched other)
      else if b = 0xA5w ∨ b = 0xADw then
        (if ¬w then Rejected
         else case decode_reg_modrm bits rest of
                Decoded (src, RmReg dst) n => Decoded (ShiftDouble (b = 0xA5w) dst src) (2 + n)
              | other => unmatched other)
      else if b && 0xF8w = 0xC8w then
        (if ¬w then Rejected else Decoded (Bswap (reg_num (word_bit 0 rex) (w2w b))) 2)
      else Rejected
End

(* F3 0F b at REX.W w, with the bytes from b on and the number of bytes
   from the 0F on: TZCNT, LZCNT and POPCNT on 64-bit registers, and TZCNT
   and POPCNT on 32-bit ones. *)
Definition decode_bitcount_def:
  decode_bitcount w bits [] = Truncated ∧
  decode_bitcount w bits (b::rest) =
    if b = 0xBCw ∨ b = 0xB8w ∨ w ∧ b = 0xBDw then
      (case decode_reg_modrm bits rest of
         Decoded (d, RmReg src) n =>
           Decoded (BitCount (if b = 0xBCw then TZCNT else if b = 0xBDw then LZCNT else POPCNT)
                             (if w then S64 else S32) d src) (2 + n)
       | other => unmatched other)
    else Rejected
End

(* The r/m8, r8 operands of 88 and 38 with a memory r/m, after the REX
   byte: the r8 register and the address. *)
Definition decode_byte_mem_def:
  decode_byte_mem (rex:word8) bits [] = Truncated ∧
  decode_byte_mem rex bits (modrm::rest) =
    if ¬byte_reg_ok rex ((5 >< 3) modrm) then Rejected
    else case decode_modrm bits (modrm::rest) of
           Decoded (src, RmMem a) n => Decoded (src, a) n
         | other => unmatched other
End

(* The VEX-encoded BMI1 and BMI2 forms after a C4 byte, with the number of
   bytes from the C4 on: the first VEX byte holds the inverted R, X and B
   bits and the opcode map (2: 0F38, 3: 0F3A), the second W, the inverted
   register vvvv, L and the implied prefix pp (0: none, 1: 66, 2: F3, 3:
   F2). Only W1 forms with L = 0, register operands but MULX's source,
   and RORX at either width are modelled; the other maps, L = 1, W0 in map
   0F38 and RORX with vvvv in use are rejected from the byte that holds
   them. *)
Definition decode_vex_def:
  decode_vex [] = Truncated ∧
  decode_vex (b1::rest) =
    let mmap = (4 >< 0) b1 : word5 in
      if mmap ≠ 2w ∧ mmap ≠ 3w then Rejected
      else case rest of
        [] => Truncated
      | b2::rest' =>
          let w = word_bit 7 b2; v = ¬((6 >< 3) b2) : word4; pp = (1 >< 0) b2 : word2;
              bits = (¬word_bit 7 b1, ¬word_bit 6 b1, ¬word_bit 5 b1)
          in
            if word_bit 2 b2 ∨ (if mmap = 2w then ¬w else pp ≠ 3w ∨ v ≠ 0w) then Rejected
            else case rest' of
              [] => Truncated
            | op::modrm =>
                if mmap = 3w then
                  (if op ≠ 0xF0w then Rejected
                   else case decode_reg_modrm bits modrm of
                          Decoded (d, RmReg src) n =>
                            (case DROP n modrm of
                               imm::_ => Decoded (Rorx (if w then S64 else S32) d src imm) (5 + n)
                             | [] => Truncated)
                        | other => unmatched other)
                else if op = 0xF6w ∧ pp = 3w then
                  (case decode_modrm bits modrm of
                     Decoded (hi, src) n => Decoded (Mulx hi v src) (4 + n)
                   | other => unmatched other)
                else if op = 0xF7w then
                  (case decode_reg_modrm bits modrm of
                     Decoded (d, RmReg src) n =>
                       Decoded (if pp = 0w then Bextr d src v
                                else ShiftX (if pp = 1w then SHL else if pp = 3w then SHR else SAR)
                                            d src v) (4 + n)
                   | other => unmatched other)
                else if op = 0xF5w ∧ pp ≠ 1w then
                  (case decode_reg_modrm bits modrm of
                     Decoded (d, RmReg src) n =>
                       Decoded (if pp = 0w then Bzhi d src v
                                else Pdep (if pp = 3w then PDEP else PEXT) d v src) (4 + n)
                   | other => unmatched other)
                else if op = 0xF2w ∧ pp = 0w then
                  (case decode_reg_modrm bits modrm of
                     Decoded (d, RmReg src) n => Decoded (Andn d v src) (4 + n)
                   | other => unmatched other)
                else if op = 0xF3w ∧ pp = 0w ∧ word_bit 7 b1 then
                  (case decode_reg_modrm bits modrm of
                     Decoded (digit, RmReg src) n =>
                       if digit = 1w then Decoded (Bls BLSR v src) (4 + n)
                       else if digit = 2w then Decoded (Bls BLSMSK v src) (4 + n)
                       else if digit = 3w then Decoded (Bls BLSI v src) (4 + n)
                       else Rejected
                   | other => unmatched other)
                else Rejected
End

(* No F2 or F3 among the prefixes. *)
Definition no_rep_def:
  no_rep [] = T ∧
  no_rep (b::bs) = (b ≠ (0xF2w:word8) ∧ b ≠ 0xF3w ∧ no_rep bs)
End

(* Whether an opcode can still complete an instruction after the legacy
   prefixes and the REX byte (rex = 0w when absent or not yet fetched):
   with legacy prefixes, only the nops (66 and 2E, no REX), 66 89, the
   vector forms (a lone 66, F2 or F3; REX.W only after 66), the bit
   counts (a lone F3), the ADX forms (66 or F3, REX.W) and CRC32
   (a lone F2, with REX.W for the qword form) are modelled. *)
Definition prefixes_ok_def:
  prefixes_ok prefixes (rex:word8) ⇔
    prefixes = [] ∨ no_rep prefixes ∧ rex = 0w ∨ prefixes = [0xF3w] ∨ prefixes = [0x66w] ∨
    prefixes = [0xF2w]
End

(* The instruction after the legacy prefixes and the REX byte (rex = 0w
   when absent), with the number of bytes from the opcode on. F2 before
   0F 38 selects CRC32. A lone 66, F2 (without REX.W) or F3 before 0F
   can be a vector form's mandatory prefix. Before 0F BC and
   0F B8, or with REX.W, F3 is a bit count's, except 66 before the 0F 1F
   nop; with no byte after 0F, 66 is
   the nop's prefix unless a REX byte rules the nop out. *)
Definition decode_opcode_def:
  decode_opcode prefixes (rex:word8) [] =
    (if prefixes_ok prefixes rex then Truncated else Rejected) ∧
  decode_opcode prefixes rex (op::rest) =
    let legacy = (prefixes ≠ []);
        w = word_bit 3 rex; bits = (word_bit 2 rex, word_bit 1 rex, word_bit 0 rex);
        sz = if w then S64 else S32;
        rb = reg_num (word_bit 0 rex) (w2w op)
    in
      if op = 0x0Fw ∧ w ∧
         (prefixes = [] ∨ prefixes = [0x66w] ∨ prefixes = [0xF3w]) ∧
         (case rest of b::_ => b = 0x38w | [] => F) then
        decode_0f38 prefixes bits (TL rest)
      else if op = 0x0Fw ∧ prefixes = [0xF2w] ∧
         (w ∨ case rest of b::_ => b = 0x38w | [] => F) then
        decode_crc32 rex rest
      else if op = 0x0Fw ∧ prefixes = [0xF3w] ∧
         (w ∨ case rest of b::_ => b = 0xBCw ∨ b = 0xB8w | [] => F) then
        decode_bitcount w bits rest
      else if op = 0x0Fw ∧
         (prefixes = [0xF2w] ∧ ¬w ∨ prefixes = [0xF3w] ∨
          prefixes = [0x66w] ∧ (case rest of b::_ => b ≠ 0x1Fw | [] => rex ≠ 0w)) then
        decode_sse (HD prefixes) rex rest
      else if op = 0x0Fw ∧ rex = 0w ∧ no_rep prefixes ∧ (legacy ∨ decode_nop rest ≠ Rejected) then
        decode_nop rest
      else if prefixes = [0x66w] ∧ op = 0x89w ∧ ¬w then
        (case decode_modrm bits rest of
           Decoded (src, RmMem a) n => Decoded (Mov S16 (RmMem a) (RmReg src)) (1 + n)
         | other => unmatched other)
      else if prefixes = [0x66w] ∧ op = 0x90w ∧ rex = 0w then Decoded Nop 1
      else if legacy then Rejected
      else if op = 0xC4w then (if rex ≠ 0w then Rejected else decode_vex rest)
      else if op && 0xF8w = 0xB8w then
        (if w then
           (if LENGTH rest < 8 then Truncated else Decoded (MovImm64 rb (le_word (TAKE 8 rest))) 9)
         else if LENGTH rest < 4 then Truncated
         else Decoded (MovImm rb (w2w (le_word (TAKE 4 rest)))) 5)
      else if op = 0x0Dw then
        (if rex ≠ 0w then Rejected
         else if LENGTH rest < 4 then Truncated
         else Decoded (BinopImm OR S32 (RmReg 0w) (sw2sw (w2w (le_word (TAKE 4 rest)) : word32))) 5)
      else if op = 0x81w then
        (if w then Rejected else
         case rest of
           [] => Truncated
         | modrm::_ =>
             if (5 >< 3) modrm ≠ (6w:word3) then Rejected
             else case decode_reg_modrm bits rest of
                    Decoded (reg, RmReg dst) n =>
                      if LENGTH (DROP n rest) < 4 then Truncated
                      else Decoded (BinopImm XOR S32 (RmReg dst)
                                      (sw2sw (w2w (le_word (TAKE 4 (DROP n rest))) : word32)))
                                   (5 + n)
                  | other => unmatched other)
      else if op = 0xC7w then
        (if ¬w then Rejected else
         case rest of
           [] => Truncated
         | modrm::_ =>
             if (5 >< 3) modrm ≠ (0w:word3) then Rejected
             else case decode_reg_modrm bits rest of
                    Decoded (reg, RmReg dst) n =>
                      if LENGTH (DROP n rest) < 4 then Truncated
                      else Decoded (MovImm64 dst
                                      (sw2sw (w2w (le_word (TAKE 4 (DROP n rest))) : word32)))
                                   (5 + n)
                  | other => unmatched other)
      else if op = 0x80w then
        (if w then Rejected else
         case rest of
           [] => Truncated
         | modrm::_ =>
             if (5 >< 3) modrm ≠ (7w:word3) then Rejected
             else case decode_reg_modrm bits rest of
                    Decoded (reg, RmReg dst) n =>
                      if ¬byte_reg_ok rex dst then Rejected
                      else (case DROP n rest of
                              imm::_ => Decoded (BinopImm CMP S8 (RmReg dst) (sw2sw imm)) (2 + n)
                            | [] => Truncated)
                  | other => unmatched other)
      else if op && 0xF8w = 0x50w then
        (if rex = 0w ∨ rex = 0x41w then Decoded (Push rb) 1 else Rejected)
      else if op && 0xF8w = 0x58w then
        (if rex = 0w ∨ rex = 0x41w then Decoded (Pop rb) 1 else Rejected)
      else if op = 0x90w then (if rex = 0w then Decoded Nop 1 else Rejected)
      else if op = 0x98w then (if rex = 0x48w then Decoded Cdqe 1 else Rejected)
      else if op = 0x99w then (if rex = 0x48w then Decoded Cqo 1 else Rejected)
      else if op = 0xC3w then (if rex = 0w then Decoded Ret 1 else Rejected)
      else if op = 0xE8w then
        (if rex ≠ 0w then Rejected
         else case displacement 2w rest of
                Decoded d n => Decoded (Call d) (1 + n)
              | other => unmatched other)
      else if op = 0x73w ∨ op = 0x74w ∨ op = 0x75w ∨ op = 0x76w ∨ op = 0x77w ∨ op = 0x79w then
        (if rex ≠ 0w then Rejected
         else case rest of d::_ => Decoded (Jcc (w2w op) (sw2sw d)) 2 | [] => Truncated)
      else if op = 0xEBw then
        (if rex ≠ 0w then Rejected
         else case rest of d::_ => Decoded (Jmp (sw2sw d)) 2 | [] => Truncated)
      else if op = 0x0Fw then decode_0f rex rest
      else if op = 0x89w then
        (case decode_modrm bits rest of
           Decoded (src, dst) n => Decoded (Mov sz dst (RmReg src)) (1 + n)
         | other => unmatched other)
      else if op = 0x8Bw then
        (case decode_modrm bits rest of
           Decoded (dst, RmMem a) n => Decoded (Mov sz (RmReg dst) (RmMem a)) (1 + n)
         | other => unmatched other)
      else if op = 0x88w ∨ op = 0x38w then
        (if w then Rejected
         else case decode_byte_mem rex bits rest of
                Decoded (src, a) n =>
                  Decoded (if op = 0x88w then Mov S8 (RmMem a) (RmReg src)
                           else Binop CMP S8 (RmMem a) (RmReg src)) (1 + n)
              | other => unmatched other)
      else if op = 0x30w ∨ op = 0x28w ∨ op = 0x84w then
        (if w then Rejected
         else case decode_reg_modrm bits rest of
                Decoded (src, RmReg dst) n =>
                  if byte_reg_ok rex src ∧ byte_reg_ok rex dst then
                    Decoded (Binop (if op = 0x30w then XOR else if op = 0x28w then SUB else TEST)
                                   S8 (RmReg dst) (RmReg src)) (1 + n)
                  else Rejected
              | other => unmatched other)
      else if op = 0x39w ∧ w then
        (case decode_modrm bits rest of
           Decoded (src, dst) n => Decoded (Binop CMP S64 dst (RmReg src)) (1 + n)
         | other => unmatched other)
      else if op = 0x8Dw then
        (if ¬w then Rejected
         else case decode_modrm bits rest of
                Decoded (dst, RmMem a) n => Decoded (Lea dst a) (1 + n)
              | other => unmatched other)
      else if op = 0x63w then
        (if ¬w then Rejected
         else case decode_modrm bits rest of
                Decoded (dst, src) n => Decoded (Movsxd dst src) (1 + n)
              | other => unmatched other)
      else if op = 0x83w then
        (case rest of
           [] => Truncated
         | modrm::_ =>
             case imm_binop w ((5 >< 3) modrm) ((7 >< 6) modrm = (3w:word2)) of
               NONE => Rejected
             | SOME bop =>
                 case decode_modrm bits rest of
                   Decoded (reg, dst) n =>
                     (case DROP n rest of
                        imm::_ => Decoded (BinopImm bop sz dst (sw2sw imm)) (2 + n)
                      | [] => Truncated)
                 | other => unmatched other)
      else if op = 0xF7w then
        (case decode_reg_modrm bits rest of
           Decoded (reg, RmReg dst) n =>
             let digit = (w2w reg : word3) in
               if digit = 2w then Decoded (Not sz (RmReg dst)) (1 + n)
               else if digit = 3w ∧ ¬w then Decoded (Neg S32 (RmReg dst)) (1 + n)
               else if (digit = 4w ∨ digit = 5w) ∧ w then Decoded (MulWide (digit = 5w) dst) (1 + n)
               else if digit = 6w then Decoded (Div F sz dst) (1 + n)
               else if digit = 7w ∧ w then Decoded (Div T S64 dst) (1 + n)
               else Rejected
         | other => unmatched other)
      else if op = 0xFFw then
        (if ¬w ∧ rex ≠ 0w ∧ rex ≠ 0x41w then Rejected
         else case decode_reg_modrm bits rest of
                Decoded (reg, RmReg dst) n =>
                  if (w2w reg : word3) = 0w ∧ w then Decoded (Inc S64 (RmReg dst)) (1 + n)
                  else if (w2w reg : word3) = 1w ∧ w then Decoded (Dec64 dst) (1 + n)
                  else if (w2w reg : word3) = 4w ∧ ¬w then Decoded (JmpReg dst) (1 + n)
                  else Rejected
              | other => unmatched other)
      else if op = 0xC1w then
        (case decode_reg_modrm bits rest of
           Decoded (reg, RmReg dst) n =>
             if (w2w reg : word3) = 5w ∨ (w2w reg : word3) = 7w ∧ w then
               (case DROP n rest of
                  imm::_ =>
                    Decoded (Shift (if (w2w reg : word3) = 5w then SHR else SAR) sz
                                   (RmReg dst) (SOME imm)) (2 + n)
                | [] => Truncated)
             else if (w2w reg : word3) = 0w ∧ ¬w then
               (case DROP n rest of
                  imm::_ => Decoded (Rotate T S32 dst (SOME imm)) (2 + n)
                | [] => Truncated)
             else Rejected
         | other => unmatched other)
      else if op = 0xD1w then
        (if ¬w then Rejected
         else case decode_reg_modrm bits rest of
                Decoded (reg, RmReg dst) n =>
                  if (w2w reg : word3) = 5w then Decoded (Shift SHR S64 (RmReg dst) (SOME 1w)) (1 + n)
                  else Rejected
              | other => unmatched other)
      else if op = 0xD3w then
        (case decode_reg_modrm bits rest of
           Decoded (reg, RmReg dst) n =>
             if (w2w reg : word3) = 4w then Decoded (Shift SHL sz (RmReg dst) NONE) (1 + n)
             else if (w2w reg : word3) = 5w ∧ w then Decoded (Shift SHR S64 (RmReg dst) NONE) (1 + n)
             else if (w2w reg : word3) = 7w ∧ ¬w then
               Decoded (Shift SAR S32 (RmReg dst) NONE) (1 + n)
             else if (w2w reg : word3) = 1w ∧ w then Decoded (Rotate F S64 dst NONE) (1 + n)
             else Rejected
         | other => unmatched other)
      else
        case rm_binop op w of
          SOME bop =>
            (case decode_modrm bits rest of
               Decoded (dst, RmMem a) n => Decoded (Binop bop sz (RmReg dst) (RmMem a)) (1 + n)
             | other => unmatched other)
        | NONE =>
            case rr_binop op w of
              NONE => Rejected
            | SOME bop =>
                case decode_reg_modrm bits rest of
                  Decoded (src, RmReg dst) n =>
                    Decoded (Binop bop sz (RmReg dst) (RmReg src)) (1 + n)
                | other => unmatched other
End

(* An instruction and its length in bytes, at most 15. *)
Definition decode_def:
  decode bytes =
    let (prefixes, rest) = split_prefixes bytes;
        p = LENGTH prefixes
    in
      case rest of
        [] => if prefixes_ok prefixes 0w then Truncated else Rejected
      | b::rest' =>
          let decoded =
                if b && 0xF0w = 0x40w then
                  (case decode_opcode prefixes b rest' of
                     Decoded i n => Decoded i (p + 1 + n)
                   | other => other)
                else
                  (case decode_opcode prefixes 0w rest of
                     Decoded i n => Decoded i (p + n)
                   | other => other)
          in
            case decoded of
              Decoded i n => if n ≤ 15 then Decoded i n else Rejected
            | other => other
End

(* Semantics *)

Definition read_reg_def:
  read_reg ops s r = ops.get_reg s.regs r
End

Definition write_reg_def:
  write_reg ops r v s = s with regs := ops.put_reg r v s.regs
End

Definition read_xmm_def:
  read_xmm ops s x = ops.get_xmm s.xmm x
End

Definition write_xmm_def:
  write_xmm ops x v s = s with xmm := ops.put_xmm x v s.xmm
End

(* Lane i of four 32-bit lanes, and the vector of four lanes, lane 0 lowest. *)
Definition lane32_def:
  lane32 (i:num) (v:word128) : word32 = w2w (v >>> (32 * i))
End

Definition lanes32_def:
  lanes32 (l0:word32) (l1:word32) (l2:word32) (l3:word32) : word128 =
    w2w l0 ‖ (w2w l1 << 32) ‖ (w2w l2 << 64) ‖ (w2w l3 << 96)
End

Theorem lane32_packed:
  (∀i. i < 4 ⇒
    lane32 i (lanes32 a b c d) = if i = 0 then a else if i = 1 then b else if i = 2 then c else d)
Proof
  CONV_TAC (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) []))) >>
  simp[lane32_def, lanes32_def] >>
  rpt conj_tac >> blastLib.BBLAST_TAC
QED

Theorem lane32_low_widen:
  lane32 0 (w2w (x:word32)) = x
Proof
  simp[lane32_def] >> blastLib.BBLAST_TAC
QED

Definition paddd_def:
  paddd a b =
    lanes32 (lane32 0 a + lane32 0 b) (lane32 1 a + lane32 1 b)
            (lane32 2 a + lane32 2 b) (lane32 3 a + lane32 3 b)
End

(* Two 64-bit lane sums. *)
Definition paddq_def:
  paddq (a:word128) (b:word128) =
    (w2w (w2w a + w2w b : word64) : word128) ‖
    (w2w (w2w (a >>> 64) + w2w (b >>> 64) : word64) << 64)
End

(* The low n bytes of the PCMPEQB result: all ones where a and b agree. *)
Definition bytes_eq_def:
  bytes_eq 0 (a:word128) (b:word128) = 0w : word128 ∧
  bytes_eq (SUC n) a b =
    bytes_eq n a b ‖
    (if (w2w (a >>> (8 * n)) : word8) = w2w (b >>> (8 * n)) then 0xFFw << (8 * n) else 0w)
End

(* Bit i is the top bit of byte i of v, for the low n bytes. *)
Definition byte_signs_def:
  byte_signs 0 (v:word128) = 0w : word64 ∧
  byte_signs (SUC n) v = byte_signs n v ‖ (if word_bit (8 * n + 7) v then 1w << n else 0w)
End

(* Lane i of two 64-bit lanes, and the vector of two lanes, lane 0 lowest. *)
Definition lane64_def:
  lane64 (i:num) (v:word128) : word64 = w2w (v >>> (64 * i))
End

Definition lanes64_def:
  lanes64 (l0:word64) (l1:word64) : word128 = w2w l0 ‖ (w2w l1 << 64)
End

Theorem lanes64_extract:
  lane64 0 (lanes64 lo hi) = lo ∧ lane64 1 (lanes64 lo hi) = hi
Proof
  simp[lane64_def, lanes64_def] >> blastLib.BBLAST_TAC
QED

Theorem word_bit_lane64:
  word_bit j (lane64 i v) ⇔ j < 64 ∧ word_bit (64 * i + j) v
Proof
  `j + 64 * i = 64 * i + j` by decide_tac >>
  Cases_on `j < 64`
  >- (`j < 128` by decide_tac >>
      asm_simp_tac bool_ss [lane64_def, word_bit_thm, dimindex_64, dimindex_128,
        w2w, word_lsr_def, fcpTheory.FCP_BETA]) >>
  simp[word_bit_thm, dimindex_64]
QED

Theorem word_bit_lanes64:
  word_bit j (lanes64 lo hi) ⇔
    if j < 64 then word_bit j lo else word_bit (j - 64) hi
Proof
  PURE_REWRITE_TAC [lanes64_def, word_bit_or, word_bit_lsl] >>
  PURE_REWRITE_TAC [word_bit_thm, dimindex_64, dimindex_128] >>
  Cases_on `j < 64`
  >- (`j < 128 ∧ ¬(64 ≤ j)` by decide_tac >>
      asm_simp_tac bool_ss [w2w, dimindex_64, dimindex_128]) >>
  Cases_on `j < 128`
  >- (`64 ≤ j ∧ j - 64 < 64 ∧ j - 64 < 128` by decide_tac >>
      asm_simp_tac bool_ss [w2w, dimindex_64, dimindex_128]) >>
  `¬(j - 64 < 64)` by decide_tac >> simp[]
QED

(* The low product, unsigned or signed minimum/maximum or difference of a
   pair of dwords, or the absolute value of the second (PABSD; INT32_MIN
   stays). *)
Definition sse4_lane_def:
  sse4_lane op (a:word32) b =
    case op of
      PMULLD => a * b
    | PMINUD => if a <₊ b then a else b
    | PMAXUD => if a <₊ b then b else a
    | PSUBD => a - b
    | PABSD => if b < 0w then -b else b
    | PMINSD => if a < b then a else b
    | PMAXSD => if a < b then b else a
    | _ => a
End

Definition sse4_lanes_def:
  sse4_lanes op a b =
    lanes32 (sse4_lane op (lane32 0 a) (lane32 0 b))
            (sse4_lane op (lane32 1 a) (lane32 1 b))
            (sse4_lane op (lane32 2 a) (lane32 2 b))
            (sse4_lane op (lane32 3 a) (lane32 3 b))
End

(* Sums of adjacent dword pairs, a's below b's. *)
Definition phaddd_def:
  phaddd a b =
    lanes32 (lane32 0 a + lane32 1 a) (lane32 2 a + lane32 3 a)
            (lane32 0 b + lane32 1 b) (lane32 2 b + lane32 3 b)
End

Theorem dword_horizontal_sum:
  lane32 0 (phaddd (phaddd v v) (phaddd v v)) =
    (lane32 0 v + lane32 1 v) + (lane32 2 v + lane32 3 v)
Proof
  simp[phaddd_def, lane32_packed]
QED

(* All ones where a is greater than b, signed. *)
Definition pcmpgtq_lane_def:
  pcmpgtq_lane (a:word64) b = if b < a then -1w else 0w : word64
End

(* v with dword lane i replaced by x. *)
Definition insert_lane32_def:
  insert_lane32 (i:num) v x =
    lanes32 (if i = 0 then x else lane32 0 v) (if i = 1 then x else lane32 1 v)
            (if i = 2 then x else lane32 2 v) (if i = 3 then x else lane32 3 v)
End

(* The full 64-bit product of two dwords, signed or unsigned. *)
Definition mul32_def:
  mul32 signed (a:word32) (b:word32) : word64 =
    if signed then sw2sw a * sw2sw b else w2w a * w2w b
End

(* PMULDQ (signed) and PMULUDQ: the products of dword lanes 0 and 2. *)
Definition pmul_even_def:
  pmul_even signed a b =
    lanes64 (mul32 signed (lane32 0 a) (lane32 0 b)) (mul32 signed (lane32 2 a) (lane32 2 b))
End

(* A signed dword saturated to an unsigned (PACKUSDW) or signed word. *)
Definition sat16_def:
  sat16 unsigned (x:word32) : word16 =
    if unsigned then (if x < 0w then 0w else if 0xFFFFw < x then 0xFFFFw else w2w x)
    else if x < 0xFFFF8000w then 0x8000w else if 0x7FFFw < x then 0x7FFFw else w2w x
End

(* Dwords i and i + 1 of v, saturated, as the low and high words of a dword. *)
Definition sat_pair_def:
  sat_pair unsigned v i : word32 =
    w2w (sat16 unsigned (lane32 i v)) ‖ (w2w (sat16 unsigned (lane32 (i + 1) v)) << 16)
End

(* PACKUSDW (unsigned) and PACKSSDW: a's four dwords saturated into the low
   four words, b's into the high four. *)
Definition pack_dwords_def:
  pack_dwords unsigned a b =
    lanes32 (sat_pair unsigned a 0) (sat_pair unsigned a 2)
            (sat_pair unsigned b 0) (sat_pair unsigned b 2)
End

Theorem pack_dwords_lanes:
  ∀i. i < 4 ⇒
    (w2w (pack_dwords unsigned a b >>> (16 * i)):word16) =
      sat16 unsigned (lane32 i a) ∧
    (w2w (pack_dwords unsigned a b >>> (16 * (4 + i))):word16) =
      sat16 unsigned (lane32 i b)
Proof
  CONV_TAC (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) []))) >>
  simp[pack_dwords_def, lanes32_def, sat_pair_def] >>
  rpt conj_tac >> blastLib.BBLAST_TAC
QED

(* Lane i of eight 16-bit or sixteen 8-bit lanes, lane 0 lowest, and the
   dword of two words, lo lowest. *)
Definition lane16_def:
  lane16 (i:num) (v:word128) : word16 = w2w (v >>> (16 * i))
End

Definition lane8_def:
  lane8 (i:num) (v:word128) : word8 = w2w (v >>> (8 * i))
End

Definition words32_def:
  words32 (lo:word16) (hi:word16) : word32 = w2w lo ‖ (w2w hi << 16)
End

(* PMADDWD dword i: the sum of the signed products of words 2i and 2i + 1.
   It wraps to 0x80000000w only when all four words are -32768. *)
Definition madd_pair_def:
  madd_pair a b i : word32 =
    sw2sw (lane16 (2 * i) a) * sw2sw (lane16 (2 * i) b) +
    sw2sw (lane16 (2 * i + 1) a) * sw2sw (lane16 (2 * i + 1) b)
End

Definition pmaddwd_def:
  pmaddwd a b = lanes32 (madd_pair a b 0) (madd_pair a b 1) (madd_pair a b 2) (madd_pair a b 3)
End

(* PMADDUBSW word i: the products of a's unsigned and b's signed bytes 2i
   and 2i + 1, summed exactly in 32 bits and saturated to a signed word. *)
Definition maddubs_word_def:
  maddubs_word a b i : word16 =
    sat16 F (w2w (lane8 (2 * i) a) * sw2sw (lane8 (2 * i) b) +
             w2w (lane8 (2 * i + 1) a) * sw2sw (lane8 (2 * i + 1) b))
End

Definition pmaddubsw_def:
  pmaddubsw a b =
    lanes32 (words32 (maddubs_word a b 0) (maddubs_word a b 1))
            (words32 (maddubs_word a b 2) (maddubs_word a b 3))
            (words32 (maddubs_word a b 4) (maddubs_word a b 5))
            (words32 (maddubs_word a b 6) (maddubs_word a b 7))
End

(* A signed word saturated to an unsigned byte. *)
Definition sat8_def:
  sat8 (x:word16) : word8 = if x < 0w then 0w else if 0xFFw < x then 0xFFw else w2w x
End

(* Words i..i + 3 of v, saturated, as the bytes of a dword. *)
Definition sat_quad_def:
  sat_quad v i : word32 =
    w2w (sat8 (lane16 i v)) ‖ (w2w (sat8 (lane16 (i + 1) v)) << 8) ‖
    (w2w (sat8 (lane16 (i + 2) v)) << 16) ‖ (w2w (sat8 (lane16 (i + 3) v)) << 24)
End

(* PACKUSWB: a's eight words saturated into the low eight bytes, b's into
   the high eight. *)
Definition pack_words_def:
  pack_words a b = lanes32 (sat_quad a 0) (sat_quad a 4) (sat_quad b 0) (sat_quad b 4)
End

Theorem pmaddwd_lanes:
  ∀i. i < 4 ⇒ lane32 i (pmaddwd a b) = madd_pair a b i
Proof
  rw[pmaddwd_def, lane32_packed] >> `i = 3` by decide_tac >> simp[]
QED

Theorem pmaddubsw_lanes:
  ∀i. i < 8 ⇒ lane16 i (pmaddubsw a b) = maddubs_word a b i
Proof
  CONV_TAC (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) []))) >>
  simp[pmaddubsw_def, lanes32_def, words32_def, lane16_def] >>
  rpt conj_tac >> blastLib.BBLAST_TAC
QED

Theorem pack_words_lanes:
  ∀i. i < 8 ⇒
    lane8 i (pack_words a b) = sat8 (lane16 i a) ∧
    lane8 (8 + i) (pack_words a b) = sat8 (lane16 i b)
Proof
  CONV_TAC (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) []))) >>
  simp[pack_words_def, lanes32_def, sat_quad_def, lane8_def] >>
  rpt conj_tac >> blastLib.BBLAST_TAC
QED

(* PAVGB, PADDUSB and PSUBUSB on a pair of unsigned bytes: the average
   rounded up, and the sum and difference clamped to 0..255 (num
   subtraction stops at 0). *)
Definition byte_lane_def:
  byte_lane op (x:word8) (y:word8) : word8 =
    case op of
      PAVGB => n2w ((w2n x + w2n y + 1) DIV 2)
    | PADDUSB => n2w (MIN 255 (w2n x + w2n y))
    | PSUBUSB => n2w (w2n x - w2n y)
    | _ => x
End

(* Bytes i..i + 3 of the byte operation, as a dword. *)
Definition byte_quad_def:
  byte_quad op a b i : word32 =
    w2w (byte_lane op (lane8 i a) (lane8 i b)) ‖
    (w2w (byte_lane op (lane8 (i + 1) a) (lane8 (i + 1) b)) << 8) ‖
    (w2w (byte_lane op (lane8 (i + 2) a) (lane8 (i + 2) b)) << 16) ‖
    (w2w (byte_lane op (lane8 (i + 3) a) (lane8 (i + 3) b)) << 24)
End

Definition byte_lanes_def:
  byte_lanes op a b =
    lanes32 (byte_quad op a b 0) (byte_quad op a b 4) (byte_quad op a b 8) (byte_quad op a b 12)
End

(* PAVGW: the average of two unsigned words, rounded up. *)
Definition avg16_def:
  avg16 (x:word16) (y:word16) : word16 = n2w ((w2n x + w2n y + 1) DIV 2)
End

Definition pavgw_def:
  pavgw a b =
    lanes32 (words32 (avg16 (lane16 0 a) (lane16 0 b)) (avg16 (lane16 1 a) (lane16 1 b)))
            (words32 (avg16 (lane16 2 a) (lane16 2 b)) (avg16 (lane16 3 a) (lane16 3 b)))
            (words32 (avg16 (lane16 4 a) (lane16 4 b)) (avg16 (lane16 5 a) (lane16 5 b)))
            (words32 (avg16 (lane16 6 a) (lane16 6 b)) (avg16 (lane16 7 a) (lane16 7 b)))
End

(* EVAL runs ABS_DIFF, which arithmetic leaves out of the compset. *)
val () = computeLib.add_persistent_funs ["arithmetic.ABS_DIFF_def"];

(* The sum of |a_j - b_j| over the unsigned bytes j = i..i + 7. *)
Definition sad8_def:
  sad8 a b i =
    ABS_DIFF (w2n (lane8 i a)) (w2n (lane8 i b)) +
    ABS_DIFF (w2n (lane8 (i + 1) a)) (w2n (lane8 (i + 1) b)) +
    ABS_DIFF (w2n (lane8 (i + 2) a)) (w2n (lane8 (i + 2) b)) +
    ABS_DIFF (w2n (lane8 (i + 3) a)) (w2n (lane8 (i + 3) b)) +
    ABS_DIFF (w2n (lane8 (i + 4) a)) (w2n (lane8 (i + 4) b)) +
    ABS_DIFF (w2n (lane8 (i + 5) a)) (w2n (lane8 (i + 5) b)) +
    ABS_DIFF (w2n (lane8 (i + 6) a)) (w2n (lane8 (i + 6) b)) +
    ABS_DIFF (w2n (lane8 (i + 7) a)) (w2n (lane8 (i + 7) b))
End

(* PSADBW: bytes 0..7's sum in the low qword, bytes 8..15's in the high.
   Each is at most 8 * 255, so bits 63:16 of each qword are 0. *)
Definition psadbw_def:
  psadbw a b = lanes64 (n2w (sad8 a b 0)) (n2w (sad8 a b 8))
End

(* The least of words i..7 of v and m, and its index, k for m: the first
   index wins a tie. *)
Definition minpos_aux_def:
  minpos_aux v (i:num) (m:word16) (k:num) =
    if 8 ≤ i then (m, k)
    else if lane16 i v <₊ m then minpos_aux v (i + 1) (lane16 i v) i
    else minpos_aux v (i + 1) m k
Termination
  WF_REL_TAC `measure (λ(v, i, m, k). 8 - i)`
End

(* PHMINPOSUW: the least unsigned word of v in bits 15:0, the lowest index
   holding it in bits 18:16, and zeros above. *)
Definition phminposuw_def:
  phminposuw v : word128 =
    case minpos_aux v 1 (lane16 0 v) 0 of (m, k) => w2w m ‖ (n2w k << 16)
End

(* The accumulator is the earliest minimum of the visited prefix. *)
Triviality minpos_aux_first_minimum:
  ∀v i m k.
    i ≤ 8 ∧ k < i ∧ m = lane16 k v ∧
    (∀j. j < i ⇒ w2n m ≤ w2n (lane16 j v)) ∧
    (∀j. j < k ⇒ w2n m < w2n (lane16 j v)) ⇒
    ∃k'. k' < 8 ∧ minpos_aux v i m k = (lane16 k' v, k') ∧
      (∀j. j < 8 ⇒ w2n (lane16 k' v) ≤ w2n (lane16 j v)) ∧
      (∀j. j < k' ⇒ w2n (lane16 k' v) < w2n (lane16 j v))
Proof
  recInduct minpos_aux_ind >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `8 ≤ i`
  >- (`i = 8` by decide_tac >>
      qexists_tac `k` >> gvs[Once minpos_aux_def]) >>
  Cases_on `lane16 i v <₊ m` >>
  PURE_ONCE_REWRITE_TAC [minpos_aux_def] >> gvs[] >>
  first_x_assum irule >>
  fs[WORD_LO] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `j = i` >> fs[] >>
  `j < i` by decide_tac >>
  res_tac >> decide_tac
QED

Theorem phminposuw_low32:
  ∃k. k < 8 ∧
    (∀j. j < 8 ⇒ lane16 k v ≤₊ lane16 j v) ∧
    (∀j. j < k ⇒ lane16 k v <₊ lane16 j v) ∧
    (w2w (lane32 0 (phminposuw v)):word64) =
      w2w (lane16 k v) ‖ (n2w k << 16)
Proof
  mp_tac (Q.SPECL [`v`, `1`, `lane16 0 v`, `0`] minpos_aux_first_minimum) >>
  impl_tac >- (simp[] >> gen_tac >> `j < 1 ⇒ j = 0` by decide_tac >> simp[]) >>
  strip_tac >> qexists_tac `k'` >>
  asm_simp_tac (srw_ss()) [WORD_LS, WORD_LO, phminposuw_def, lane32_def] >>
  `k' < 8 ⇒ k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 ∨
                k' = 4 ∨ k' = 5 ∨ k' = 6 ∨ k' = 7` by decide_tac >>
  res_tac >> fs[] >> blastLib.BBLAST_TAC
QED

Theorem byte_lanes_lanes:
  ∀i. i < 16 ⇒ lane8 i (byte_lanes op a b) = byte_lane op (lane8 i a) (lane8 i b)
Proof
  CONV_TAC (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) []))) >>
  simp[byte_lanes_def, lanes32_def, byte_quad_def, lane8_def] >>
  rpt conj_tac >> blastLib.BBLAST_TAC
QED

Theorem pavgw_lanes:
  ∀i. i < 8 ⇒ lane16 i (pavgw a b) = avg16 (lane16 i a) (lane16 i b)
Proof
  CONV_TAC (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) []))) >>
  simp[pavgw_def, lanes32_def, words32_def, lane16_def] >>
  rpt conj_tac >> blastLib.BBLAST_TAC
QED

Definition pbinop_result_def:
  pbinop_result op (a:word128) (b:word128) =
    case op of
      PXOR => a ⊕ b
    | PADDD => paddd a b
    | PADDQ => paddq a b
    | PAND => a && b
    | POR => a ‖ b
    | PCMPEQB => bytes_eq 16 a b
    | PMULLD => sse4_lanes PMULLD a b
    | PMINUD => sse4_lanes PMINUD a b
    | PMAXUD => sse4_lanes PMAXUD a b
    | PSUBD => sse4_lanes PSUBD a b
    | PSUBQ => lanes64 (lane64 0 a - lane64 0 b) (lane64 1 a - lane64 1 b)
    | PABSD => sse4_lanes PABSD a b
    | PHADDD => phaddd a b
    | PCMPGTQ => lanes64 (pcmpgtq_lane (lane64 0 a) (lane64 0 b))
                         (pcmpgtq_lane (lane64 1 a) (lane64 1 b))
    | PMULUDQ => pmul_even F a b
    | PMULDQ => pmul_even T a b
    | PMINSD => sse4_lanes PMINSD a b
    | PMAXSD => sse4_lanes PMAXSD a b
    | PACKUSDW => pack_dwords T a b
    | PACKSSDW => pack_dwords F a b
    | PMADDWD => pmaddwd a b
    | PMADDUBSW => pmaddubsw a b
    | PACKUSWB => pack_words a b
    | PSADBW => psadbw a b
    | PAVGB => byte_lanes PAVGB a b
    | PAVGW => pavgw a b
    | PADDUSB => byte_lanes PADDUSB a b
    | PSUBUSB => byte_lanes PSUBUSB a b
    | PHMINPOSUW => phminposuw b
End

(* The low n bytes of the blend, selected by the high bits of the mask bytes. *)
Definition pblendvb_def:
  pblendvb 0 (a:word128) (b:word128) (mask:word128) = 0w : word128 ∧
  pblendvb (SUC n) a b mask =
    pblendvb n a b mask ‖
    (w2w (w2w ((if word_bit (8 * n + 7) mask then b else a) >>> (8 * n)) : word8)
     << (8 * n))
End

(* Each matched dword lane has every bit set. PCMPGTD compares signed lanes. *)
Definition pcmpd_lane_def:
  pcmpd_lane gt (a:word32) b =
    if (if gt then b < a else a = b) then -1w else 0w : word32
End

Definition pcmpd_def:
  pcmpd gt a b =
    lanes32 (pcmpd_lane gt (lane32 0 a) (lane32 0 b))
            (pcmpd_lane gt (lane32 1 a) (lane32 1 b))
            (pcmpd_lane gt (lane32 2 a) (lane32 2 b))
            (pcmpd_lane gt (lane32 3 a) (lane32 3 b))
End

Definition ptest_flags_def:
  ptest_flags (a:word128) (b:word128) =
    <| CF := (¬a && b = 0w); PF := F; AF := F; ZF := (a && b = 0w); SF := F; OF := F |>
End

(* Lane i of the result is the lane of v that bits 2i+1..2i of imm select. *)
Definition pshufd_def:
  pshufd v (imm:word8) =
    lanes32 (lane32 (w2n ((1 >< 0) imm : word2)) v) (lane32 (w2n ((3 >< 2) imm : word2)) v)
            (lane32 (w2n ((5 >< 4) imm : word2)) v) (lane32 (w2n ((7 >< 6) imm : word2)) v)
End

(* Word k of the four 16-bit words of q. *)
Definition word16_at_def:
  word16_at (q:word64) (k:word2) : word64 = w2w (w2w (q >>> (16 * w2n k)) : word16)
End

(* PSHUFLW, and PSHUFHW if high: word i of the low (high) half of the result
   is the word of v's low (high) half that bits 2i+1..2i of imm select; the
   other half is v's. *)
Definition pshufw_def:
  pshufw high (v:word128) (imm:word8) =
    let q : word64 = if high then w2w (v >>> 64) else w2w v;
        r = word16_at q ((1 >< 0) imm) ‖ (word16_at q ((3 >< 2) imm) << 16) ‖
            (word16_at q ((5 >< 4) imm) << 32) ‖ (word16_at q ((7 >< 6) imm) << 48)
    in
      if high then (w2w r << 64) ‖ w2w (w2w v : word64) else (v >>> 64 << 64) ‖ w2w r
End

(* The low n bytes of the PSHUFB result: byte i is 0 if bit 7 of byte i of c
   is set, and otherwise the byte of v that its bits 3..0 select. *)
Definition pshufb_def:
  pshufb 0 (v:word128) (c:word128) = 0w : word128 ∧
  pshufb (SUC n) v c =
    pshufb n v c ‖
    (if word_bit (8 * n + 7) c then 0w
     else (w2w (w2w (v >>> (8 * w2n (w2w (c >>> (8 * n)) : word4))) : word8) : word128) << (8 * n))
End

Definition pwiden_byte_def:
  pwiden_byte signed (v:word64) n =
    let lane = (w2w (v >>> (8 * n)) : word8) in
      if signed then (sw2sw lane : word32) else w2w lane
End

(* Bytes n and n + 1 of v extended to words, as a dword. *)
Definition pwiden_pair_def:
  pwiden_pair signed v n =
    words32 (w2w (pwiden_byte signed v n)) (w2w (pwiden_byte signed v (n + 1)))
End

(* Extend the low 4 bytes to dwords (S32), the 8 bytes to words (S16) or
   the 2 dwords to qwords. *)
Definition pwiden_def:
  pwiden signed sz (v:word64) =
    if sz = S32 then
      lanes32 (pwiden_byte signed v 0) (pwiden_byte signed v 1)
              (pwiden_byte signed v 2) (pwiden_byte signed v 3)
    else if sz = S16 then
      lanes32 (pwiden_pair signed v 0) (pwiden_pair signed v 2)
              (pwiden_pair signed v 4) (pwiden_pair signed v 6)
    else
      let lo = (w2w v : word32); hi = (w2w (v >>> 32) : word32) in
        if signed then lanes64 (sw2sw lo) (sw2sw hi)
        else lanes64 (w2w lo) (w2w hi)
End

Theorem pwiden16_lanes:
  ∀i. i < 8 ⇒
    lane16 i (pwiden signed S16 v) =
      if signed then sw2sw (w2w (v >>> (8 * i)) : word8) else w2w (w2w (v >>> (8 * i)) : word8)
Proof
  CONV_TAC (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) []))) >>
  simp[pwiden_def, pwiden_pair_def, pwiden_byte_def, lanes32_def, words32_def, lane16_def] >>
  Cases_on `signed` >> simp[] >> rpt conj_tac >> blastLib.BBLAST_TAC
QED

(* PSLLDQ (left) and PSRLDQ: v shifted by n bytes. A count above 15 clears
   v, as HOL's shifts do. *)
Definition pshiftdq_def:
  pshiftdq left (v:word128) n = if left then v << (8 * n) else v >>> (8 * n)
End

(* The carryless (GF(2)[x]) product of a and the low n bits of b: the XOR
   of a shifted left by i for each set bit i of b below n. *)
Definition clmul_def:
  clmul 0 (a:word64) (b:word64) = 0w : word128 ∧
  clmul (SUC n) a b = clmul n a b ⊕ (if word_bit n b then w2w a << n else 0w)
End

(* PCLMULQDQ: the carryless product of the qword of v1 that bit 0 of imm
   selects and the qword of v2 that bit 4 selects. The product has degree
   at most 126, so bit 127 is 0. *)
Definition pclmul_def:
  pclmul (v1:word128) (v2:word128) (imm:word8) =
    clmul 64 (lane64 (if word_bit 0 imm then 1 else 0) v1)
             (lane64 (if word_bit 4 imm then 1 else 0) v2)
End

(* PALIGNR: the low 128 bits of d:s shifted right by n bytes. A count above
   31 gives 0, as HOL's shift does. *)
Definition palignr_def:
  palignr (d:word128) (s:word128) n = (127 >< 0) (((d @@ s) : 256 word) >>> (8 * n)) : word128
End

(* PSLLD (left) and PSRLD on the 32-bit lanes (S32), PSLLQ and PSRLQ on the
   64-bit lanes (S64), by n. A count of at least the lane width clears
   every lane, as HOL's shifts do. *)
Definition pshift_def:
  pshift left sz (v:word128) n =
    if sz = S32 then
      (if left then lanes32 (lane32 0 v << n) (lane32 1 v << n) (lane32 2 v << n) (lane32 3 v << n)
       else lanes32 (lane32 0 v >>> n) (lane32 1 v >>> n) (lane32 2 v >>> n) (lane32 3 v >>> n))
    else if left then lanes64 (lane64 0 v << n) (lane64 1 v << n)
    else lanes64 (lane64 0 v >>> n) (lane64 1 v >>> n)
End

(* PSRAD: each dword shifted right by n, filling with its sign (all sign bits
   for n ≥ 32). *)
Definition psrad_def:
  psrad (v:word128) n =
    lanes32 (lane32 0 v >> n) (lane32 1 v >> n) (lane32 2 v >> n) (lane32 3 v >> n)
End

Theorem lane32_psrad:
  i < 4 ⇒ lane32 i (psrad v n) = lane32 i v >> n
Proof
  strip_tac >> simp[psrad_def, lane32_packed] >> rw[] >>
  `i = 3` by decide_tac >> simp[]
QED

Definition size_mask_def:
  size_mask S8 = 0xFFw : word64 ∧
  size_mask S16 = 0xFFFFw ∧
  size_mask S32 = 0xFFFFFFFFw ∧
  size_mask S64 = 0xFFFFFFFFFFFFFFFFw
End

Definition size_bytes_def:
  size_bytes S8 = 1n ∧
  size_bytes S16 = 2 ∧
  size_bytes S32 = 4 ∧
  size_bytes S64 = 8
End

Definition sign_bit_def:
  sign_bit S8 (w:word64) = word_bit 7 w ∧
  sign_bit S16 w = word_bit 15 w ∧
  sign_bit S32 w = word_bit 31 w ∧
  sign_bit S64 w = word_bit 63 w
End

(* The low size bits of w, sign-extended. *)
Definition sign_extend_def:
  sign_extend S8 (w:word64) = (sw2sw (w2w w : word8) : word64) ∧
  sign_extend S16 w = sw2sw (w2w w : word16) ∧
  sign_extend S32 w = sw2sw (w2w w : word32) ∧
  sign_extend S64 w = w
End

(* A register after writing v at a size: 8- and 16-bit writes keep the
   other bits, 32-bit writes clear the upper half. *)
Definition merge_reg_def:
  merge_reg S8 (old:word64) v = (old && ¬0xFFw) ‖ (v && 0xFFw) ∧
  merge_reg S16 old v = (old && ¬0xFFFFw) ‖ (v && 0xFFFFw) ∧
  merge_reg S32 old v = v && 0xFFFFFFFFw ∧
  merge_reg S64 old v = v
End

Definition count_bits_def:
  count_bits 0 (w:word64) = 0n ∧
  count_bits (SUC n) w = (if word_bit n w then 1 else 0) + count_bits n w
End

Definition even_parity_def:
  even_parity w ⇔ EVEN (count_bits 8 w)
End

(* Result and flags of op on size-masked operands a and b, with carry in c
   (for ADC and SBB). u supplies the flags the architecture leaves
   undefined: AF after OR, AND, XOR and TEST. *)
Definition binop_result_def:
  binop_result (u:eflags) c sz op (a:word64) b =
    let r = (case op of
               ADD => a + b
             | OR => a ‖ b
             | ADC => a + b + (if c then 1w else 0w)
             | SBB => a - b - (if c then 1w else 0w)
             | AND => a && b
             | SUB => a - b
             | XOR => a ⊕ b
             | CMP => a - b
             | TEST => a && b) && size_mask sz;
        logic = (op = OR ∨ op = AND ∨ op = XOR ∨ op = TEST);
        sub = (op = SUB ∨ op = SBB ∨ op = CMP);
        sa = sign_bit sz a; sb = sign_bit sz b; sr = sign_bit sz r
    in
      (r, <| CF := (if logic then F
                    else if op = ADC then r <₊ a ∨ c ∧ r = a
                    else if op = SBB then a <₊ b ∨ c ∧ a = b
                    else if sub then a <₊ b else r <₊ a);
             PF := even_parity r;
             AF := (if logic then u.AF else word_bit 4 (a ⊕ b ⊕ r));
             ZF := (r = 0w);
             SF := sr;
             OF := (if logic then F
                    else if sub then sa ≠ sb ∧ sr ≠ sa
                    else sa = sb ∧ sr ≠ sa) |>)
End

(* Both ADX instructions use unsigned carry, including ADOX's OF chain. *)
Definition adx_result_def:
  adx_result c (a:word64) b =
    let r = a + b + (if c then 1w else 0w) in
      (r, r <₊ a ∨ c ∧ r = a)
End

Theorem arithmetic_flags_defined:
  op = ADD ∨ op = ADC ∨ op = SUB ∨ op = SBB ∨ op = CMP ⇒
  binop_result u c sz op a b = binop_result u' c sz op a b
Proof
  rw[binop_result_def]
QED

Definition writes_result_def:
  writes_result op ⇔ op ≠ CMP ∧ op ≠ TEST
End

(* Result and flags of shifting the size-masked a by count, masked to 5 bits
   (6 at 64 bits). A masked count of 0 leaves the flags f; otherwise AF, and
   OF after counts above 1, come from u. *)
Definition shift_result_def:
  shift_result (u:eflags) (f:eflags) sz op (a:word64) (count:word8) =
    let c = w2n (count && (if sz = S64 then 63w else 31w));
        r = (case op of
               SHL => a << c
             | SHR => a >>> c
             | SAR => sign_extend sz a >> c) && size_mask sz;
        n = 8 * size_bytes sz
    in
      if c = 0 then (r, f)
      else
        (r, <| CF := (if op = SHL then word_bit (n - c) a else word_bit (c - 1) a);
               PF := even_parity r;
               AF := u.AF;
               ZF := (r = 0w);
               SF := sign_bit sz r;
               OF := (if c ≠ 1 then u.OF
                      else if op = SHL then sign_bit sz a ≠ word_bit (n - 2) a
                      else if op = SHR then sign_bit sz a
                      else F) |>)
End

(* Result and flags of rotating the size-masked a left (or right) by count,
   masked to 5 bits (6 at 64 bits); only S32 and S64 are decoded, so the
   masked count is below the width. A masked count of 0 leaves the flags f;
   otherwise CF is the bit rotated last, OF is defined at count 1 and comes
   from u above it, and PF, AF, ZF and SF keep their values. *)
Definition rotate_result_def:
  rotate_result (u:eflags) (f:eflags) left sz (a:word64) (count:word8) =
    let c = w2n (count && (if sz = S64 then 63w else 31w));
        n = 8 * size_bytes sz;
        r = (if left then (a << c) ‖ (a >>> (n - c)) else (a >>> c) ‖ (a << (n - c))) &&
            size_mask sz
    in
      if c = 0 then (r, f)
      else
        (r, f with <| CF := (if left then word_bit 0 r else word_bit (n - 1) r);
                      OF := (if c ≠ 1 then u.OF
                             else if left then word_bit (n - 1) r ≠ word_bit 0 r
                             else word_bit (n - 1) r ≠ word_bit (n - 2) r) |>)
End

Triviality rotate_right_shifts:
  n < dimindex(:'a) ⇒
  (x:'a word) #>> n = (x >>> n) ‖ (x << (dimindex(:'a) - n))
Proof
  strip_tac >>
  simp[fcpTheory.CART_EQ, word_ror_def, word_lsr_def, word_lsl_def,
       word_or_def, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> Cases_on `i + n < dimindex(:'a)`
  >- (`¬(dimindex(:'a) - n ≤ i)` by decide_tac >> simp[LESS_MOD]) >>
  `dimindex(:'a) - n ≤ i ∧ i + n - dimindex(:'a) < dimindex(:'a)` by decide_tac >>
  `(i + n) MOD dimindex(:'a) = i + n - dimindex(:'a)` by
    (qspecl_then [`dimindex(:'a)`, `i + n - dimindex(:'a)`]
       mp_tac ADD_MODULUS_LEFT >>
     `i + n - dimindex(:'a) + dimindex(:'a) = i + n` by decide_tac >>
     simp[LESS_MOD]) >>
  `i - (dimindex(:'a) - n) = i + n - dimindex(:'a)` by decide_tac >> simp[]
QED

Triviality rotate_left_shifts:
  n < dimindex(:'a) ⇒
  (x:'a word) #<< n = (x << n) ‖ (x >>> (dimindex(:'a) - n))
Proof
  strip_tac >> Cases_on `n = 0`
  >- simp[SHIFT_ZERO, LSR_LIMIT, WORD_OR_CLAUSES] >>
  simp[word_rol_def, LESS_MOD] >>
  `dimindex(:'a) - n < dimindex(:'a)` by decide_tac >>
  `dimindex(:'a) - (dimindex(:'a) - n) = n` by decide_tac >>
  drule_then (qspec_then `x` mp_tac) rotate_right_shifts >>
  simp[] >> metis_tac[WORD_OR_COMM]
QED

Triviality rotate32_shifts:
  n < 32 ⇒
  ((((w2w x:word64) >>> n) ‖ ((w2w x:word64) << (32 - n))) && 0xFFFFFFFFw =
    w2w ((x:word32) #>> n)) ∧
  ((((w2w x:word64) << n) ‖ ((w2w x:word64) >>> (32 - n))) && 0xFFFFFFFFw =
    w2w ((x:word32) #<< n))
Proof
  strip_tac >>
  `(x:word32) #>> n = (x >>> n) ‖ (x << (32 - n))` by
    (mp_tac (INST_TYPE [alpha |-> ``:32``] rotate_right_shifts) >> simp[]) >>
  `(x:word32) #<< n = (x << n) ‖ (x >>> (32 - n))` by
    (mp_tac (INST_TYPE [alpha |-> ``:32``] rotate_left_shifts) >> simp[]) >>
  PURE_ASM_REWRITE_TAC [fcpTheory.CART_EQ] >>
  rpt conj_tac >> rpt strip_tac >>
  `i < 64` by fs[] >>
  `(0xFFFFFFFFw:word64) ' i ⇔ i < 32` by
    (mp_tac (Q.INST [`n` |-> `2 ** 32 - 1`, `i` |-> `i`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:64``] word_index))) >>
     PURE_REWRITE_TAC [bitTheory.BIT_EXP_SUB1] >> simp[]) >>
  simp_tac bool_ss [word_and_def, fcpTheory.FCP_BETA] >>
  Cases_on `i < 32` >>
  fs[fcpTheory.FCP_BETA, w2w] >>
  `i < 64 ∧ i + n < 64 ∧ i + (32 - n) < 64 ∧
    i - n < 64 ∧ i - (32 - n) < 64 ∧ i - n < 32 ∧ i - (32 - n) < 32` by
    decide_tac >>
  asm_simp_tac (srw_ss() ++ fcpLib.FCP_ss) [w2w, word_or_def, word_lsl_def, word_lsr_def] >>
  fs[fcpTheory.FCP_BETA, w2w] >> decide_tac
QED

Triviality rotate_count_mask:
  w2n ((ct:word8) && 31w) = w2n ct MOD 32 ∧
  w2n (ct && 63w) = w2n ct MOD 64
Proof
  Cases_on `ct` >>
  simp[SIMP_RULE (srw_ss()) [] (Q.SPEC `5` WORD_AND_EXP_SUB1),
       SIMP_RULE (srw_ss()) [] (Q.SPEC `6` WORD_AND_EXP_SUB1), w2n_n2w] >>
  `n MOD 32 < 32 ∧ n MOD 64 < 64` by simp[] >>
  simp[LESS_MOD]
QED

Triviality fst_same:
  FST (if cond then (v,f) else (v,g)) = v
Proof
  Cases_on `cond` >> simp[]
QED

Theorem rotate_result_value32:
  FST (rotate_result u f left S32 (a && size_mask S32) ct) =
  (w2w (if left then (w2w a:word32) #<< (w2n ct MOD 32)
        else (w2w a:word32) #>> (w2n ct MOD 32)):word64)
Proof
  `a && size_mask S32 = (w2w (w2w a:word32):word64)` by
    (simp[size_mask_def] >> blastLib.BBLAST_TAC) >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  Cases_on `left` >>
  PURE_REWRITE_TAC [rotate_result_def, LET_THM] >> BETA_TAC >>
  PURE_REWRITE_TAC [fst_same] >>
  simp_tac bool_ss [EVAL ``S32 = S64``, rotate_count_mask, size_bytes_def, size_mask_def] >>
  mp_tac (Q.INST [`x` |-> `w2w (a:word64):word32`, `n` |-> `w2n (ct:word8) MOD 32`]
           rotate32_shifts) >>
  simp[]
QED

Theorem rotate_result_value64:
  FST (rotate_result u f left S64 (a && size_mask S64) ct) =
  if left then a #<< (w2n ct MOD 64) else a #>> (w2n ct MOD 64)
Proof
  `size_mask S64 = (UINT_MAXw:word64)` by EVAL_TAC >>
  Cases_on `left` >>
  PURE_REWRITE_TAC [rotate_result_def, LET_THM] >> BETA_TAC >>
  PURE_REWRITE_TAC [fst_same] >>
  asm_simp_tac bool_ss [rotate_count_mask, size_bytes_def, WORD_AND_CLAUSES] >>
  mp_tac (Q.INST [`x` |-> `a:word64`, `n` |-> `w2n (ct:word8) MOD 64`]
           (INST_TYPE [alpha |-> ``:64``] rotate_right_shifts)) >>
  mp_tac (Q.INST [`x` |-> `a:word64`, `n` |-> `w2n (ct:word8) MOD 64`]
           (INST_TYPE [alpha |-> ``:64``] rotate_left_shifts)) >>
  simp[WORD_AND_CLAUSES]
QED

(* 64-bit IMUL: CF and OF report signed overflow; SF, ZF, AF and PF come
   from u. *)
Definition imul_result_def:
  imul_result (u:eflags) (a:word64) b =
    let r = a * b;
        overflow = ((sw2sw a * sw2sw b : word128) ≠ sw2sw r)
    in
      (r, u with <| CF := overflow; OF := overflow |>)
End

(* One-operand MUL and IMUL: the high and low halves of the unsigned or
   signed 128-bit product a * b. CF and OF report a high half that is not
   the extension of the low half; SF, ZF, AF and PF come from u. *)
Definition mul_wide_def:
  mul_wide (u:eflags) signed (a:word64) (b:word64) =
    let p : word128 = if signed then sw2sw a * sw2sw b else w2w a * w2w b;
        lo : word64 = w2w p;
        overflow = if signed then p ≠ sw2sw lo else p ≠ w2w lo
    in
      (w2w (p >>> 64) : word64, lo, u with <| CF := overflow; OF := overflow |>)
End

(* DIV and IDIV at size sz of the dividend hi:lo (each half size-masked)
   by d: SOME (quotient, remainder), or NONE (#DE) when d is 0 or the
   quotient does not fit the size. IDIV rounds towards 0 and gives the
   remainder the dividend's sign. *)
Definition div_result_def:
  div_result signed sz (hi:word64) (lo:word64) (d:word64) =
    let n = 8 * size_bytes sz;
        a = w2n (hi && size_mask sz) * 2 ** n + w2n (lo && size_mask sz);
        b = w2n (d && size_mask sz)
    in
      if signed then
        let an = (2 ** (2 * n - 1) ≤ a); bn = (2 ** (n - 1) ≤ b);
            am = if an then 2 ** (2 * n) - a else a;
            bm = if bn then 2 ** n - b else b
        in
          if bm = 0 then NONE
          else
            let q = am DIV bm; r = am MOD bm; qn = (an ≠ bn) in
              if (if qn then 2 ** (n - 1) < q else 2 ** (n - 1) ≤ q) then NONE
              else SOME ((if qn then -n2w q else n2w q) && size_mask sz,
                         (if an then -n2w r else n2w r) && size_mask sz)
      else if b = 0 then NONE
      else if 2 ** n ≤ a DIV b then NONE
      else SOME (n2w (a DIV b), n2w (a MOD b))
End

(* Result and flags of SHLD (left) or SHRD of d by count, masked to 6 bits,
   shifting in bits of src. A masked count of 0 leaves d and the flags f;
   otherwise AF, and OF after counts above 1, come from u. *)
Definition shift_double_result_def:
  shift_double_result (u:eflags) (f:eflags) left (d:word64) (src:word64) (count:word8) =
    let c = w2n (count && 63w);
        r = if left then (d << c) ‖ (src >>> (64 - c)) else (d >>> c) ‖ (src << (64 - c))
    in
      if c = 0 then (d, f)
      else
        (r, <| CF := (if left then word_bit (64 - c) d else word_bit (c - 1) d);
               PF := even_parity r;
               AF := u.AF;
               ZF := (r = 0w);
               SF := word_bit 63 r;
               OF := (if c = 1 then word_bit 63 r ≠ word_bit 63 d else u.OF) |>)
End

(* The zero bits of w below its lowest one bit, and above its highest one
   bit, among its low n bits: n for 0. *)
Definition trailing_zeros_def:
  trailing_zeros 0 (w:word64) = 0n ∧
  trailing_zeros (SUC n) w = if word_bit 0 w then 0 else SUC (trailing_zeros n (w >>> 1))
End

Definition leading_zeros_def:
  leading_zeros 0 (w:word64) = 0n ∧
  leading_zeros (SUC n) w = if word_bit n w then 0 else SUC (leading_zeros n w)
End

Triviality word_bit_lsr:
  word_bit i ((w:word64) >>> j) ⇔ word_bit (i + j) w
Proof
  simp[word_bit_thm, word_lsr_def, fcpTheory.FCP_BETA] >>
  Cases_on `i < 64` >> simp[fcpTheory.FCP_BETA] >> decide_tac
QED

Theorem trailing_zeros_index:
  ∀n w. trailing_zeros n w ≤ n ∧
    (∀i. i < trailing_zeros n w ⇒ ¬word_bit i w) ∧
    (trailing_zeros n w < n ⇒ word_bit (trailing_zeros n w) w)
Proof
  Induct >> simp[trailing_zeros_def] >> gen_tac >>
  Cases_on `word_bit 0 w` >> simp[] >>
  first_x_assum (qspec_then `w >>> 1` strip_assume_tac) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `i` >> gs[] >>
      first_x_assum (qspec_then `n'` mp_tac) >>
      gvs[word_bit_lsr, ADD1]) >>
  strip_tac >> first_x_assum drule >> simp[word_bit_lsr, ADD1]
QED

Theorem leading_zeros_index:
  ∀n w. leading_zeros n w ≤ n ∧
    (∀i. i < leading_zeros n w ⇒ ¬word_bit (n - 1 - i) w) ∧
    (leading_zeros n w < n ⇒ word_bit (n - 1 - leading_zeros n w) w)
Proof
  Induct >> simp[leading_zeros_def] >> gen_tac >>
  Cases_on `word_bit n w` >> simp[] >>
  first_x_assum (qspec_then `w` strip_assume_tac) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `i` >> gs[] >>
      first_x_assum (qspec_then `n'` mp_tac) >>
      `n - 1 - n' = n - SUC n'` by decide_tac >> gvs[ADD1]) >>
  strip_tac >> first_x_assum drule >>
  `n - 1 - leading_zeros n w = n - SUC (leading_zeros n w)` by decide_tac >>
  gvs[ADD1]
QED

Theorem popcount_as_bit_count:
  count_bits (dimindex(:64)) w = bit_count w
Proof
  `∀n. n ≤ 64 ⇒ count_bits n w = bit_count_upto n w` by
    (Induct >> simp[count_bits_def, bit_count_upto_0, bit_count_upto_SUC] >>
     strip_tac >> simp[word_bit_thm]) >>
  simp[bit_count_def]
QED

(* On the n-bit source a: TZCNT and LZCNT set CF for a zero source and ZF for a zero result, with
   OF, SF, AF and PF from u; POPCNT sets ZF for a zero source and clears the
   rest. *)
Definition bit_count_result_def:
  bit_count_result (u:eflags) op n (a:word64) =
    case op of
      TZCNT => let r = n2w (trailing_zeros n a) : word64 in
                 (r, u with <| CF := (a = 0w); ZF := (r = 0w) |>)
    | LZCNT => let r = n2w (leading_zeros n a) : word64 in
                 (r, u with <| CF := (a = 0w); ZF := (r = 0w) |>)
    | POPCNT => (n2w (count_bits n a),
                 <| CF := F; PF := F; AF := F; ZF := (a = 0w); SF := F; OF := F |>)
End

(* The flags of ANDN, BZHI, BLSR, BLSI and BLSMSK on a 64-bit result r: SF
   and ZF from r, CF as given, OF clear, and AF and PF from u. *)
Definition bmi_flags_def:
  bmi_flags (u:eflags) cf (r:word64) =
    <| CF := cf; PF := u.PF; AF := u.AF; ZF := (r = 0w); SF := word_bit 63 r; OF := F |>
End

(* BZHI: a with the bits from index n (the low byte of the index register)
   up cleared, and whether n is past the top bit (CF). *)
Definition bzhi_result_def:
  bzhi_result (a:word64) (n:word8) =
    if w2n n < 64 then (a && ((1w << w2n n) - 1w), F) else (a, T)
End

(* BLSR, BLSI and BLSMSK of a, and CF. BLSMSK's result is never 0, so ZF
   is clear after it, as the SDM has it. *)
Definition bls_result_def:
  bls_result op (a:word64) =
    case op of
      BLSR => (a && (a - 1w), a = 0w)
    | BLSI => (a && -a, a ≠ 0w)
    | BLSMSK => (a ⊕ (a - 1w), a = 0w)
End

(* PDEP: the low bits of src deposited, lowest first, at the set bits of
   mask, which is consumed from bit 0 up over n bits; PEXT: the bits of src
   at the set bits of mask, gathered into the low bits. *)
Definition pdep_aux_def:
  pdep_aux 0 (src:word64) (mask:word64) = 0w : word64 ∧
  pdep_aux (SUC n) src mask =
    if word_bit 0 mask then (src && 1w) || pdep_aux n (src >>> 1) (mask >>> 1) << 1
    else pdep_aux n src (mask >>> 1) << 1
End

Definition pext_aux_def:
  pext_aux 0 (src:word64) (mask:word64) = 0w : word64 ∧
  pext_aux (SUC n) src mask =
    if word_bit 0 mask then (src && 1w) || pext_aux n (src >>> 1) (mask >>> 1) << 1
    else pext_aux n (src >>> 1) (mask >>> 1)
End

Definition pdep_result_def:
  pdep_result op src mask =
    case op of PDEP => pdep_aux 64 src mask | PEXT => pext_aux 64 src mask
End

(* BEXTR: len bits of src from bit start, where start is the control's
   bits 7:0 and len its bits 15:8; bits past 63 read as 0. *)
Definition bextr_result_def:
  bextr_result (src:word64) (control:word64) =
    let start = w2n ((7 >< 0) control : word8); len = w2n ((15 >< 8) control : word8) in
      (if start < 64 then src >>> start else 0w) &&
      (if len < 64 then (1w << len) - 1w else UINT_MAXw)
End

(* BEXTR's flags: ZF from the result, CF and OF clear, AF, SF and PF from u. *)
Definition bextr_flags_def:
  bextr_flags (u:eflags) (r:word64) =
    <| CF := F; PF := u.PF; AF := u.AF; ZF := (r = 0w); SF := u.SF; OF := F |>
End

Theorem blsmsk_nonzero:
  FST (bls_result BLSMSK a) ≠ 0w
Proof
  simp[bls_result_def] >> blastLib.BBLAST_TAC
QED

(* Reflected CRC-32C (Castagnoli): consume the least significant source
   bit first, using the reflected polynomial 0x82F63B78. *)
Definition crc32c_bit_def:
  crc32c_bit (crc:word32) bit =
    (crc >>> 1) ⊕ (if word_bit 0 crc ≠ bit then 0x82F63B78w else 0w)
End

Definition crc32c_bits_def:
  crc32c_bits 0 crc (src:word64) = crc ∧
  crc32c_bits (SUC n) crc src =
    crc32c_bits n (crc32c_bit crc (word_bit 0 src)) (src >>> 1)
End

Definition condition_def:
  condition (cc:word4) f =
    let n = w2n (cc >>> 1);
        base = if n = 0 then f.OF
               else if n = 1 then f.CF
               else if n = 2 then f.ZF
               else if n = 3 then f.CF ∨ f.ZF
               else if n = 4 then f.SF
               else if n = 5 then f.PF
               else if n = 6 then f.SF ≠ f.OF
               else f.ZF ∨ f.SF ≠ f.OF
    in if word_bit 0 cc then ¬base else base
End

(* The address of a memory operand of an instruction of len bytes at s.rip. *)
Definition address_of_def:
  address_of ops s len (Mem base index scale disp) =
    (case base of NONE => 0w | SOME b => read_reg ops s b) +
    (case index of NONE => 0w | SOME i => read_reg ops s i << w2n scale) +
    disp ∧
  address_of ops s len (RipRel disp) = s.rip + n2w len + disp
End

Definition read_bytes_def:
  read_bytes ops 0 s a = [] ∧
  read_bytes ops (SUC n) s a = ops.get_byte s.mem a :: read_bytes ops n s (a + 1w)
End

(* The low n bytes of w, least significant first. *)
Definition le_bytes_def:
  le_bytes 0 (w:word64) = [] : word8 list ∧
  le_bytes (SUC n) w = w2w w :: le_bytes n (w >>> 8)
End

(* The bytes of w in the opposite order. *)
Definition bswap64_def:
  bswap64 (w:word64) = le_word (REVERSE (le_bytes 8 w))
End

Definition write_bytes_def:
  write_bytes ops [] a s = s ∧
  write_bytes ops (b::bs) a s =
    write_bytes ops bs (a + 1w) (s with mem := ops.put_byte a b s.mem)
End

Datatype:
  access = Read | Write | Execute
End

(* W^X: code is fetched only from readable, executable, non-writable bytes,
   and stores go only to readable, writable, non-executable ones. *)
Definition allowed_def:
  allowed Read p = p.read ∧
  allowed Write p = (p.read ∧ p.write ∧ ¬p.execute) ∧
  allowed Execute p = (p.read ∧ p.execute ∧ ¬p.write)
End

Definition access_ok_def:
  (access_ok ops k 0 s a ⇔ T) ∧
  (access_ok ops k (SUC n) s a ⇔
    allowed k (ops.get_perm s.perms a) ∧ access_ok ops k n s (a + 1w))
End

(* An n-byte little-endian load, NONE if any byte is unreadable. *)
Definition load_def:
  load (ops:('g,'m,'p,'x) x86_storage) n a (s:('g,'m,'p,'x) x86_machine) =
    if access_ok ops Read n s a then SOME (le_word (read_bytes ops n s a)) else NONE
End

(* An n-byte little-endian store. All n bytes are checked before any is
   written, so a store that faults changes nothing. *)
Definition store_def:
  store (ops:('g,'m,'p,'x) x86_storage) n a (v:word64) (s:('g,'m,'p,'x) x86_machine) =
    if access_ok ops Write n s a then Next (write_bytes ops (le_bytes n v) a s)
    else Fault Store
End

(* A 16-byte load and store, as two little-endian 8-byte halves. All 16
   bytes are checked before any is read or written; no alignment is
   required (MOVUPS, MOVDQU). *)
Definition load128_def:
  load128 (ops:('g,'m,'p,'x) x86_storage) a (s:('g,'m,'p,'x) x86_machine) =
    if access_ok ops Read 16 s a then
      SOME ((w2w (le_word (read_bytes ops 8 s (a + 8w))) << 64) ‖
            w2w (le_word (read_bytes ops 8 s a)) : word128)
    else NONE
End

Definition store128_def:
  store128 (ops:('g,'m,'p,'x) x86_storage) a (v:word128) (s:('g,'m,'p,'x) x86_machine) =
    if access_ok ops Write 16 s a then
      Next (write_bytes ops (le_bytes 8 (w2w v) ++ le_bytes 8 (w2w (v >>> 64))) a s)
    else Fault Store
End

(* A register or a legacy SIMD memory operand that requires alignment. *)
Definition read_aligned_xmm_def:
  read_aligned_xmm ops s len (RmReg r) = Next (read_xmm ops s r) ∧
  read_aligned_xmm ops s len (RmMem a) =
    let addr = address_of ops s len a in
      if addr && 15w ≠ 0w then Fault Alignment
      else case load128 ops addr s of
             NONE => Fault Load
           | SOME value => Next value
End

Definition read_operand_def:
  read_operand ops sz s len (RmReg r) = SOME (read_reg ops s r && size_mask sz) ∧
  read_operand ops sz s len (RmMem a) = load ops (size_bytes sz) (address_of ops s len a) s
End

Definition write_operand_def:
  write_operand ops sz s len (RmReg r) v =
    Next (write_reg ops r (merge_reg sz (read_reg ops s r) v) s) ∧
  write_operand ops sz s len (RmMem a) v =
    store ops (size_bytes sz) (address_of ops s len a) v s
End

Definition next_rip_def:
  next_rip len (Next s) = Next (s with rip := s.rip + n2w len) ∧
  next_rip len (Fault f) = Fault f
End

(* One instruction of len bytes at s.rip. Operand addresses are computed in
   s, before RIP moves past the instruction. *)
Definition execute_with_def:
  execute_with ops u (MovImm r imm) len s =
    Next (write_reg ops r (w2w imm) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Mov sz d src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME v => next_rip len (write_operand ops sz s len d v)) ∧
  execute_with ops u (Binop op sz d src) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         case read_operand ops sz s len src of
           NONE => Fault Load
         | SOME b =>
             let (v, f) = binop_result u s.flags.CF sz op a b in
               next_rip len (if writes_result op then write_operand ops sz (s with flags := f) len d v
                             else Next (s with flags := f))) ∧
  execute_with ops u (BinopImm op sz d imm) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         let (v, f) = binop_result u s.flags.CF sz op a (imm && size_mask sz) in
           next_rip len (if writes_result op then write_operand ops sz (s with flags := f) len d v
                         else Next (s with flags := f))) ∧
  execute_with ops u (Movzx sz r src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME v => Next (write_reg ops r v s with rip := s.rip + n2w len)) ∧
  execute_with ops u (MovImm64 r imm) len s =
    Next (write_reg ops r imm s with rip := s.rip + n2w len) ∧
  execute_with ops u (Movsx r src) len s =
    (case read_operand ops S8 s len src of
       NONE => Fault Load
     | SOME v => Next (write_reg ops r (sign_extend S8 v && 0xFFFFFFFFw) s with rip := s.rip + n2w len)) ∧
  execute_with ops u (Movsxd r src) len s =
    (case read_operand ops S32 s len src of
       NONE => Fault Load
     | SOME v => Next (write_reg ops r (sign_extend S32 v) s with rip := s.rip + n2w len)) ∧
  execute_with ops u Cdqe len s =
    Next (write_reg ops 0w (sign_extend S32 (read_reg ops s 0w)) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Lea r a) len s =
    Next (write_reg ops r (address_of ops s len a) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Not sz d) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a => next_rip len (write_operand ops sz s len d (¬a && size_mask sz))) ∧
  execute_with ops u (Neg sz d) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         let (v, f) = binop_result u F sz SUB 0w a in
           next_rip len (write_operand ops sz (s with flags := f) len d v)) ∧
  execute_with ops u (Inc sz d) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         let (v, f) = binop_result u F sz ADD a 1w in
           next_rip len (write_operand ops sz (s with flags := (f with CF := s.flags.CF)) len d v)) ∧
  execute_with ops u (Dec64 d) len s =
    (let (v, f) = binop_result u F S64 SUB (read_reg ops s d) 1w in
       Next (write_reg ops d v s
             with <| flags := f with CF := s.flags.CF; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Shift op sz d count) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         let c = (case count of SOME c => c | NONE => w2w (read_reg ops s 1w));
             (v, f) = shift_result u s.flags sz op a c
         in
           next_rip len (write_operand ops sz (s with flags := f) len d v)) ∧
  execute_with ops u (Rotate left sz r count) len s =
    (let c = (case count of SOME c => c | NONE => w2w (read_reg ops s 1w));
         (v, f) = rotate_result u s.flags left sz (read_reg ops s r && size_mask sz) c
     in
       Next (write_reg ops r (merge_reg sz (read_reg ops s r) v) s
             with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Imul r src) len s =
    (case read_operand ops S64 s len src of
       NONE => Fault Load
     | SOME b =>
         let (v, f) = imul_result u (read_reg ops s r) b in
           Next (write_reg ops r v s with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (MulWide signed r) len s =
    (let (hi, lo, f) = mul_wide u signed (read_reg ops s 0w) (read_reg ops s r) in
       Next (write_reg ops 2w hi (write_reg ops 0w lo s) with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Div signed sz r) len s =
    (case div_result signed sz (read_reg ops s 2w) (read_reg ops s 0w) (read_reg ops s r) of
       NONE => Fault Divide
     | SOME (q, rm) =>
         Next (write_reg ops 2w rm (write_reg ops 0w q s) with <| flags := u; rip := s.rip + n2w len |>)) ∧
  execute_with ops u Cqo len s =
    Next (write_reg ops 2w (if word_bit 63 (read_reg ops s 0w) then -1w else 0w) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (ShiftDouble left d src) len s =
    (let (v, f) = shift_double_result u s.flags left (read_reg ops s d) (read_reg ops s src)
                                      (w2w (read_reg ops s 1w))
     in
       Next (write_reg ops d v s with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Bswap r) len s =
    Next (write_reg ops r (bswap64 (read_reg ops s r)) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Adx overflow d src) len s =
    (let c = if overflow then s.flags.OF else s.flags.CF;
         (r, carry) = adx_result c (read_reg ops s d) (read_reg ops s src);
         f = if overflow then s.flags with OF := carry else s.flags with CF := carry
     in
       Next (write_reg ops d r s with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (MovbeLoad d a) len s =
    (case read_operand ops S64 s len (RmMem a) of
       NONE => Fault Load
     | SOME v => Next (write_reg ops d (bswap64 v) s with rip := s.rip + n2w len)) ∧
  execute_with ops u (MovbeStore a src) len s =
    next_rip len (write_operand ops S64 s len (RmMem a) (bswap64 (read_reg ops s src))) ∧
  execute_with ops u (Crc32 sz d src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME v =>
         Next (write_reg ops d (w2w (crc32c_bits (8 * size_bytes sz) (w2w (read_reg ops s d)) v)) s
               with rip := s.rip + n2w len)) ∧
  execute_with ops u (BitCount op sz d src) len s =
    (let (v, f) = bit_count_result u op (8 * size_bytes sz) (read_reg ops s src && size_mask sz) in
       Next (write_reg ops d v s with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Cmov cc sz r src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME v =>
         next_rip len (write_operand ops sz s len (RmReg r)
                         (if condition cc s.flags then v else read_reg ops s r))) ∧
  execute_with ops u (Setcc cc d) len s =
    next_rip len (write_operand ops S8 s len d (if condition cc s.flags then 1w else 0w)) ∧
  execute_with ops u (Mulx hi lo src) len s =
    (case read_operand ops S64 s len src of
       NONE => Fault Load
     | SOME b =>
         let (h, l, f) = mul_wide u F (read_reg ops s 2w) b in
           Next (write_reg ops hi h (write_reg ops lo l s) with rip := s.rip + n2w len)) ∧
  execute_with ops u (Rorx sz d src imm) len s =
    Next (write_reg ops d (FST (rotate_result u s.flags F sz (read_reg ops s src && size_mask sz) imm)) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (ShiftX op d src cnt) len s =
    Next (write_reg ops d (FST (shift_result u s.flags S64 op (read_reg ops s src)
                                             (w2w (read_reg ops s cnt)))) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (Andn d a b) len s =
    (let r = ¬read_reg ops s a && read_reg ops s b in
       Next (write_reg ops d r s with <| flags := bmi_flags u F r; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Bzhi d a n) len s =
    (let (r, cf) = bzhi_result (read_reg ops s a) (w2w (read_reg ops s n)) in
       Next (write_reg ops d r s with <| flags := bmi_flags u cf r; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Bls op d a) len s =
    (let (r, cf) = bls_result op (read_reg ops s a) in
       Next (write_reg ops d r s with <| flags := bmi_flags u cf r; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Pdep op d a mask) len s =
    Next (write_reg ops d (pdep_result op (read_reg ops s a) (read_reg ops s mask)) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (Bextr d a c) len s =
    (let r = bextr_result (read_reg ops s a) (read_reg ops s c) in
       Next (write_reg ops d r s with <| flags := bextr_flags u r; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Push r) len s =
    (let sp = read_reg ops s 4w - 8w in
       case store ops 8 sp (read_reg ops s r) s of
         Next t => Next (write_reg ops 4w sp t with rip := s.rip + n2w len)
       | Fault f => Fault f) ∧
  execute_with ops u (Pop r) len s =
    (let sp = read_reg ops s 4w in
       case load ops 8 sp s of
         NONE => Fault Load
       | SOME v => Next (write_reg ops r v (write_reg ops 4w (sp + 8w) s)
                         with rip := s.rip + n2w len)) ∧
  execute_with ops u (Call d) len s =
    (let sp = read_reg ops s 4w - 8w; ret = s.rip + n2w len in
       case store ops 8 sp ret s of
         Next t => Next (write_reg ops 4w sp t with rip := ret + d)
       | Fault f => Fault f) ∧
  execute_with ops u (Jcc cc d) len s =
    Next (s with rip := s.rip + n2w len + (if condition cc s.flags then d else 0w)) ∧
  execute_with ops u (Jmp d) len s = Next (s with rip := s.rip + n2w len + d) ∧
  execute_with ops u (JmpReg r) len s = Next (s with rip := read_reg ops s r) ∧
  execute_with ops u Ret len s =
    (let sp = read_reg ops s 4w in
       case load ops 8 sp s of
         NONE => Fault Load
       | SOME v => Next (write_reg ops 4w (sp + 8w) s with rip := v)) ∧
  execute_with ops u Nop len s = Next (s with rip := s.rip + n2w len) ∧
  execute_with ops u (VecLoad aligned x a) len s =
    (let addr = address_of ops s len a in
       if aligned ∧ addr && 15w ≠ 0w then Fault Alignment
       else case load128 ops addr s of
              NONE => Fault Load
            | SOME v => Next (write_xmm ops x v s with rip := s.rip + n2w len)) ∧
  execute_with ops u (VecStore a x) len s =
    next_rip len (store128 ops (address_of ops s len a) (read_xmm ops s x) s) ∧
  execute_with ops u (VecMov d x) len s =
    Next (write_xmm ops d (read_xmm ops s x) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Pbinop op d x) len s =
    Next (write_xmm ops d (pbinop_result op (read_xmm ops s d) (read_xmm ops s x)) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (Pblendvb d src) len s =
    (case read_aligned_xmm ops s len src of
       Next v => Next (write_xmm ops d (pblendvb 16 (read_xmm ops s d) v (read_xmm ops s 0w)) s
                      with rip := s.rip + n2w len)
     | Fault f => Fault f) ∧
  execute_with ops u (Pcmpd gt d src) len s =
    (case read_aligned_xmm ops s len src of
       Next v => Next (write_xmm ops d (pcmpd gt (read_xmm ops s d) v) s
                      with rip := s.rip + n2w len)
     | Fault f => Fault f) ∧
  execute_with ops u (Pwiden signed sz d a) len s =
    (case load ops (if sz = S32 then 4 else 8) (address_of ops s len a) s of
       SOME v => Next (write_xmm ops d (pwiden signed sz v) s with rip := s.rip + n2w len)
     | NONE => Fault Load) ∧
  execute_with ops u (Ptest d x) len s =
    Next (s with <| flags := ptest_flags (read_xmm ops s d) (read_xmm ops s x);
                   rip := s.rip + n2w len |>) ∧
  execute_with ops u (Pshufd d x imm) len s =
    Next (write_xmm ops d (pshufd (read_xmm ops s x) imm) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Pshufw high d x imm) len s =
    Next (write_xmm ops d (pshufw high (read_xmm ops s x) imm) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Pshufb d src) len s =
    (case read_aligned_xmm ops s len src of
       Next c => Next (write_xmm ops d (pshufb 16 (read_xmm ops s d) c) s
                      with rip := s.rip + n2w len)
     | Fault f => Fault f) ∧
  execute_with ops u (Pshift left sz x imm) len s =
    Next (write_xmm ops x (pshift left sz (read_xmm ops s x) (w2n imm)) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (Psrad x imm) len s =
    Next (write_xmm ops x (psrad (read_xmm ops s x) (w2n imm)) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Pshiftdq left x imm) len s =
    Next (write_xmm ops x (pshiftdq left (read_xmm ops s x) (w2n imm)) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (PxorMem d a) len s =
    (case read_aligned_xmm ops s len (RmMem a) of
       Next v => Next (write_xmm ops d (read_xmm ops s d ?? v) s
                      with rip := s.rip + n2w len)
     | Fault f => Fault f) ∧
  execute_with ops u (AesRound op d src) len s =
    (case read_aligned_xmm ops s len src of
       Next k => Next (write_xmm ops d (aes_round_result op (read_xmm ops s d) k) s
                      with rip := s.rip + n2w len)
     | Fault f => Fault f) ∧
  execute_with ops u (AesImc d src) len s =
    Next (write_xmm ops d (aes_imc_result (read_xmm ops s src)) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (Pclmul d x imm) len s =
    Next (write_xmm ops d (pclmul (read_xmm ops s d) (read_xmm ops s x) imm) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (AesKeygen d x imm) len s =
    Next (write_xmm ops d (aes_keygen_assist (read_xmm ops s x) imm) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (Palignr d x imm) len s =
    Next (write_xmm ops d (palignr (read_xmm ops s d) (read_xmm ops s x) (w2n imm)) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (Pinsrq x src imm) len s =
    (case read_operand ops S64 s len src of
       NONE => Fault Load
     | SOME v =>
         let old = read_xmm ops s x;
             result = if word_bit 0 imm then lanes64 (lane64 0 old) v
                      else lanes64 v (lane64 1 old) in
           Next (write_xmm ops x result s with rip := s.rip + n2w len)) ∧
  execute_with ops u (Pextrq dst x imm) len s =
    next_rip len (write_operand ops S64 s len dst
      (lane64 (if word_bit 0 imm then 1 else 0) (read_xmm ops s x))) ∧
  execute_with ops u (Punpcklqdq d src) len s =
    Next (write_xmm ops d (lanes64 (lane64 0 (read_xmm ops s d))
      (lane64 0 (read_xmm ops s src))) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Pmovmskb r x) len s =
    Next (write_reg ops r (byte_signs 16 (read_xmm ops s x)) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Movd sz r x) len s =
    Next (write_reg ops r (if sz = S64 then w2w (read_xmm ops s x) else w2w (lane32 0 (read_xmm ops s x))) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (MovqXmm x r) len s =
    Next (write_xmm ops x (w2w (read_reg ops s r)) s with rip := s.rip + n2w len) ∧
  execute_with ops u (Pinsrd x src imm) len s =
    (case read_operand ops S32 s len src of
       NONE => Fault Load
     | SOME v =>
         Next (write_xmm ops x (insert_lane32 (w2n imm MOD 4) (read_xmm ops s x) (w2w v)) s
               with rip := s.rip + n2w len)) ∧
  execute_with ops u (Pextrd dst x imm) len s =
    next_rip len (write_operand ops S32 s len dst
      (w2w (lane32 (w2n imm MOD 4) (read_xmm ops s x)))) ∧
  execute_with ops u (MovdXmm x src) len s =
    (case read_operand ops S32 s len src of
       NONE => Fault Load
     | SOME v => Next (write_xmm ops x (w2w v) s with rip := s.rip + n2w len))
End

(* The number of consecutive executable bytes from a, at most n. *)
Definition fetchable_def:
  fetchable ops 0 s a = 0n ∧
  fetchable ops (SUC n) s a =
    if allowed Execute (ops.get_perm s.perms a) then SUC (fetchable ops n s (a + 1w)) else 0
End

(* One instruction. u gives the values of flags the instruction leaves
   architecturally undefined. Only the executable bytes of the 15-byte fetch
   window reach the decoder, so bytes the CPU may not fetch never decide the
   outcome: an instruction whose decoding needs a byte past a
   non-executable one is a fetch fault. *)
Definition step_with_def:
  step_with ops u s =
    let n = fetchable ops 15 s s.rip in
      if n = 0 then Fault Fetch
      else case decode (read_bytes ops n s s.rip) of
        Decoded i len => execute_with ops u i len s
      | Truncated => if n < 15 then Fault Fetch else Fault Unsupported
      | Rejected => Fault Unsupported
End

Definition step_def:
  step u (s:x86_state) : x86_state x86_result = step_with functional_storage u s
End

(* Runs under an undefined-flag stream: step k takes its undefined flags
   from u k, so a property over all u covers every value a CPU may choose. *)
Definition x86_next_def:
  x86_next (u:num -> eflags) (k, s) (k', s') ⇔ k' = k + 1 ∧ step (u k) s = Next s'
End

Definition run_def:
  run (u:num -> eflags) k 0 s = Next s ∧
  run u k (SUC n) s =
    case step (u k) s of
      Next t => run u (k + 1) n t
    | Fault f => Fault f
End

Theorem load_byte:
  load ops 1 a s =
    if allowed Read (ops.get_perm s.perms a) then SOME (w2w (ops.get_byte s.mem a)) else NONE
Proof
  REWRITE_TAC [arithmeticTheory.ONE, load_def, access_ok_def, read_bytes_def, le_word_def] >>
  simp[]
QED

(* Stores *)

Theorem write_bytes_fields:
  ∀bs a s. (write_bytes ops bs a s).regs = s.regs ∧
           (write_bytes ops bs a s).xmm = s.xmm ∧
           (write_bytes ops bs a s).rip = s.rip ∧
           (write_bytes ops bs a s).flags = s.flags ∧
           (write_bytes ops bs a s).perms = s.perms
Proof
  Induct >> simp[write_bytes_def]
QED

Theorem word_offset_suc:
  (a:word64) + n2w (SUC i) = a + 1w + n2w i
Proof
  REWRITE_TAC [GSYM WORD_ADD_ASSOC, word_add_n2w] >>
  `1 + i = SUC i` by decide_tac >> simp[]
QED

Theorem write_bytes_unchanged:
  ∀bs a s x. (∀i. i < LENGTH bs ⇒ x ≠ a + n2w i) ⇒
    (write_bytes functional_storage bs a s).mem x = s.mem x
Proof
  Induct >> rw[write_bytes_def] >>
  first_x_assum (qspecl_then [`a + 1w`, `s with mem := functional_storage.put_byte a h s.mem`,
                              `x`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
      `a + 1w + n2w i = a + n2w (SUC i)` suffices_by simp[] >>
      REWRITE_TAC [word_offset_suc]) >>
  first_x_assum (qspec_then `0` mp_tac) >>
  simp[functional_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem le_bytes_length[simp]:
  ∀n w. LENGTH (le_bytes n w) = n
Proof
  Induct >> simp[le_bytes_def]
QED

(* A store faults, writing nothing (it carries no state), exactly when a
   byte it would write is not readable, not writable or executable. *)
Theorem store_fault:
  store ops n a v s = Fault k ⇔ k = Store ∧ ¬access_ok ops Write n s a
Proof
  Cases_on `k` >> rw[store_def]
QED

(* A store that succeeds had every byte writable, and changes only the
   n stored bytes. *)
Theorem store_footprint:
  store functional_storage n a v s = Next t ⇒
    access_ok functional_storage Write n s a ∧
    t.regs = s.regs ∧ t.xmm = s.xmm ∧ t.rip = s.rip ∧ t.flags = s.flags ∧ t.perms = s.perms ∧
    ∀x. (∀i. i < n ⇒ x ≠ a + n2w i) ⇒ t.mem x = s.mem x
Proof
  rw[store_def] >> simp[write_bytes_fields] >>
  irule write_bytes_unchanged >> simp[]
QED

Theorem store128_fault:
  store128 ops a v s = Fault k ⇔ k = Store ∧ ¬access_ok ops Write 16 s a
Proof
  Cases_on `k` >> rw[store128_def]
QED

(* A 16-byte store that succeeds had every byte writable, and changes only
   the 16 stored bytes. *)
Theorem store128_footprint:
  store128 functional_storage a v s = Next t ⇒
    access_ok functional_storage Write 16 s a ∧
    t.regs = s.regs ∧ t.xmm = s.xmm ∧ t.rip = s.rip ∧ t.flags = s.flags ∧ t.perms = s.perms ∧
    ∀x. (∀i. i < 16 ⇒ x ≠ a + n2w i) ⇒ t.mem x = s.mem x
Proof
  rw[store128_def] >> simp[write_bytes_fields] >>
  irule write_bytes_unchanged >> simp[]
QED
