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
    df : bool;
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

(* RCL and RCR rotate through CF. *)
Datatype:
  rotate = ROL | ROR | RCL | RCR
End

(* BT copies a bit to CF; BTS, BTR and BTC also set, reset or complement it. *)
Datatype:
  bt = BT | BTS | BTR | BTC
End

(* LOOP, LOOPE and LOOPNE decrement RCX and branch while it is not 0 (and ZF
   is set, or clear); JRCXZ branches when RCX is 0. *)
Datatype:
  loop = LOOP | LOOPE | LOOPNE | JRCXZ
End

Datatype:
  strop = MOVS | CMPS | STOS | LODS | SCAS
End

(* No repeat prefix; REP or REPE (F3, and F2 before MOVS, STOS and LODS);
   REPNE (F2 before CMPS and SCAS). *)
Datatype:
  rep = NoRep | RepE | RepNE
End

Datatype:
  flagop = CLC | STC | CMC | CLD | STD
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

(* RmHigh r: AH, CH, DH or BH, bits 15:8 of register r (0..3), named by
   register numbers 4..7 of a byte operand without a REX prefix. *)
Datatype:
  rm = RmReg word4 | RmHigh word2 | RmMem address
End

(* Instructions take the destination first. A size is the operand size:
   S8 for byte forms, S16 with a 66 prefix, S64 with REX.W, S32 otherwise
   (S64 by default for stack and branch operands). Immediates are held
   sign-extended to 64 bits. *)
Datatype:
  x86_instr =
    MovImm size rm word64               (* B0+r ib, B8+r iw/id/io, C6 /0 ib, C7 /0 iz *)
  | Mov size rm rm                      (* 88..8B /r; A0..A3 moffs64 *)
  | Binop binop size rm rm              (* 00..3B /r: ADD .. CMP; 84, 85 /r: TEST *)
  | BinopImm binop size rm word64       (* 04..3D: AL/rAX, imm; 80, 81, 83 /digit;
                                           A8, A9; F6, F7 /0: TEST *)
  | Movx bool size size word4 rm        (* 0F B6, B7, BE, BF /r: MOVZX, MOVSX (signed);
                                           63 /r: MOVSXD: destination and source sizes *)
  | Cbw size                            (* 98: CBW, CWDE, CDQE *)
  | Cwd size                            (* 99: CWD, CDQ, CQO *)
  | Lea size word4 address              (* 8D /r *)
  | Not size rm                         (* F6, F7 /2 *)
  | Neg size rm                         (* F6, F7 /3 *)
  | Inc size rm                         (* FE, FF /0 *)
  | Dec size rm                         (* FE, FF /1 *)
  | Shift shift size rm (word8 option)  (* C0, C1 /4 /5 /7 ib; D0, D1 (SOME 1w);
                                           D2, D3 (by CL: NONE) *)
  | Rotate rotate size rm (word8 option) (* C0, C1, D0..D3 /0..3 *)
  | Imul size word4 rm (word64 option)  (* 0F AF /r; 69 /r iz, 6B /r ib (SOME imm) *)
  | MulWide bool size rm                (* F6, F7 /4 /5: MUL, IMUL (signed) into rDX:rAX *)
  | Div bool size rm                    (* F6, F7 /6 /7: DIV, IDIV (signed) *)
  | ShiftDouble bool size rm word4 (word8 option)
                                        (* 0F A4 ib, A5 (CL): SHLD (T); 0F AC, AD: SHRD *)
  | Bswap size word4                    (* 0F C8+r *)
  | Xchg size rm rm                     (* 86, 87 /r; 90+r *)
  | Xadd size rm rm                     (* 0F C0, C1 /r *)
  | Cmpxchg size rm rm                  (* 0F B0, B1 /r *)
  | Cmpxchg2 bool address               (* 0F C7 /1: CMPXCHG8B; REX.W: CMPXCHG16B (T) *)
  | Bt bt size rm word4                 (* 0F A3, AB, B3, BB /r: bit offset in a register *)
  | BtImm bt size rm word8              (* 0F BA /4..7 ib *)
  | BitScan bool size word4 rm          (* 0F BC, BD /r: BSF, BSR (reverse) *)
  | BitCount bitcount size word4 rm     (* F3 0F BC, BD, B8 /r: TZCNT, LZCNT, POPCNT *)
  | Adx bool size word4 rm              (* 66, F3 0F 38 F6 /r: ADCX, ADOX (T) *)
  | Movbe size rm rm                    (* 0F 38 F0, F1 /r, one operand in memory *)
  | Crc32 size word4 rm                 (* F2 0F 38 F0, F1 /r: the source size *)
  | Cmov word4 size word4 rm            (* 0F 40..4F /r *)
  | Setcc word4 rm                      (* 0F 90..9F /r *)
  | Mulx size word4 word4 rm            (* VEX.LZ.F2.0F38 F6 /r: high, low, source *)
  | Rorx size word4 rm word8            (* VEX.LZ.F2.0F3A F0 /r ib *)
  | ShiftX shift size word4 rm word4    (* VEX.LZ.66, F3, F2.0F38 F7 /r: SHLX, SARX, SHRX
                                           (count in vvvv) *)
  | Andn size word4 word4 rm            (* VEX.LZ.0F38 F2 /r: d, inverted vvvv, r/m *)
  | Bzhi size word4 rm word4            (* VEX.LZ.0F38 F5 /r: index in vvvv *)
  | Bls bls size word4 rm               (* VEX.LZ.0F38 F3 /1 /3 /2: destination in vvvv *)
  | Pdep pdep size word4 word4 rm       (* VEX.LZ.F2, F3.0F38 F5 /r: PDEP, PEXT d, vvvv, mask *)
  | Bextr size word4 rm word4           (* VEX.LZ.0F38 F7 /r: control in vvvv *)
  | Push size rm                        (* 50+r; FF /6 *)
  | PushImm size word64                 (* 6A ib, 68 iz *)
  | Pop size rm                         (* 58+r; 8F /0 *)
  | Pushf size                          (* 9C *)
  | Popf size                           (* 9D *)
  | Lahf                                (* 9F *)
  | Sahf                                (* 9E *)
  | FlagOp flagop                       (* F8, F9, F5, FC, FD *)
  | Leave size                          (* C9 *)
  | Enter size word16 word8             (* C8 iw ib *)
  | Call word64                         (* E8 cd *)
  | CallInd rm                          (* FF /2 *)
  | Jcc word4 word64                    (* 70..7F cb; 0F 80..8F cd *)
  | Jmp word64                          (* EB cb; E9 cd *)
  | JmpInd rm                           (* FF /4 *)
  | Loop loop word64                    (* E0..E3 cb *)
  | Ret word16                          (* C3; C2 iw *)
  | Xlat                                (* D7 *)
  | StringOp strop size rep             (* A4..A7, AA..AF *)
  | Nop                                 (* 90, F3 90, and the hint NOPs 0F 0D, 0F 18..1F /r *)
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

(* Prefixes in 64-bit mode: 66 (operand size, or a vector form's mandatory
   prefix), F2 and F3 (repeat, or mandatory prefixes), the null segment
   overrides 2E, 3E, 26 and 36, which are ignored, and REX bytes (40-4F),
   which count only right before the opcode. LOCK, the FS and GS overrides
   and the 67 address-size prefix are not modelled. *)
Definition split_prefixes_def:
  split_prefixes [] = ([], []) ∧
  split_prefixes (b::bs) =
    if b = 0x66w ∨ b = 0xF2w ∨ b = 0xF3w ∨ b = 0x2Ew ∨ b = 0x3Ew ∨ b = 0x26w ∨ b = 0x36w ∨
       b && 0xF0w = 0x40w then
      (let (ps, rest) = split_prefixes bs in (b::ps, rest))
    else ([], b::bs)
End

Definition has_prefix_def:
  has_prefix (p:word8) [] = F ∧
  has_prefix p (b::bs) = (b = p ∨ has_prefix p bs)
End

Definition has_rex_def:
  has_rex [] = F ∧
  has_rex (b::bs) = (b && 0xF0w = 0x40w ∨ has_rex bs)
End

(* What the prefixes say: an operand-size (66) prefix, the repeat prefix (F2
   or F3, 0w when absent) and the REX byte (0w when absent). *)
Datatype:
  prefix = <| opsize : bool; rep : word8; rex : word8 |>
End

(* The operand size of a form with byte (S8) and full-size variants, at its
   full size. *)
Definition op_size_def:
  op_size pf = if word_bit 3 pf.rex then S64 else if pf.opsize then S16 else S32
End

(* The operand size of a stack form, 64 bits unless a 66 prefix makes it 16. *)
Definition stack_size_def:
  stack_size pf = if pf.opsize ∧ ¬word_bit 3 pf.rex then S16 else S64
End

Definition rex_bits_def:
  rex_bits (rex:word8) = (word_bit 2 rex, word_bit 1 rex, word_bit 0 rex)
End

(* An operand of size sz: registers 4..7 of a byte operand are AH..BH
   without a REX prefix. *)
Definition sized_def:
  sized sz (rex:word8) (RmReg r) =
    (if sz = S8 ∧ rex = 0w ∧ 4w ≤₊ r then RmHigh (w2w (r - 4w)) else RmReg r) ∧
  sized sz rex (RmHigh h) = RmHigh h ∧
  sized sz rex (RmMem a) = RmMem a
End

(* A k-byte little-endian immediate, sign-extended (k = 1, 2 or 4) or whole
   (k = 8). *)
Definition imm_value_def:
  imm_value k (v:word64) =
    if k = 1 then sw2sw (w2w v : word8) : word64
    else if k = 2 then sw2sw (w2w v : word16)
    else if k = 4 then sw2sw (w2w v : word32)
    else v
End

Definition immediate_def:
  immediate k bytes =
    if LENGTH bytes < k then Truncated
    else Decoded (imm_value k (le_word (TAKE k bytes))) k
End

(* The bytes of the immediate of a size-sz form. *)
Definition imm_bytes_def:
  imm_bytes S8 = 1n ∧ imm_bytes S16 = 2 ∧ imm_bytes S32 = 4 ∧ imm_bytes S64 = 4
End

(* A ModRM operand followed by a k-byte immediate (none for k = 0). *)
Definition modrm_imm_def:
  modrm_imm bits k bytes =
    case decode_modrm bits bytes of
      Decoded (reg, rm) n =>
        (case immediate k (DROP n bytes) of
           Decoded v m => Decoded (reg, rm, v) (n + m)
         | other => unmatched other)
    | other => unmatched other
End

(* The ModRM reg field of an opcode group, before the ModRM byte is decoded. *)
Definition reg_field_def:
  reg_field [] = NONE ∧
  reg_field (m::rest) = SOME ((5 >< 3) m : word3)
End

Definition alu_def:
  alu (d:word3) =
    if d = 0w then ADD else if d = 1w then OR else if d = 2w then ADC
    else if d = 3w then SBB else if d = 4w then AND else if d = 5w then SUB
    else if d = 6w then XOR else CMP
End

Definition rotate_op_def:
  rotate_op (d:word3) = if d = 0w then ROL else if d = 1w then ROR else if d = 2w then RCL else RCR
End

Definition bt_op_def:
  bt_op (d:word2) = if d = 0w then BT else if d = 1w then BTS else if d = 2w then BTR else BTC
End

(* A4..A7 and AA..AF; F3 repeats, as does F2 but before CMPS and SCAS,
   where it is REPNE. *)
Definition string_op_def:
  string_op (op:word8) =
    if op <₊ 0xA6w then MOVS else if op <₊ 0xA8w then CMPS else if op <₊ 0xACw then STOS
    else if op <₊ 0xAEw then LODS else SCAS
End

Definition string_rep_def:
  string_rep (op:word8) (rep:word8) =
    if rep = 0w then NoRep
    else if rep = 0xF2w ∧ (string_op op = CMPS ∨ string_op op = SCAS) then RepNE
    else RepE
End

(* A ModRM operand that must be a register: other operands are rejected
   from the ModRM byte, before any SIB or displacement byte. *)
Definition decode_reg_modrm_def:
  decode_reg_modrm bits [] = Truncated ∧
  decode_reg_modrm bits (modrm::rest) =
    if (7 >< 6) modrm = (3w:word2) then decode_modrm bits (modrm::rest) else Rejected
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

(* 0F 38 F0, F1 and F6 after the prefixes, with the bytes from F0, F1 or F6
   on and the number of bytes from the 0F on: MOVBE (no repeat prefix, a
   memory operand), CRC32 (F2: a byte source from F0, a full-size one from
   F1) and ADCX (66) or ADOX (F3, with or without 66). *)
Definition decode_0f38_def:
  decode_0f38 pf [] = Truncated ∧
  decode_0f38 pf (c::rest) =
    let rex = pf.rex; bits = rex_bits rex; sz = op_size pf in
      if c = 0xF6w then
        (if pf.rep = 0xF2w ∨ ¬pf.opsize ∧ pf.rep ≠ 0xF3w then Rejected
         else case modrm_imm bits 0 rest of
                Decoded (reg, rm, _) n =>
                  Decoded (Adx (pf.rep = 0xF3w) (if word_bit 3 rex then S64 else S32) reg rm) (3 + n)
              | other => unmatched other)
      else if pf.rep = 0xF2w then
        (case modrm_imm bits 0 rest of
           Decoded (reg, rm, _) n =>
             Decoded (if c = 0xF0w then Crc32 S8 reg (sized S8 rex rm) else Crc32 sz reg rm) (3 + n)
         | other => unmatched other)
      else if pf.rep = 0xF3w then Rejected
      else
        case decode_modrm bits rest of
          Decoded (reg, RmMem a) n =>
            Decoded (if c = 0xF0w then Movbe sz (RmReg reg) (RmMem a)
                     else Movbe sz (RmMem a) (RmReg reg)) (3 + n)
        | other => unmatched other
End

(* The two-byte opcodes 0F b after the prefixes, with the bytes from b on
   and the number of bytes from the 0F on. A repeat prefix is ignored where
   the opcode doesn't use it; the vector forms take a lone 66, F2 or F3 as
   their mandatory prefix. *)
Definition decode_0f_def:
  decode_0f pf [] = Truncated ∧
  decode_0f pf (b::rest) =
    let rex = pf.rex; bits = rex_bits rex; sz = op_size pf;
        bsz = if word_bit 0 b then sz else S8
    in
      if b = 0x38w ∧ (case rest of c::_ => c = 0xF0w ∨ c = 0xF1w ∨ c = 0xF6w | [] => T) then
        decode_0f38 pf rest
      (* The hint NOPs, except the prefetches (0F 0D and 0F 18 /0..3 with a
         memory operand), CLDEMOTE (0F 1C /0 with a memory operand and no
         66, F2 or F3) and RDSSP (F3 0F 1E /1 with a register operand). *)
      else if b = 0x0Dw ∨ 0x18w ≤₊ b ∧ b ≤₊ 0x1Fw then
        (case rest of
           [] => Truncated
         | m::_ =>
             let d = (5 >< 3) m : word3; mem = ((7 >< 6) m ≠ (3w:word2)) in
               if b = 0x0Dw ∧ mem ∨ b = 0x18w ∧ mem ∧ d <₊ 4w ∨
                  b = 0x1Cw ∧ mem ∧ d = 0w ∧ ¬pf.opsize ∧ pf.rep = 0w ∨
                  b = 0x1Ew ∧ ¬mem ∧ d = 1w ∧ pf.rep = 0xF3w
               then Rejected
               else case modrm_imm bits 0 rest of
                      Decoded _ n => Decoded Nop (2 + n)
                    | other => unmatched other)
      else if b && 0xF0w = 0x40w then
        (case modrm_imm bits 0 rest of
           Decoded (reg, rm, _) n => Decoded (Cmov (w2w b) sz reg rm) (2 + n)
         | other => unmatched other)
      else if b && 0xF0w = 0x80w then
        (if pf.opsize then Rejected
         else case immediate 4 rest of
                Decoded d n => Decoded (Jcc (w2w b) d) (2 + n)
              | other => unmatched other)
      else if b && 0xF0w = 0x90w then
        (case modrm_imm bits 0 rest of
           Decoded (_, rm, _) n => Decoded (Setcc (w2w b) (sized S8 rex rm)) (2 + n)
         | other => unmatched other)
      else if b = 0xA3w ∨ b = 0xABw ∨ b = 0xB3w ∨ b = 0xBBw then
        (case modrm_imm bits 0 rest of
           Decoded (reg, rm, _) n => Decoded (Bt (bt_op ((4 >< 3) b)) sz rm reg) (2 + n)
         | other => unmatched other)
      else if b = 0xBAw then
        (case reg_field rest of
           NONE => Truncated
         | SOME d =>
             if ¬word_bit 2 d then Rejected
             else case modrm_imm bits 1 rest of
                    Decoded (reg, rm, v) n => Decoded (BtImm (bt_op (w2w d)) sz rm (w2w v)) (2 + n)
                  | other => unmatched other)
      else if b = 0xA4w ∨ b = 0xA5w ∨ b = 0xACw ∨ b = 0xADw then
        (case modrm_imm bits (if word_bit 0 b then 0 else 1) rest of
           Decoded (reg, rm, v) n =>
             Decoded (ShiftDouble (b <₊ 0xA8w) sz rm reg (if word_bit 0 b then NONE else SOME (w2w v)))
                     (2 + n)
         | other => unmatched other)
      else if b = 0xAFw then
        (case modrm_imm bits 0 rest of
           Decoded (reg, rm, _) n => Decoded (Imul sz reg rm NONE) (2 + n)
         | other => unmatched other)
      else if b = 0xB0w ∨ b = 0xB1w ∨ b = 0xC0w ∨ b = 0xC1w then
        (case modrm_imm bits 0 rest of
           Decoded (reg, rm, _) n =>
             let d = sized bsz rex rm; s = sized bsz rex (RmReg reg) in
               Decoded (if b <₊ 0xC0w then Cmpxchg bsz d s else Xadd bsz d s) (2 + n)
         | other => unmatched other)
      else if b = 0xB6w ∨ b = 0xB7w ∨ b = 0xBEw ∨ b = 0xBFw then
        (case modrm_imm bits 0 rest of
           Decoded (reg, rm, _) n =>
             Decoded (if word_bit 0 b then Movx (word_bit 3 b) sz S16 reg rm
                      else Movx (word_bit 3 b) sz S8 reg (sized S8 rex rm)) (2 + n)
         | other => unmatched other)
      else if b = 0xB8w ∨ b = 0xBCw ∨ b = 0xBDw then
        (if b = 0xB8w ∧ pf.rep ≠ 0xF3w then Rejected
         else case modrm_imm bits 0 rest of
                Decoded (reg, rm, _) n =>
                  Decoded (if pf.rep = 0xF3w then
                             BitCount (if b = 0xBCw then TZCNT else if b = 0xBDw then LZCNT else POPCNT)
                                      sz reg rm
                           else BitScan (b = 0xBDw) sz reg rm) (2 + n)
              | other => unmatched other)
      else if b = 0xC7w then
        (case rest of
           [] => Truncated
         | c::_ =>
             if (5 >< 3) c ≠ (1w:word3) ∨ (7 >< 6) c = (3w:word2) then Rejected
             else case decode_modrm bits rest of
                    Decoded (_, RmMem a) n => Decoded (Cmpxchg2 (word_bit 3 rex) a) (2 + n)
                  | other => unmatched other)
      else if b && 0xF8w = 0xC8w then Decoded (Bswap sz (reg_num (word_bit 0 rex) (w2w b))) 2
      else if pf.opsize ∧ pf.rep ≠ 0w then Rejected
      else decode_sse (if pf.rep ≠ 0w then pf.rep else if pf.opsize then 0x66w else 0w) rex (b::rest)
End

(* The VEX-encoded BMI1 and BMI2 forms after a C4 byte, with the number of
   bytes from the C4 on: the first VEX byte holds the inverted R, X and B
   bits and the opcode map (2: 0F38, 3: 0F3A), the second W (64-bit
   operands), the inverted register vvvv, L and the implied prefix pp (0:
   none, 1: 66, 2: F3, 3: F2). Forms with L = 1, other maps, and RORX with
   vvvv in use are rejected from the byte that holds them. *)
Definition decode_vex_def:
  decode_vex [] = Truncated ∧
  decode_vex (b1::rest) =
    let mmap = (4 >< 0) b1 : word5 in
      if mmap ≠ 2w ∧ mmap ≠ 3w then Rejected
      else case rest of
        [] => Truncated
      | b2::rest' =>
          let v = ¬((6 >< 3) b2) : word4; pp = (1 >< 0) b2 : word2;
              bits = (¬word_bit 7 b1, ¬word_bit 6 b1, ¬word_bit 5 b1);
              sz = if word_bit 7 b2 then S64 else S32
          in
            if word_bit 2 b2 ∨ mmap = 3w ∧ (pp ≠ 3w ∨ v ≠ 0w) then Rejected
            else case rest' of
              [] => Truncated
            | op::modrm =>
                if mmap = 3w then
                  (if op ≠ 0xF0w then Rejected
                   else case modrm_imm bits 1 modrm of
                          Decoded (d, src, imm) n => Decoded (Rorx sz d src (w2w imm)) (4 + n)
                        | other => unmatched other)
                else if op = 0xF6w ∧ pp = 3w ∨ op = 0xF7w ∨ op = 0xF5w ∧ pp ≠ 1w ∨
                        op = 0xF2w ∧ pp = 0w then
                  (case modrm_imm bits 0 modrm of
                     Decoded (d, src, _) n =>
                       Decoded (if op = 0xF6w then Mulx sz d v src
                                else if op = 0xF7w then
                                  (if pp = 0w then Bextr sz d src v
                                   else ShiftX (if pp = 1w then SHL else if pp = 3w then SHR else SAR)
                                               sz d src v)
                                else if op = 0xF5w then
                                  (if pp = 0w then Bzhi sz d src v
                                   else Pdep (if pp = 3w then PDEP else PEXT) sz d v src)
                                else Andn sz d v src) (4 + n)
                   | other => unmatched other)
                else if op = 0xF3w ∧ pp = 0w then
                  (case reg_field modrm of
                     NONE => Truncated
                   | SOME g =>
                       if g ≠ 1w ∧ g ≠ 2w ∧ g ≠ 3w then Rejected
                       else case modrm_imm bits 0 modrm of
                              Decoded (_, src, _) n =>
                                Decoded (Bls (if g = 1w then BLSR else if g = 2w then BLSMSK else BLSI)
                                             sz v src) (4 + n)
                            | other => unmatched other)
                else Rejected
End

(* The instruction after the prefixes, from its opcode byte op on, with the
   number of bytes from op on. A 66 prefix before a near branch is rejected:
   Intel and AMD CPUs execute it differently. *)
Definition decode_one_def:
  decode_one pf (op:word8) rest =
    let rex = pf.rex; bits = rex_bits rex; sz = op_size pf; ssz = stack_size pf;
        bsz = if word_bit 0 op then sz else S8;
        rb = reg_num (word_bit 0 rex) (w2w op)
    in
      if op <₊ 0x40w ∧ (op && 7w) <₊ 4w then
        (case modrm_imm bits 0 rest of
           Decoded (reg, rm, _) n =>
             let r = sized bsz rex (RmReg reg); m = sized bsz rex rm in
               Decoded (if word_bit 1 op then Binop (alu (w2w (op >>> 3))) bsz r m
                        else Binop (alu (w2w (op >>> 3))) bsz m r) (1 + n)
         | other => unmatched other)
      else if op <₊ 0x40w ∧ (op && 6w) = 4w then
        (case immediate (imm_bytes bsz) rest of
           Decoded v n => Decoded (BinopImm (alu (w2w (op >>> 3))) bsz (RmReg 0w) v) (1 + n)
         | other => unmatched other)
      else if op && 0xF8w = 0x50w then Decoded (Push ssz (RmReg rb)) 1
      else if op && 0xF8w = 0x58w then Decoded (Pop ssz (RmReg rb)) 1
      else if op = 0x63w then
        (case modrm_imm bits 0 rest of
           Decoded (reg, rm, _) n => Decoded (Movx T sz (if sz = S64 then S32 else sz) reg rm) (1 + n)
         | other => unmatched other)
      else if op = 0x68w ∨ op = 0x6Aw then
        (case immediate (if op = 0x6Aw then 1 else imm_bytes ssz) rest of
           Decoded v n => Decoded (PushImm ssz v) (1 + n)
         | other => unmatched other)
      else if op = 0x69w ∨ op = 0x6Bw then
        (case modrm_imm bits (if op = 0x6Bw then 1 else imm_bytes sz) rest of
           Decoded (reg, rm, v) n => Decoded (Imul sz reg rm (SOME v)) (1 + n)
         | other => unmatched other)
      else if op && 0xF0w = 0x70w then
        (if pf.opsize then Rejected
         else case immediate 1 rest of
                Decoded d n => Decoded (Jcc (w2w op) d) (1 + n)
              | other => unmatched other)
      else if op = 0x80w ∨ op = 0x81w ∨ op = 0x83w then
        (case modrm_imm bits (if op = 0x81w then imm_bytes sz else 1) rest of
           Decoded (reg, rm, v) n =>
             let s = if op = 0x80w then S8 else sz in
               Decoded (BinopImm (alu (w2w reg)) s (sized s rex rm) v) (1 + n)
         | other => unmatched other)
      else if 0x84w ≤₊ op ∧ op ≤₊ 0x8Bw then
        (case modrm_imm bits 0 rest of
           Decoded (reg, rm, _) n =>
             let r = sized bsz rex (RmReg reg); m = sized bsz rex rm in
               Decoded (if op <₊ 0x86w then Binop TEST bsz m r
                        else if op <₊ 0x88w then Xchg bsz m r
                        else if word_bit 1 op then Mov bsz r m
                        else Mov bsz m r) (1 + n)
         | other => unmatched other)
      else if op = 0x8Dw then
        (case decode_modrm bits rest of
           Decoded (reg, RmMem a) n => Decoded (Lea sz reg a) (1 + n)
         | other => unmatched other)
      else if op = 0x8Fw then
        (case reg_field rest of
           NONE => Truncated
         | SOME d =>
             if d ≠ 0w then Rejected
             else case modrm_imm bits 0 rest of
                    Decoded (_, rm, _) n => Decoded (Pop ssz rm) (1 + n)
                  | other => unmatched other)
      else if op && 0xF8w = 0x90w then
        (if op = 0x90w ∧ (pf.rep = 0xF3w ∨ ¬word_bit 0 rex) then Decoded Nop 1
         else Decoded (Xchg sz (RmReg rb) (RmReg 0w)) 1)
      else if op = 0x98w then Decoded (Cbw sz) 1
      else if op = 0x99w then Decoded (Cwd sz) 1
      else if op = 0x9Cw then Decoded (Pushf ssz) 1
      else if op = 0x9Dw then Decoded (Popf ssz) 1
      else if op = 0x9Ew then Decoded Sahf 1
      else if op = 0x9Fw then Decoded Lahf 1
      else if op && 0xFCw = 0xA0w then
        (case immediate 8 rest of
           Decoded a n =>
             let m = RmMem (Mem NONE NONE 0w a) in
               Decoded (if word_bit 1 op then Mov bsz m (RmReg 0w) else Mov bsz (RmReg 0w) m)
                       (1 + n)
         | other => unmatched other)
      else if op = 0xA8w ∨ op = 0xA9w then
        (case immediate (imm_bytes bsz) rest of
           Decoded v n => Decoded (BinopImm TEST bsz (RmReg 0w) v) (1 + n)
         | other => unmatched other)
      else if 0xA4w ≤₊ op ∧ op ≤₊ 0xAFw then
        Decoded (StringOp (string_op op) bsz (string_rep op pf.rep)) 1
      else if op && 0xF0w = 0xB0w then
        (let s = if op <₊ 0xB8w then S8 else sz in
           case immediate (if s = S64 then 8 else imm_bytes s) rest of
             Decoded v n => Decoded (MovImm s (sized s rex (RmReg rb)) v) (1 + n)
           | other => unmatched other)
      else if op = 0xC0w ∨ op = 0xC1w ∨ op && 0xFCw = 0xD0w then
        (case reg_field rest of
           NONE => Truncated
         | SOME d =>
             if d = 6w then Rejected
             else case modrm_imm bits (if op <₊ 0xD0w then 1 else 0) rest of
                    Decoded (_, rm, v) n =>
                      let count = if op <₊ 0xD0w then SOME (w2w v)
                                  else if op <₊ 0xD2w then SOME 1w else NONE;
                          m = sized bsz rex rm
                      in
                        Decoded (if d = 4w then Shift SHL bsz m count
                                 else if d = 5w then Shift SHR bsz m count
                                 else if d = 7w then Shift SAR bsz m count
                                 else Rotate (rotate_op d) bsz m count) (1 + n)
                  | other => unmatched other)
      else if op = 0xC2w ∨ op = 0xC3w then
        (if pf.opsize then Rejected
         else if op = 0xC3w then Decoded (Ret 0w) 1
         else case immediate 2 rest of
                Decoded v n => Decoded (Ret (w2w v)) (1 + n)
              | other => unmatched other)
      else if op = 0xC6w ∨ op = 0xC7w then
        (case reg_field rest of
           NONE => Truncated
         | SOME d =>
             if d ≠ 0w then Rejected
             else case modrm_imm bits (imm_bytes bsz) rest of
                    Decoded (_, rm, v) n => Decoded (MovImm bsz (sized bsz rex rm) v) (1 + n)
                  | other => unmatched other)
      else if op = 0xC8w then
        (case rest of
           a::b::c::_ => Decoded (Enter ssz (w2w (le_word [a; b])) c) 4
         | _ => Truncated)
      else if op = 0xC9w then Decoded (Leave ssz) 1
      else if op = 0xD7w then Decoded Xlat 1
      else if op && 0xFCw = 0xE0w then
        (if pf.opsize then Rejected
         else case immediate 1 rest of
                Decoded d n =>
                  Decoded (Loop (if op = 0xE0w then LOOPNE else if op = 0xE1w then LOOPE
                                 else if op = 0xE2w then LOOP else JRCXZ) d) (1 + n)
              | other => unmatched other)
      else if op = 0xE8w ∨ op = 0xE9w ∨ op = 0xEBw then
        (if pf.opsize then Rejected
         else case immediate (if op = 0xEBw then 1 else 4) rest of
                Decoded d n => Decoded (if op = 0xE8w then Call d else Jmp d) (1 + n)
              | other => unmatched other)
      else if op = 0xF5w then Decoded (FlagOp CMC) 1
      else if op = 0xF8w then Decoded (FlagOp CLC) 1
      else if op = 0xF9w then Decoded (FlagOp STC) 1
      else if op = 0xFCw then Decoded (FlagOp CLD) 1
      else if op = 0xFDw then Decoded (FlagOp STD) 1
      else if op = 0xF6w ∨ op = 0xF7w then
        (case reg_field rest of
           NONE => Truncated
         | SOME d =>
             if d = 1w then Rejected
             else case modrm_imm bits (if d = 0w then imm_bytes bsz else 0) rest of
                    Decoded (_, rm, v) n =>
                      let m = sized bsz rex rm in
                        Decoded (if d = 0w then BinopImm TEST bsz m v
                                 else if d = 2w then Not bsz m
                                 else if d = 3w then Neg bsz m
                                 else if d = 4w then MulWide F bsz m
                                 else if d = 5w then MulWide T bsz m
                                 else if d = 6w then Div F bsz m
                                 else Div T bsz m) (1 + n)
                  | other => unmatched other)
      else if op = 0xFEw ∨ op = 0xFFw then
        (case reg_field rest of
           NONE => Truncated
         | SOME d =>
             if op = 0xFEw ∧ 2w ≤₊ d ∨ d = 3w ∨ d = 5w ∨ d = 7w ∨
                pf.opsize ∧ (d = 2w ∨ d = 4w) then Rejected
             else case modrm_imm bits 0 rest of
                    Decoded (_, rm, _) n =>
                      let m = sized bsz rex rm in
                        Decoded (if d = 0w then Inc bsz m
                                 else if d = 1w then Dec bsz m
                                 else if d = 2w then CallInd rm
                                 else if d = 4w then JmpInd rm
                                 else Push ssz rm) (1 + n)
                  | other => unmatched other)
      else if op = 0x0Fw then decode_0f pf rest
      else if op = 0xC4w then
        (if pf.opsize ∨ pf.rep ≠ 0w ∨ rex ≠ 0w then Rejected else decode_vex rest)
      else Rejected
End

(* An instruction and its length in bytes, at most 15: prefixes, at most one
   of F2 and F3, then the opcode; a REX byte counts only as the last prefix.
   A VEX form after any REX byte is rejected, as QEMU does, rather than
   reading a REX byte before other prefixes as ignored, as XED does. *)
Definition decode_def:
  decode bytes =
    let (prefixes, body) = split_prefixes bytes;
        p = LENGTH prefixes
    in
      if has_prefix 0xF2w prefixes ∧ has_prefix 0xF3w prefixes ∨
         has_rex prefixes ∧ (case body of b::_ => b = 0xC4w | [] => F) then Rejected
      else
        let rex = (case REVERSE prefixes of
                     b::_ => if b && 0xF0w = 0x40w then b else 0w
                   | [] => 0w);
            pf = <| opsize := has_prefix 0x66w prefixes;
                    rep := (if has_prefix 0xF3w prefixes then 0xF3w
                            else if has_prefix 0xF2w prefixes then 0xF2w else 0w);
                    rex := rex |>
        in
          case body of
            [] => Truncated
          | op::more =>
              case decode_one pf op more of
                Decoded i n => if p + n ≤ 15 then Decoded i (p + n) else Rejected
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
  adx_result c sz (a:word64) b =
    let r = (a + b + (if c then 1w else 0w)) && size_mask sz in
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
   (6 at 64 bits). A masked count of 0 leaves the flags f; otherwise AF, OF
   after counts above 1, and CF after SHL or SHR by the width or more come
   from u. *)
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
        (r, <| CF := (if op = SAR then word_bit (c - 1) (sign_extend sz a)
                      else if n ≤ c then u.CF
                      else if op = SHL then word_bit (n - c) a
                      else word_bit (c - 1) a);
               PF := even_parity r;
               AF := u.AF;
               ZF := (r = 0w);
               SF := sign_bit sz r;
               OF := (if c ≠ 1 then u.OF
                      else if op = SHL then sign_bit sz a ≠ word_bit (n - 2) a
                      else if op = SHR then sign_bit sz a
                      else F) |>)
End

(* Result and flags of rotating the size-masked a by count, masked to 5 bits
   (6 at 64 bits): ROL and ROR by the masked count modulo the width; RCL and
   RCR rotate the width + 1 bits of CF and a, by the masked count modulo
   width + 1. A masked count of 0 leaves the flags f; otherwise CF is the
   bit rotated last (into CF, for RCL and RCR), OF is defined at count 1
   and comes from u above it, and PF, AF, ZF and SF keep their values. *)
Definition rotate_result_def:
  rotate_result (u:eflags) (f:eflags) op sz (a:word64) (count:word8) =
    let c = w2n (count && (if sz = S64 then 63w else 31w));
        n = 8 * size_bytes sz;
        t = (if op = ROL ∨ op = ROR then c MOD n else c MOD (n + 1));
        cin : word64 = if f.CF then 1w else 0w;
        r = (case op of
               ROL => (a << t) ‖ (a >>> (n - t))
             | ROR => (a >>> t) ‖ (a << (n - t))
             | RCL => if t = 0 then a else (a << t) ‖ (cin << (t - 1)) ‖ (a >>> (n + 1 - t))
             | RCR => if t = 0 then a else (a >>> t) ‖ (cin << (n - t)) ‖ (a << (n + 1 - t))) &&
            size_mask sz;
        carry = (case op of
                   ROL => word_bit 0 r
                 | ROR => word_bit (n - 1) r
                 | RCL => if t = 0 then f.CF else word_bit (n - t) a
                 | RCR => if t = 0 then f.CF else word_bit (t - 1) a)
    in
      if c = 0 then (r, f)
      else
        (r, f with <| CF := carry;
                      OF := (if c ≠ 1 then u.OF
                             else if op = ROL ∨ op = RCL then word_bit (n - 1) r ≠ carry
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
  w2n (ct && 63w) = w2n ct MOD 64 ∧
  w2n (31w && ct) = w2n ct MOD 32 ∧
  w2n (63w && ct) = w2n ct MOD 64
Proof
  ONCE_REWRITE_TAC [WORD_AND_COMM] >> Cases_on `ct` >>
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
  FST (rotate_result u f (if left then ROL else ROR) S32 (a && size_mask S32) ct) =
  (w2w (if left then (w2w a:word32) #<< (w2n ct MOD 32)
        else (w2w a:word32) #>> (w2n ct MOD 32)):word64)
Proof
  `a && size_mask S32 = (w2w (w2w a:word32):word64)` by
    (simp[size_mask_def] >> blastLib.BBLAST_TAC) >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  Cases_on `left` >>
  PURE_REWRITE_TAC [rotate_result_def, LET_THM] >> BETA_TAC >>
  PURE_REWRITE_TAC [fst_same] >>
  simp_tac (srw_ss()) [rotate_count_mask, size_bytes_def, size_mask_def] >>
  mp_tac (Q.INST [`x` |-> `w2w (a:word64):word32`, `n` |-> `w2n (ct:word8) MOD 32`]
           rotate32_shifts) >>
  simp[]
QED

Theorem rotate_result_value64:
  FST (rotate_result u f (if left then ROL else ROR) S64 (a && size_mask S64) ct) =
  if left then a #<< (w2n ct MOD 64) else a #>> (w2n ct MOD 64)
Proof
  `size_mask S64 = (UINT_MAXw:word64)` by EVAL_TAC >>
  Cases_on `left` >>
  PURE_REWRITE_TAC [rotate_result_def, LET_THM] >> BETA_TAC >>
  PURE_REWRITE_TAC [fst_same] >>
  pop_assum (fn th => PURE_REWRITE_TAC [th, WORD_AND_CLAUSES]) >>
  simp_tac (srw_ss()) [rotate_count_mask, size_bytes_def] >>
  mp_tac (Q.INST [`x` |-> `a:word64`, `n` |-> `w2n (ct:word8) MOD 64`]
           (INST_TYPE [alpha |-> ``:64``] rotate_right_shifts)) >>
  mp_tac (Q.INST [`x` |-> `a:word64`, `n` |-> `w2n (ct:word8) MOD 64`]
           (INST_TYPE [alpha |-> ``:64``] rotate_left_shifts)) >>
  simp[WORD_AND_CLAUSES]
QED

(* Two- and three-operand IMUL of the size-masked a and b: CF and OF report
   a signed product that does not fit the size; SF, ZF, AF and PF come from
   u. *)
Definition imul_result_def:
  imul_result (u:eflags) sz (a:word64) b =
    let r = (a * b) && size_mask sz;
        overflow = ((sw2sw (sign_extend sz a) * sw2sw (sign_extend sz b) : word128) ≠
                    sw2sw (sign_extend sz r))
    in
      (r, u with <| CF := overflow; OF := overflow |>)
End

(* One-operand MUL and IMUL: the high and low halves, each size-masked, of
   the unsigned or signed double-size product of the size-masked a and b. CF
   and OF report a high half that is not the extension of the low half;
   SF, ZF, AF and PF come from u. *)
Definition mul_wide_def:
  mul_wide (u:eflags) signed sz (a:word64) (b:word64) =
    let p : word128 = if signed then sw2sw (sign_extend sz a) * sw2sw (sign_extend sz b)
                      else w2w a * w2w b;
        lo = (w2w p : word64) && size_mask sz;
        hi = (w2w (p >>> (8 * size_bytes sz)) : word64) && size_mask sz;
        overflow = if signed then p ≠ sw2sw (sign_extend sz lo) else hi ≠ 0w
    in
      (hi, lo, u with <| CF := overflow; OF := overflow |>)
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

(* Result and flags of SHLD (left) or SHRD of the size-masked d by count,
   masked to 5 bits (6 at 64 bits), shifting in bits of src. A masked count
   of 0 leaves d and the flags f; otherwise AF, and OF after counts above 1,
   come from u. At 16 bits a count above 16 leaves the result undefined;
   execute_with does not take it here. *)
Definition shift_double_result_def:
  shift_double_result (u:eflags) (f:eflags) left sz (d:word64) (src:word64) (count:word8) =
    let c = w2n (count && (if sz = S64 then 63w else 31w));
        n = 8 * size_bytes sz;
        r = (if left then (d << c) ‖ (src >>> (n - c)) else (d >>> c) ‖ (src << (n - c))) &&
            size_mask sz
    in
      if c = 0 then (d, f)
      else
        (r, <| CF := (if left then word_bit (n - c) d else word_bit (c - 1) d);
               PF := even_parity r;
               AF := u.AF;
               ZF := (r = 0w);
               SF := sign_bit sz r;
               OF := (if c = 1 then sign_bit sz r ≠ sign_bit sz d else u.OF) |>)
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

(* The flags of ANDN, BZHI, BLSR, BLSI and BLSMSK on a size-sz result r: SF
   and ZF from r, CF as given, OF clear, and AF and PF from u. *)
Definition bmi_flags_def:
  bmi_flags (u:eflags) sz cf (r:word64) =
    <| CF := cf; PF := u.PF; AF := u.AF; ZF := (r = 0w); SF := sign_bit sz r; OF := F |>
End

(* BZHI: the size-masked a with the bits from index n (the low byte of the
   index register) up cleared, and whether n is past the top bit (CF). *)
Definition bzhi_result_def:
  bzhi_result sz (a:word64) (n:word8) =
    if w2n n < 8 * size_bytes sz then (a && ((1w << w2n n) - 1w), F) else (a, T)
End

(* BLSR, BLSI and BLSMSK of a at size sz, and CF. BLSMSK's result is never 0,
   so ZF is clear after it, as the SDM has it. *)
Definition bls_result_def:
  bls_result op sz (a:word64) =
    let a = a && size_mask sz in
      case op of
        BLSR => ((a && (a - 1w)) && size_mask sz, a = 0w)
      | BLSI => ((a && -a) && size_mask sz, a ≠ 0w)
      | BLSMSK => ((a ⊕ (a - 1w)) && size_mask sz, a = 0w)
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
  pdep_result op sz src mask =
    let n = 8 * size_bytes sz in
      case op of PDEP => pdep_aux n src mask | PEXT => pext_aux n src mask
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
  FST (bls_result BLSMSK sz a) ≠ 0w
Proof
  Cases_on `sz` >> simp[bls_result_def, size_mask_def] >> blastLib.BBLAST_TAC
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

(* The low n bytes of w in the opposite order. *)
Definition byte_swap_def:
  byte_swap n (w:word64) = le_word (REVERSE (le_bytes n w))
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
  read_aligned_xmm ops s len (RmHigh r) = Fault Unsupported ∧
  read_aligned_xmm ops s len (RmMem a) =
    let addr = address_of ops s len a in
      if addr && 15w ≠ 0w then Fault Alignment
      else case load128 ops addr s of
             NONE => Fault Load
           | SOME value => Next value
End

(* A size-sz value v written to register r: 8- and 16-bit writes keep the
   other bits, 32-bit writes clear the upper half. *)
Definition write_sized_def:
  write_sized ops sz r v s = write_reg ops r (merge_reg sz (read_reg ops s r) v) s
End

Definition read_operand_def:
  read_operand ops sz s len (RmReg r) = SOME (read_reg ops s r && size_mask sz) ∧
  read_operand ops sz s len (RmHigh r) = SOME ((read_reg ops s (w2w r) >>> 8) && 0xFFw) ∧
  read_operand ops sz s len (RmMem a) = load ops (size_bytes sz) (address_of ops s len a) s
End

Definition write_operand_def:
  write_operand ops sz s len (RmReg r) v = Next (write_sized ops sz r v s) ∧
  write_operand ops sz s len (RmHigh r) v =
    Next (write_reg ops (w2w r)
            ((read_reg ops s (w2w r) && ¬0xFF00w) ‖ ((v && 0xFFw) << 8)) s) ∧
  write_operand ops sz s len (RmMem a) v =
    store ops (size_bytes sz) (address_of ops s len a) v s
End

Definition next_rip_def:
  next_rip len (Next s) = Next (s with rip := s.rip + n2w len) ∧
  next_rip len (Fault f) = Fault f
End

(* Push the low size-sz bytes of v. *)
Definition push_def:
  push ops sz (v:word64) s =
    let sp = read_reg ops s 4w - n2w (size_bytes sz) in
      case store ops (size_bytes sz) sp v s of
        Next t => Next (write_reg ops 4w sp t)
      | Fault f => Fault f
End

(* ENTER's copies of k enclosing frame pointers, read downwards from fp. *)
Definition enter_frames_def:
  enter_frames ops sz 0 (fp:word64) s = Next s ∧
  enter_frames ops sz (SUC k) fp s =
    let fp' = fp - n2w (size_bytes sz) in
      case load ops (size_bytes sz) fp' s of
        NONE => Fault Load
      | SOME v =>
          case push ops sz v s of
            Next t => enter_frames ops sz k fp' t
          | Fault f => Fault f
End

(* RFLAGS as PUSHF stores it: the status flags, DF, the reserved bit 1 and
   IF, which is always set in user mode. *)
Definition flags_word_def:
  flags_word f df : word64 =
    (if f.CF then 1w else 0w) ‖ 2w ‖ (if f.PF then 4w else 0w) ‖
    (if f.AF then 0x10w else 0w) ‖ (if f.ZF then 0x40w else 0w) ‖
    (if f.SF then 0x80w else 0w) ‖ 0x200w ‖ (if df then 0x400w else 0w) ‖
    (if f.OF then 0x800w else 0w)
End

Definition word_flags_def:
  word_flags (v:word64) =
    <| CF := word_bit 0 v; PF := word_bit 2 v; AF := word_bit 4 v;
       ZF := word_bit 6 v; SF := word_bit 7 v; OF := word_bit 11 v |>
End

(* One iteration of a string instruction, without moving RIP. RSI and RDI
   step by the operand size, down when DF is set. *)
Definition string_step_def:
  string_step ops u op sz s =
    let n = size_bytes sz;
        d = (if s.df then -n2w n else n2w n);
        si = read_reg ops s 6w; di = read_reg ops s 7w
    in
      case op of
        MOVS =>
          (case load ops n si s of
             NONE => Fault Load
           | SOME v =>
               case store ops n di v s of
                 Next t => Next (write_reg ops 7w (di + d) (write_reg ops 6w (si + d) t))
               | Fault f => Fault f)
      | CMPS =>
          (case load ops n si s of
             NONE => Fault Load
           | SOME a =>
               case load ops n di s of
                 NONE => Fault Load
               | SOME b =>
                   Next (write_reg ops 7w (di + d) (write_reg ops 6w (si + d) s)
                         with flags := SND (binop_result u F sz CMP a b)))
      | STOS =>
          (case store ops n di (read_reg ops s 0w) s of
             Next t => Next (write_reg ops 7w (di + d) t)
           | Fault f => Fault f)
      | LODS =>
          (case load ops n si s of
             NONE => Fault Load
           | SOME v => Next (write_reg ops 6w (si + d) (write_sized ops sz 0w v s)))
      | SCAS =>
          (case load ops n di s of
             NONE => Fault Load
           | SOME b =>
               Next (write_reg ops 7w (di + d) s
                     with flags := SND (binop_result u F sz CMP (read_reg ops s 0w && size_mask sz) b)))
End

(* The byte address of the operand-size unit holding bit offset off of a bit
   string in memory, relative to its base. *)
Definition bit_base_def:
  bit_base sz (off:word64) = (sign_extend sz off >> 3) && ¬(n2w (size_bytes sz) - 1w)
End

Definition bt_result_def:
  bt_result op (a:word64) i =
    let m = (1w:word64) << i in
      case op of BT => a | BTS => a ‖ m | BTR => a && ¬m | BTC => a ⊕ m
End

(* One instruction of len bytes at s.rip. Operand addresses are computed in
   s, before RIP moves past the instruction. Results the SDM leaves
   undefined (BSF and BSR of 0, 16-bit SHLD and SHRD by more than 16, a
   16-bit BSWAP) fault Unsupported. *)
Definition execute_with_def:
  execute_with ops u (MovImm sz d imm) len s =
    next_rip len (write_operand ops sz s len d (imm && size_mask sz)) ∧
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
  execute_with ops u (Movx signed dsz ssz r src) len s =
    (case read_operand ops ssz s len src of
       NONE => Fault Load
     | SOME v =>
         Next (write_sized ops dsz r ((if signed then sign_extend ssz v else v) && size_mask dsz) s
               with rip := s.rip + n2w len)) ∧
  execute_with ops u (Cbw sz) len s =
    (let h = (case sz of S16 => S8 | S32 => S16 | _ => S32) in
       Next (write_sized ops sz 0w (sign_extend h (read_reg ops s 0w) && size_mask sz) s
             with rip := s.rip + n2w len)) ∧
  execute_with ops u (Cwd sz) len s =
    Next (write_sized ops sz 2w (if sign_bit sz (read_reg ops s 0w) then size_mask sz else 0w) s
          with rip := s.rip + n2w len) ∧
  execute_with ops u (Lea sz r a) len s =
    Next (write_sized ops sz r (address_of ops s len a && size_mask sz) s
          with rip := s.rip + n2w len) ∧
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
  execute_with ops u (Dec sz d) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         let (v, f) = binop_result u F sz SUB a 1w in
           next_rip len (write_operand ops sz (s with flags := (f with CF := s.flags.CF)) len d v)) ∧
  execute_with ops u (Shift op sz d count) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         let c = (case count of SOME c => c | NONE => w2w (read_reg ops s 1w));
             (v, f) = shift_result u s.flags sz op a c
         in
           next_rip len (write_operand ops sz (s with flags := f) len d v)) ∧
  execute_with ops u (Rotate op sz d count) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         let c = (case count of SOME c => c | NONE => w2w (read_reg ops s 1w));
             (v, f) = rotate_result u s.flags op sz a c
         in
           next_rip len (write_operand ops sz (s with flags := f) len d v)) ∧
  execute_with ops u (Imul sz r src imm) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME b =>
         let a = (case imm of SOME v => v | NONE => read_reg ops s r) && size_mask sz;
             (v, f) = imul_result u sz a b
         in
           Next (write_sized ops sz r v s with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (MulWide signed sz src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME b =>
         let (hi, lo, f) = mul_wide u signed sz (read_reg ops s 0w && size_mask sz) b;
             t = (if sz = S8 then write_sized ops S16 0w ((hi << 8) ‖ lo) s
                  else write_sized ops sz 2w hi (write_sized ops sz 0w lo s))
         in
           Next (t with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Div signed sz src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME d =>
         let a = read_reg ops s 0w;
             hi = (if sz = S8 then a >>> 8 else read_reg ops s 2w)
         in
           case div_result signed sz hi a d of
             NONE => Fault Divide
           | SOME (q, r) =>
               let t = (if sz = S8 then write_sized ops S16 0w ((r << 8) ‖ q) s
                        else write_sized ops sz 2w r (write_sized ops sz 0w q s))
               in
                 Next (t with <| flags := u; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (ShiftDouble left sz d src count) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         let c = (case count of SOME c => c | NONE => w2w (read_reg ops s 1w)) in
           if sz = S16 ∧ 16 < w2n (c && 31w) then Fault Unsupported
           else
             let (v, f) = shift_double_result u s.flags left sz a
                            (read_reg ops s src && size_mask sz) c
             in
               next_rip len (write_operand ops sz (s with flags := f) len d v)) ∧
  execute_with ops u (Bswap sz r) len s =
    (if sz = S16 then Fault Unsupported
     else Next (write_sized ops sz r (byte_swap (size_bytes sz) (read_reg ops s r)) s
                with rip := s.rip + n2w len)) ∧
  execute_with ops u (Xchg sz a b) len s =
    (case read_operand ops sz s len a of
       NONE => Fault Load
     | SOME va =>
         case read_operand ops sz s len b of
           NONE => Fault Load
         | SOME vb =>
             case write_operand ops sz s len a vb of
               Next t => next_rip len (write_operand ops sz t len b va)
             | Fault f => Fault f) ∧
  execute_with ops u (Xadd sz d src) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         case read_operand ops sz s len src of
           NONE => Fault Load
         | SOME b =>
             let (v, f) = binop_result u F sz ADD a b; s' = s with flags := f in
               (* A memory destination is stored first, at the address its
                  registers give before the source register changes; a
                  register destination is written last, so that XADD r, r
                  leaves the sum. *)
               case d of
                 RmMem _ =>
                   (case write_operand ops sz s' len d v of
                      Next t => next_rip len (write_operand ops sz t len src a)
                    | Fault e => Fault e)
               | _ =>
                   (case write_operand ops sz s' len src a of
                      Next t => next_rip len (write_operand ops sz t len d v)
                    | Fault e => Fault e)) ∧
  execute_with ops u (Cmpxchg sz d src) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         case read_operand ops sz s len src of
           NONE => Fault Load
         | SOME b =>
             let acc = read_reg ops s 0w && size_mask sz;
                 f = SND (binop_result u F sz CMP acc a)
             in
               if acc = a then next_rip len (write_operand ops sz (s with flags := f) len d b)
               else
                 (* On failure only a memory destination is written (back);
                    a register keeps its upper half. *)
                 case (case d of
                         RmMem _ => write_operand ops sz (s with flags := f) len d a
                       | _ => Next (s with flags := f)) of
                   Next t => Next (write_sized ops sz 0w a t with rip := s.rip + n2w len)
                 | Fault e => Fault e) ∧
  execute_with ops u (Cmpxchg2 wide m) len s =
    (let addr = address_of ops s len m;
         lo = read_reg ops s 0w; hi = read_reg ops s 2w
     in
       if wide then
         if addr && 15w ≠ 0w then Fault Alignment
         else
           case load128 ops addr s of
             NONE => Fault Load
           | SOME v =>
               let same = (v = (w2w hi << 64) ‖ w2w lo) in
                 case store128 ops addr
                        (if same then (w2w (read_reg ops s 1w) << 64) ‖ w2w (read_reg ops s 3w) else v) s of
                   Fault f => Fault f
                 | Next t =>
                     let t = (if same then t else write_reg ops 2w (w2w (v >>> 64)) (write_reg ops 0w (w2w v) t)) in
                       Next (t with <| flags := t.flags with ZF := same; rip := s.rip + n2w len |>)
       else
         case load ops 8 addr s of
           NONE => Fault Load
         | SOME v =>
             let same = (v = (hi << 32) ‖ (lo && 0xFFFFFFFFw)) in
               case store ops 8 addr
                      (if same then (read_reg ops s 1w << 32) ‖ (read_reg ops s 3w && 0xFFFFFFFFw) else v) s of
                 Fault f => Fault f
               | Next t =>
                   let t = (if same then t else write_reg ops 2w (v >>> 32) (write_reg ops 0w (v && 0xFFFFFFFFw) t)) in
                     Next (t with <| flags := t.flags with ZF := same; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Bt op sz d r) len s =
    (let off = read_reg ops s r && size_mask sz;
         i = w2n off MOD (8 * size_bytes sz);
         m = (case d of RmMem a => RmMem (Mem NONE NONE 0w (address_of ops s len a + bit_base sz off))
                      | _ => d)
     in
       case read_operand ops sz s len m of
         NONE => Fault Load
       | SOME a =>
           let f = u with <| CF := word_bit i a; ZF := s.flags.ZF |> in
             if op = BT then Next (s with <| flags := f; rip := s.rip + n2w len |>)
             else next_rip len (write_operand ops sz (s with flags := f) len m (bt_result op a i))) ∧
  execute_with ops u (BtImm op sz d imm) len s =
    (case read_operand ops sz s len d of
       NONE => Fault Load
     | SOME a =>
         let i = w2n imm MOD (8 * size_bytes sz);
             f = u with <| CF := word_bit i a; ZF := s.flags.ZF |>
         in
           if op = BT then Next (s with <| flags := f; rip := s.rip + n2w len |>)
           else next_rip len (write_operand ops sz (s with flags := f) len d (bt_result op a i))) ∧
  execute_with ops u (BitScan rev sz r src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME a =>
         let n = 8 * size_bytes sz in
           if a = 0w then Fault Unsupported
           else
             Next (write_sized ops sz r
                     (n2w (if rev then n - 1 - leading_zeros n a else trailing_zeros n a)) s
                   with <| flags := u with ZF := F; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (BitCount op sz r src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME a =>
         let (v, f) = bit_count_result u op (8 * size_bytes sz) a in
           Next (write_sized ops sz r v s with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Adx overflow sz r src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME b =>
         let c = (if overflow then s.flags.OF else s.flags.CF);
             (v, carry) = adx_result c sz (read_reg ops s r && size_mask sz) b;
             f = (if overflow then s.flags with OF := carry else s.flags with CF := carry)
         in
           Next (write_sized ops sz r v s with <| flags := f; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Movbe sz d src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME v => next_rip len (write_operand ops sz s len d (byte_swap (size_bytes sz) v))) ∧
  execute_with ops u (Crc32 sz r src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME v =>
         Next (write_reg ops r (w2w (crc32c_bits (8 * size_bytes sz) (w2w (read_reg ops s r)) v)) s
               with rip := s.rip + n2w len)) ∧
  execute_with ops u (Cmov cc sz r src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME v =>
         Next (write_sized ops sz r (if condition cc s.flags then v else read_reg ops s r) s
               with rip := s.rip + n2w len)) ∧
  execute_with ops u (Setcc cc d) len s =
    next_rip len (write_operand ops S8 s len d (if condition cc s.flags then 1w else 0w)) ∧
  execute_with ops u (Mulx sz hi lo src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME b =>
         let (h, l, f) = mul_wide u F sz (read_reg ops s 2w && size_mask sz) b in
           Next (write_sized ops sz hi h (write_sized ops sz lo l s) with rip := s.rip + n2w len)) ∧
  execute_with ops u (Rorx sz d src imm) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME a =>
         Next (write_sized ops sz d (FST (rotate_result u s.flags ROR sz a imm)) s
               with rip := s.rip + n2w len)) ∧
  execute_with ops u (ShiftX op sz d src cnt) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME a =>
         Next (write_sized ops sz d (FST (shift_result u s.flags sz op a (w2w (read_reg ops s cnt)))) s
               with rip := s.rip + n2w len)) ∧
  execute_with ops u (Andn sz d a src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME b =>
         let r = ¬read_reg ops s a && b in
           Next (write_sized ops sz d r s with <| flags := bmi_flags u sz F r; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Bzhi sz d src n) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME a =>
         let (r, cf) = bzhi_result sz a (w2w (read_reg ops s n)) in
           Next (write_sized ops sz d r s with <| flags := bmi_flags u sz cf r; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Bls op sz d src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME a =>
         let (r, cf) = bls_result op sz a in
           Next (write_sized ops sz d r s with <| flags := bmi_flags u sz cf r; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Pdep op sz d a src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME mask =>
         Next (write_sized ops sz d (pdep_result op sz (read_reg ops s a && size_mask sz) mask) s
               with rip := s.rip + n2w len)) ∧
  execute_with ops u (Bextr sz d src c) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME a =>
         let r = bextr_result a (read_reg ops s c && size_mask sz) in
           Next (write_sized ops sz d r s with <| flags := bextr_flags u r; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (Push sz src) len s =
    (case read_operand ops sz s len src of
       NONE => Fault Load
     | SOME v => next_rip len (push ops sz v s)) ∧
  execute_with ops u (PushImm sz v) len s = next_rip len (push ops sz v s) ∧
  execute_with ops u (Pop sz d) len s =
    (let sp = read_reg ops s 4w in
       case load ops (size_bytes sz) sp s of
         NONE => Fault Load
       | SOME v =>
           next_rip len (write_operand ops sz (write_reg ops 4w (sp + n2w (size_bytes sz)) s) len d v)) ∧
  execute_with ops u (Pushf sz) len s = next_rip len (push ops sz (flags_word s.flags s.df) s) ∧
  execute_with ops u (Popf sz) len s =
    (let sp = read_reg ops s 4w in
       case load ops (size_bytes sz) sp s of
         NONE => Fault Load
       | SOME v =>
           if v && 0x244100w ≠ 0w then Fault Unsupported
           else
             Next (write_reg ops 4w (sp + n2w (size_bytes sz)) s
                   with <| flags := word_flags v; df := word_bit 10 v; rip := s.rip + n2w len |>)) ∧
  execute_with ops u Lahf len s =
    next_rip len (write_operand ops S8 s len (RmHigh 0w) (flags_word s.flags s.df && 0xFFw)) ∧
  execute_with ops u Sahf len s =
    (let v = (read_reg ops s 0w >>> 8) && 0xFFw ‖ (if s.flags.OF then 0x800w else 0w) in
       Next (s with <| flags := word_flags v; rip := s.rip + n2w len |>)) ∧
  execute_with ops u (FlagOp op) len s =
    Next ((case op of
             CLC => s with flags := s.flags with CF := F
           | STC => s with flags := s.flags with CF := T
           | CMC => s with flags := s.flags with CF := ¬s.flags.CF
           | CLD => s with df := F
           | STD => s with df := T) with rip := s.rip + n2w len) ∧
  execute_with ops u (Leave sz) len s =
    (let sp = read_reg ops s 5w in
       case load ops (size_bytes sz) sp s of
         NONE => Fault Load
       | SOME v =>
           Next (write_sized ops sz 5w v (write_reg ops 4w (sp + n2w (size_bytes sz)) s)
                 with rip := s.rip + n2w len)) ∧
  execute_with ops u (Enter sz alloc level) len s =
    (let fp = read_reg ops s 5w; l = w2n level MOD 32 in
       case push ops sz fp s of
         Fault f => Fault f
       | Next t =>
           let frame = read_reg ops t 4w in
             case (if l = 0 then Next t
                   else case enter_frames ops sz (l - 1) fp t of
                          Next t' => push ops sz frame t'
                        | Fault f => Fault f) of
               Fault f => Fault f
             | Next t' =>
                 let sp = read_reg ops t' 4w - w2w alloc in
                   (* ENTER faults if a write at the final stack pointer would. *)
                   if access_ok ops Write (size_bytes sz) t' sp then
                     Next (write_reg ops 4w sp (write_sized ops sz 5w frame t')
                           with rip := s.rip + n2w len)
                   else Fault Store) ∧
  execute_with ops u (Call d) len s =
    (let ret = s.rip + n2w len in
       case push ops S64 ret s of
         Next t => Next (t with rip := ret + d)
       | Fault f => Fault f) ∧
  execute_with ops u (CallInd src) len s =
    (case read_operand ops S64 s len src of
       NONE => Fault Load
     | SOME target =>
         case push ops S64 (s.rip + n2w len) s of
           Next t => Next (t with rip := target)
         | Fault f => Fault f) ∧
  execute_with ops u (Jcc cc d) len s =
    Next (s with rip := s.rip + n2w len + (if condition cc s.flags then d else 0w)) ∧
  execute_with ops u (Jmp d) len s = Next (s with rip := s.rip + n2w len + d) ∧
  execute_with ops u (JmpInd src) len s =
    (case read_operand ops S64 s len src of
       NONE => Fault Load
     | SOME target => Next (s with rip := target)) ∧
  execute_with ops u (Loop op d) len s =
    (let c = read_reg ops s 1w in
       if op = JRCXZ then
         Next (s with rip := s.rip + n2w len + (if c = 0w then d else 0w))
       else
         let c = c - 1w;
             taken = (c ≠ 0w ∧ (op = LOOP ∨ (op = LOOPE ⇔ s.flags.ZF)))
         in
           Next (write_reg ops 1w c s with rip := s.rip + n2w len + (if taken then d else 0w))) ∧
  execute_with ops u (Ret n) len s =
    (let sp = read_reg ops s 4w in
       case load ops 8 sp s of
         NONE => Fault Load
       | SOME v => Next (write_reg ops 4w (sp + 8w + w2w n) s with rip := v)) ∧
  execute_with ops u Xlat len s =
    (case load ops 1 (read_reg ops s 3w + (read_reg ops s 0w && 0xFFw)) s of
       NONE => Fault Load
     | SOME v => Next (write_sized ops S8 0w v s with rip := s.rip + n2w len)) ∧
  execute_with ops u (StringOp op sz rep) len s =
    (let c = read_reg ops s 1w in
       if rep ≠ NoRep ∧ c = 0w then Next (s with rip := s.rip + n2w len)
       else
         case string_step ops u op sz s of
           Fault f => Fault f
         | Next t =>
             if rep = NoRep then Next (t with rip := s.rip + n2w len)
             else
               let c = c - 1w;
                   t = write_reg ops 1w c t;
                   stop = (c = 0w ∨ (op = CMPS ∨ op = SCAS) ∧ (rep = RepE ⇔ ¬t.flags.ZF))
               in
                 Next (if stop then t with rip := s.rip + n2w len else t)) ∧
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
