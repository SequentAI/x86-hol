(* Which flags the model leaves to the undefined-flag argument u, checked
   against AWS s2n-bignum's x86 semantics (x86/proofs/x86.ml): its x86_AND,
   x86_OR, x86_TEST and x86_XOR end in UNDEFINED_VALUES[AF] with CF and OF
   cleared; x86_ADD, x86_ADC, x86_SUB, x86_SBB and x86_CMP define every flag;
   x86_SHL, x86_SHR and x86_SAR leave the flags alone at a masked count of 0
   and otherwise end in UNDEFINED_VALUES[AF], with OF undefined unless the
   count is 1; x86_IMUL defines CF and OF only (UNDEFINED_VALUES[ZF;SF;PF;AF]);
   so do x86_MUL2 and x86_IMUL2 (one-operand MUL and IMUL); x86_SHLD and
   x86_SHRD treat the flags as the single shifts do; x86_ROL and x86_ROR
   leave the flags alone at a masked count of 0 and otherwise set CF and
   OF only, OF to UNDEFINED_VALUES unless the count is 1; x86_TZCNT and x86_LZCNT
   define CF and ZF only (UNDEFINED_VALUES[OF;SF;PF;AF]); x86_POPCNT defines
   every flag. s2n-bignum has no DIV or IDIV: the Intel SDM leaves CF, OF,
   SF, ZF, AF and PF undefined after both. x86_NOT, x86_MOVSX, x86_MOV,
   x86_SET and x86_CMOV leave every flag alone. x86_MULX4 writes no flag.
   x86_ADCX writes only CF and x86_ADOX only OF; neither uses undefined
   flags. MOVBE writes no flag (Intel SDM), nor do MOVDQA, PSHUFLW,
   PSHUFHW, PSHUFB, the packed immediate shifts PSLLD, PSRLD, PSLLQ and
   PSRLQ, the byte shifts PSLLDQ and PSRLDQ, PALIGNR, PCLMULQDQ, AES-NI and
   MOVQ xmm, r64.
   s2n-bignum has no RORX, SHLX, SHRX, SARX, ANDN, BZHI, BLSR, BLSI or
   BLSMSK; the Intel SDM's Flags Affected for them: none for RORX, SHLX,
   SHRX and SARX; for ANDN, SF and ZF from the result and CF and OF cleared;
   for BZHI, ZF and SF from the result, CF set when the index is past the
   top bit, OF cleared; for BLSR and BLSI, ZF and SF from the result, CF
   set when the source is zero (BLSR) or nonzero (BLSI), OF cleared; for
   BLSMSK, SF from the result, CF set when the source is zero, ZF and OF
   cleared; AF and PF undefined after all five. x86_PEXT writes no flag;
   s2n-bignum has no PDEP or BEXTR, and the SDM has PDEP write none and
   BEXTR set ZF from the result, clear CF and OF, and leave AF, SF and PF
   undefined. x86_RCL and x86_RCR treat the flags as x86_ROL and x86_ROR
   do. x86_BT, x86_BTC, x86_BTR and x86_BTS set CF to the selected bit and
   leave ZF, SF, PF, OF and AF undefined; the Intel SDM leaves ZF
   unaffected, as the model does. x86_BSF and x86_BSR set ZF and leave CF,
   OF, SF, PF and AF undefined. XADD, CMPXCHG, CMPS and SCAS set the flags
   as ADD and CMP do; CMPXCHG8B and CMPXCHG16B write ZF only (Intel SDM). *)
Theory x86UndefinedFlags
Ancestors x86Isa

Theorem logic_flags:
  op = OR ∨ op = AND ∨ op = XOR ∨ op = TEST ⇒
  (SND (binop_result u c sz op a b)).AF = u.AF ∧
  ¬(SND (binop_result u c sz op a b)).CF ∧
  ¬(SND (binop_result u c sz op a b)).OF
Proof
  rw[binop_result_def] >> simp[]
QED

(* u reaches no output of a binop but AF. *)
Theorem binop_undefined_af_only:
  FST (binop_result u c sz op a b) = FST (binop_result u' c sz op a b) ∧
  SND (binop_result u c sz op a b) with AF := F = SND (binop_result u' c sz op a b) with AF := F
Proof
  rw[binop_result_def, LET_THM]
QED

(* A shift whose masked count k is 0 leaves the flags f as they were. *)
Theorem shift_zero_count_flags:
  w2n (k && (if sz = S64 then 63w else 31w)) = 0 ⇒
  SND (shift_result u f sz op a k) = f
Proof
  rw[shift_result_def]
QED

(* Otherwise u reaches AF always, OF unless the masked count is 1, and CF
   after SHL or SHR by the operand width or more (8- and 16-bit only). *)
Theorem shift_undefined_flags:
  w2n (k && (if sz = S64 then 63w else 31w)) ≠ 0 ⇒
  (SND (shift_result u f sz op a k)).AF = u.AF ∧
  (w2n (k && (if sz = S64 then 63w else 31w)) ≠ 1 ⇒
   (SND (shift_result u f sz op a k)).OF = u.OF) ∧
  (op ≠ SAR ∧ 8 * size_bytes sz ≤ w2n (k && (if sz = S64 then 63w else 31w)) ⇒
   (SND (shift_result u f sz op a k)).CF = u.CF)
Proof
  rw[shift_result_def, LET_THM]
QED

Theorem shift_undefined_af_of_cf_only:
  u.AF = u'.AF ∧ u.OF = u'.OF ∧ u.CF = u'.CF ⇒ shift_result u = shift_result u'
Proof
  rw[FUN_EQ_THM, shift_result_def]
QED

Triviality masked_count_bound:
  ¬(32 ≤ w2n (31w && (k:word8))) ∧ ¬(32 ≤ w2n (k && 31w)) ∧
  ¬(64 ≤ w2n (63w && k)) ∧ ¬(64 ≤ w2n (k && 63w))
Proof
  `31w && k <₊ 32w ∧ k && 31w <₊ 32w ∧ 63w && k <₊ 64w ∧ k && 63w <₊ (64w:word8)` by
    blastLib.BBLAST_TAC >>
  fs[wordsTheory.WORD_LO, arithmeticTheory.NOT_LESS_EQUAL]
QED

Triviality write_operand_flags:
  next_rip len (write_operand ops sz s len d v) = Next t ⇒ t.flags = s.flags
Proof
  Cases_on `d` >> rw[write_operand_def, store_def, next_rip_def, write_sized_def, write_reg_def] >>
  simp[x86_machine_accfupds, write_bytes_fields]
QED

(* NOT, MOVZX, MOVSX, MOV of an immediate, SETcc and CMOVcc leave the flags
   as they were. *)
Theorem flags_unchanged:
  (i = Not sz d ∨ i = Movx sg dsz sz r src ∨ i = MovImm sz d v ∨ i = Setcc cc d ∨
   i = Cmov cc sz r src) ∧
  execute_with ops u i len s = Next t ⇒ t.flags = s.flags
Proof
  rw[] >> gvs[execute_with_def, AllCaseEqs()] >>
  imp_res_tac write_operand_flags >> gvs[write_sized_def, write_reg_def, x86_machine_accfupds]
QED

(* IMUL defines CF and OF and leaves the rest to u. *)
Theorem imul_undefined_flags:
  SND (imul_result u sz a b) with <| CF := F; OF := F |> = u with <| CF := F; OF := F |>
Proof
  rw[imul_result_def, LET_THM]
QED

(* MUL and IMUL with one operand: the same. *)
Theorem mul_wide_undefined_flags:
  SND (SND (mul_wide u sg sz a b)) with <| CF := F; OF := F |> = u with <| CF := F; OF := F |>
Proof
  rw[mul_wide_def, LET_THM]
QED

(* DIV and IDIV take every flag from u. *)
Theorem div_undefined_flags:
  execute_with ops u (Div sg sz src) len s = Next t ⇒ t.flags = u
Proof
  rw[execute_with_def, AllCaseEqs()] >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >> rw[] >> simp[write_sized_def, write_reg_def]
QED

(* SHLD and SHRD: as the single shifts. *)
Theorem shift_double_zero_count_flags:
  w2n (k && (if sz = S64 then 63w else 31w)) = 0 ⇒
  SND (shift_double_result u f left sz a b k) = f
Proof
  rw[shift_double_result_def]
QED

Theorem shift_double_undefined_flags:
  w2n (k && (if sz = S64 then 63w else 31w)) ≠ 0 ⇒
  (SND (shift_double_result u f left sz a b k)).AF = u.AF ∧
  (w2n (k && (if sz = S64 then 63w else 31w)) ≠ 1 ⇒
   (SND (shift_double_result u f left sz a b k)).OF = u.OF)
Proof
  rw[shift_double_result_def, LET_THM]
QED

(* ROL, ROR, RCL and RCR: a masked count of 0 leaves the flags f;
   otherwise they change CF and OF only, OF from u unless the masked count
   is 1. *)
Theorem rotate_zero_count_flags:
  w2n (k && (if sz = S64 then 63w else 31w)) = 0 ⇒
  SND (rotate_result u f op sz a k) = f
Proof
  rw[rotate_result_def]
QED

Theorem rotate_undefined_flags:
  w2n (k && (if sz = S64 then 63w else 31w)) ≠ 0 ⇒
  SND (rotate_result u f op sz a k) with <| CF := F; OF := F |> =
    f with <| CF := F; OF := F |> ∧
  (w2n (k && (if sz = S64 then 63w else 31w)) ≠ 1 ⇒
   (SND (rotate_result u f op sz a k)).OF = u.OF)
Proof
  PURE_REWRITE_TAC [rotate_result_def, LET_THM] >> BETA_TAC >> strip_tac >>
  ASM_REWRITE_TAC [pairTheory.SND] >>
  qmatch_goalsub_abbrev_tac `f with <|CF := cy; OF := ov|>` >>
  simp[Abbr `ov`]
QED

(* TZCNT and LZCNT define CF and ZF and leave the rest to u; POPCNT takes
   nothing from u. *)
Theorem bit_count_undefined_flags:
  op ≠ POPCNT ⇒
  SND (bit_count_result u op n a) with <| CF := F; ZF := F |> = u with <| CF := F; ZF := F |>
Proof
  Cases_on `op` >> rw[bit_count_result_def, LET_THM]
QED

Theorem popcnt_flags_defined:
  bit_count_result u POPCNT n a = bit_count_result u' POPCNT n a
Proof
  rw[bit_count_result_def]
QED

Theorem binop_agrees:
  op = ADD ∨ op = ADC ∨ op = SUB ∨ op = SBB ∨ op = CMP ∨ u.AF = u'.AF ⇒
  ∀c sz. binop_result u c sz op = binop_result u' c sz op
Proof
  rw[FUN_EQ_THM, binop_result_def] >> ASM_REWRITE_TAC[]
QED

Theorem shift_agrees:
  (w2n (k && (if sz = S64 then 63w else 31w)) ≠ 0 ⇒ u.AF = u'.AF) ∧
  (1 < w2n (k && (if sz = S64 then 63w else 31w)) ⇒ u.OF = u'.OF) ∧
  (op ≠ SAR ∧ 8 * size_bytes sz ≤ w2n (k && (if sz = S64 then 63w else 31w)) ⇒ u.CF = u'.CF) ⇒
  shift_result u f sz op a k = shift_result u' f sz op a k
Proof
  strip_tac >> simp[shift_result_def, LET_THM] >>
  qabbrev_tac `c = w2n (k && (if sz = S64 then 63w else 31w))` >>
  IF_CASES_TAC >- simp[] >>
  `c ≠ 0` by gvs[Abbr `c`] >>
  `c ≠ 1 ⇒ (u.OF ⇔ u'.OF)` by (strip_tac >> first_x_assum irule >> decide_tac) >>
  rw[] >> gvs[]
QED

Theorem imul_agrees:
  u.SF = u'.SF ∧ u.ZF = u'.ZF ∧ u.AF = u'.AF ∧ u.PF = u'.PF ⇒
  imul_result u = imul_result u'
Proof
  rw[FUN_EQ_THM, imul_result_def, eflags_component_equality]
QED

Theorem mul_wide_agrees:
  u.SF = u'.SF ∧ u.ZF = u'.ZF ∧ u.AF = u'.AF ∧ u.PF = u'.PF ⇒
  mul_wide u = mul_wide u'
Proof
  rw[FUN_EQ_THM, mul_wide_def, eflags_component_equality]
QED

Theorem shift_double_agrees:
  (w2n (k && (if sz = S64 then 63w else 31w)) ≠ 0 ⇒ u.AF = u'.AF) ∧
  (1 < w2n (k && (if sz = S64 then 63w else 31w)) ⇒ u.OF = u'.OF) ⇒
  shift_double_result u f left sz a b k = shift_double_result u' f left sz a b k
Proof
  strip_tac >> simp[shift_double_result_def, LET_THM] >>
  qabbrev_tac `c = w2n (k && (if sz = S64 then 63w else 31w))` >>
  IF_CASES_TAC >- simp[] >>
  `c ≠ 0` by gvs[Abbr `c`] >>
  `c ≠ 1 ⇒ (u.OF ⇔ u'.OF)` by (strip_tac >> first_x_assum irule >> decide_tac) >>
  rw[] >> gvs[]
QED

Theorem rotate_agrees:
  (1 < w2n (k && (if sz = S64 then 63w else 31w)) ⇒ u.OF = u'.OF) ⇒
  rotate_result u f op sz a k = rotate_result u' f op sz a k
Proof
  strip_tac >> PURE_REWRITE_TAC [rotate_result_def, LET_THM] >> BETA_TAC >>
  qabbrev_tac `c = w2n (k && (if sz = S64 then 63w else 31w))` >>
  Cases_on `c = 0` >> ASM_REWRITE_TAC [] >>
  `c ≠ 1 ⇒ (u.OF ⇔ u'.OF)` by (strip_tac >> first_x_assum irule >> decide_tac) >>
  Cases_on `c = 1` >> ASM_REWRITE_TAC [] >> res_tac >> ASM_REWRITE_TAC []
QED

Theorem bit_count_agrees:
  (op ≠ POPCNT ⇒ u.OF = u'.OF ∧ u.SF = u'.SF ∧ u.PF = u'.PF ∧ u.AF = u'.AF) ⇒
  bit_count_result u op = bit_count_result u' op
Proof
  Cases_on `op` >> rw[FUN_EQ_THM, bit_count_result_def, eflags_component_equality]
QED

(* ANDN, BZHI, BLSR, BLSI and BLSMSK take AF and PF from u and clear OF. *)
Theorem bmi_undefined_flags:
  (bmi_flags u sz cf r).AF = u.AF ∧ (bmi_flags u sz cf r).PF = u.PF ∧ ¬(bmi_flags u sz cf r).OF
Proof
  simp[bmi_flags_def]
QED

(* BLSMSK's result is never 0, so it clears ZF. *)
Theorem blsmsk_clears_zf:
  ¬(bmi_flags u sz (SND (bls_result BLSMSK sz a)) (FST (bls_result BLSMSK sz a))).ZF
Proof
  simp[bmi_flags_def, blsmsk_nonzero]
QED

Theorem bmi_flags_agrees:
  u.AF = u'.AF ∧ u.PF = u'.PF ⇒ bmi_flags u = bmi_flags u'
Proof
  rw[FUN_EQ_THM, bmi_flags_def]
QED

(* The masked count of a shift by cnt, as execute_with computes it. *)
Definition shift_count_def:
  shift_count ops s sz cnt =
    w2n ((case cnt of SOME c => c | NONE => w2w (read_reg ops s 1w)) &&
         (if sz = S64 then 63w else 31w))
End

Theorem adx_flag_writes:
  execute_with ops u (Adx overflow sz d src) len s = Next t ⇒
  t.flags = if overflow then s.flags with OF := t.flags.OF
            else s.flags with CF := t.flags.CF
Proof
  Cases_on `overflow` >>
  rw[execute_with_def, AllCaseEqs(), pairTheory.ELIM_UNCURRY] >> simp[]
QED

Theorem movbe_flags_unchanged:
  execute_with ops u (Movbe sz d src) len s = Next t ⇒ t.flags = s.flags
Proof
  rw[execute_with_def, AllCaseEqs()] >> imp_res_tac write_operand_flags
QED

Theorem shuffle_shift_flags_unchanged:
  (execute_with ops u (VecMov d x) len s = Next t ∨
   execute_with ops u (Pshufw high d x imm) len s = Next t ∨
   execute_with ops u (Pshufb d src) len s = Next t ∨
   execute_with ops u (Pshift left sz x imm) len s = Next t ∨
   execute_with ops u (Psrad x imm) len s = Next t) ⇒ t.flags = s.flags
Proof
  rw[execute_with_def, write_xmm_def] >>
  gvs[AllCaseEqs(), write_xmm_def]
QED

Theorem aes_flags_unchanged:
  (execute_with ops u (AesRound op d src) len s = Next t ∨
   execute_with ops u (AesImc d x) len s = Next t ∨
   execute_with ops u (PxorMem d a) len s = Next t) ⇒ t.flags = s.flags
Proof
  rw[execute_with_def, write_xmm_def] >>
  gvs[AllCaseEqs(), write_xmm_def]
QED

Theorem clmul_flags_unchanged:
  (execute_with ops u (Pclmul d x imm) len s = Next t ∨
   execute_with ops u (Pshiftdq left x imm) len s = Next t ∨
   execute_with ops u (MovqXmm x r) len s = Next t ∨
   execute_with ops u (AesKeygen d x imm) len s = Next t ∨
   execute_with ops u (Palignr d x imm) len s = Next t) ⇒ t.flags = s.flags
Proof
  rw[execute_with_def, write_xmm_def] >> simp[]
QED

Theorem qword_lane_flags_unchanged:
  (execute_with ops u (Pinsrq x src imm) len s = Next t ∨
   execute_with ops u (Pextrq dst x imm) len s = Next t ∨
   execute_with ops u (Punpcklqdq x y) len s = Next t) ⇒ t.flags = s.flags
Proof
  rw[execute_with_def, LET_THM] >>
  gvs[AllCaseEqs(), write_xmm_def, next_rip_def] >>
  Cases_on `dst` >>
  gvs[write_operand_def, write_sized_def, write_reg_def, store_def, next_rip_def] >>
  Cases_on `access_ok ops Write (size_bytes S64) s (address_of ops s len a)` >>
  gvs[next_rip_def, write_bytes_fields]
QED

Theorem dword_lane_flags_unchanged:
  (execute_with ops u (Pinsrd x src imm) len s = Next t ∨
   execute_with ops u (Pextrd dst x imm) len s = Next t ∨
   execute_with ops u (MovdXmm x src) len s = Next t) ⇒ t.flags = s.flags
Proof
  rw[execute_with_def, LET_THM] >>
  gvs[AllCaseEqs(), write_xmm_def, next_rip_def] >>
  Cases_on `dst` >>
  gvs[write_operand_def, write_sized_def, write_reg_def, store_def, next_rip_def] >>
  Cases_on `access_ok ops Write (size_bytes S32) s (address_of ops s len a)` >>
  gvs[next_rip_def, write_bytes_fields]
QED

Theorem blend_compare_widen_flags_unchanged:
  (execute_with ops u (Pblendvb d src) len s = Next t ∨
   execute_with ops u (Pcmpd gt d src) len s = Next t ∨
   execute_with ops u (Pwiden signed sz d a) len s = Next t) ⇒ t.flags = s.flags
Proof
  rw[execute_with_def] >>
  gvs[AllCaseEqs(), write_xmm_def]
QED

(* Each instruction depends on u through the flags it leaves undefined
   only: AF after OR, AND, XOR and TEST; AF after a shift or double shift
   by a nonzero masked count, OF after one by more than 1, and CF after an
   8- or 16-bit SHL or SHR by the operand width or more; OF after a
   rotate by more than 1; SF, ZF, AF
   and PF after IMUL and one-operand MUL and IMUL; every flag after DIV and
   IDIV; OF, SF, PF and AF after TZCNT, LZCNT and the bit tests; CF, OF,
   SF, PF and AF after BSF and BSR; AF and PF after ANDN, BZHI, BLSR, BLSI
   and BLSMSK; AF, SF and PF after BEXTR; none after any other
   instruction. *)
Triviality shift_result_fst:
  ∀u u' f sz op a k. FST (shift_result u f sz op a k) = FST (shift_result u' f sz op a k)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [shift_result_def, LET_THM] >> BETA_TAC >>
  COND_CASES_TAC >> REWRITE_TAC [pairTheory.FST]
QED

Theorem execute_undefined_flags:
  (case i of
     Binop op sz d r => op = ADD ∨ op = ADC ∨ op = SUB ∨ op = SBB ∨ op = CMP ∨ u.AF = u'.AF
   | BinopImm op sz d imm =>
       op = ADD ∨ op = ADC ∨ op = SUB ∨ op = SBB ∨ op = CMP ∨ u.AF = u'.AF
   | Shift op sz d cnt =>
       (shift_count ops s sz cnt ≠ 0 ⇒ u.AF = u'.AF) ∧
       (1 < shift_count ops s sz cnt ⇒ u.OF = u'.OF) ∧
       (op ≠ SAR ∧ 8 * size_bytes sz ≤ shift_count ops s sz cnt ⇒ u.CF = u'.CF)
   | Imul sz r src imm => u.SF = u'.SF ∧ u.ZF = u'.ZF ∧ u.AF = u'.AF ∧ u.PF = u'.PF
   | MulWide sg sz src => u.SF = u'.SF ∧ u.ZF = u'.ZF ∧ u.AF = u'.AF ∧ u.PF = u'.PF
   | Div sg sz src => u = u'
   | ShiftDouble left sz d src cnt =>
       (shift_count ops s sz cnt ≠ 0 ⇒ u.AF = u'.AF) ∧
       (1 < shift_count ops s sz cnt ⇒ u.OF = u'.OF)
   | Rotate op sz d cnt => (1 < shift_count ops s sz cnt ⇒ u.OF = u'.OF)
   | Bt op sz d r => u.OF = u'.OF ∧ u.SF = u'.SF ∧ u.PF = u'.PF ∧ u.AF = u'.AF
   | BtImm op sz d imm => u.OF = u'.OF ∧ u.SF = u'.SF ∧ u.PF = u'.PF ∧ u.AF = u'.AF
   | BitScan rev sz r src =>
       u.CF = u'.CF ∧ u.OF = u'.OF ∧ u.SF = u'.SF ∧ u.PF = u'.PF ∧ u.AF = u'.AF
   | BitCount op sz d src => op ≠ POPCNT ⇒ u.OF = u'.OF ∧ u.SF = u'.SF ∧ u.PF = u'.PF ∧ u.AF = u'.AF
   | Andn sz d a b => u.AF = u'.AF ∧ u.PF = u'.PF
   | Bzhi sz d a n => u.AF = u'.AF ∧ u.PF = u'.PF
   | Bls op sz d a => u.AF = u'.AF ∧ u.PF = u'.PF
   | Bextr sz d a c => u.AF = u'.AF ∧ u.SF = u'.SF ∧ u.PF = u'.PF
   | _ => T) ⇒
  execute_with ops u i len s = execute_with ops u' i len s
Proof
  Cases_on `i` >> simp[]
  >~ [`Binop`] >- (disch_then (assume_tac o MATCH_MP binop_agrees) >> simp[execute_with_def])
  >~ [`BinopImm`] >- (disch_then (assume_tac o MATCH_MP binop_agrees) >> simp[execute_with_def])
  >~ [`Neg`] >- (assume_tac (Q.INST [`op` |-> `SUB`] binop_agrees) >> gvs[execute_with_def])
  >~ [`Inc`] >- (assume_tac (Q.INST [`op` |-> `ADD`] binop_agrees) >> gvs[execute_with_def])
  >~ [`Dec`] >- (assume_tac (Q.INST [`op` |-> `SUB`] binop_agrees) >> gvs[execute_with_def])
  >~ [`Xadd`] >- (assume_tac (Q.INST [`op` |-> `ADD`] binop_agrees) >> gvs[execute_with_def])
  >~ [`Cmpxchg`] >- (assume_tac (Q.INST [`op` |-> `CMP`] binop_agrees) >> gvs[execute_with_def])
  >~ [`StringOp`]
  >- (assume_tac (Q.INST [`op` |-> `CMP`] binop_agrees) >> gvs[execute_with_def, string_step_def])
  >~ [`BtImm`] >- (Cases_on `u` >> Cases_on `u'` >> rw[] >> simp[execute_with_def, eflags_fn_updates])
  >~ [`Bt`] >- (Cases_on `u` >> Cases_on `u'` >> rw[] >> simp[execute_with_def, eflags_fn_updates])
  >~ [`BitScan`] >- (Cases_on `u` >> Cases_on `u'` >> rw[] >> simp[execute_with_def, eflags_fn_updates])
  >~ [`Imul`] >- (disch_then (assume_tac o MATCH_MP imul_agrees) >> simp[execute_with_def])
  >~ [`MulWide`] >- (disch_then (assume_tac o MATCH_MP mul_wide_agrees) >> simp[execute_with_def])
  >~ [`BitCount`] >- (disch_then (assume_tac o MATCH_MP bit_count_agrees) >> simp[execute_with_def])
  >~ [`Andn`] >- (disch_then (assume_tac o MATCH_MP bmi_flags_agrees) >> simp[execute_with_def])
  >~ [`Bzhi`] >- (disch_then (assume_tac o MATCH_MP bmi_flags_agrees) >> simp[execute_with_def])
  >~ [`Bls`] >- (disch_then (assume_tac o MATCH_MP bmi_flags_agrees) >> simp[execute_with_def])
  >~ [`Bextr`] >- rw[execute_with_def, bextr_flags_def]
  >~ [`Mulx`] >- (simp[execute_with_def] >> CASE_TAC >> simp[mul_wide_def])
  >~ [`Rorx`] >- simp[execute_with_def, rotate_result_def, COND_RAND]
  >~ [`ShiftX`]
  >- (qspecl_then [`u`, `u'`] assume_tac shift_result_fst >> asm_simp_tac (srw_ss()) [execute_with_def])
  >~ [`ShiftDouble`]
  >- (rw[execute_with_def] >> rpt CASE_TAC >>
      qmatch_goalsub_abbrev_tac `shift_double_result u fl lft sz' xa xb xk` >>
      `shift_double_result u fl lft sz' xa xb xk = shift_double_result u' fl lft sz' xa xb xk`
        by (irule shift_double_agrees >> gvs[shift_count_def, Abbr `xk`]) >>
      simp[])
  >~ [`Rotate`]
  >- (rw[execute_with_def] >> rpt CASE_TAC >>
      qmatch_goalsub_abbrev_tac `rotate_result u fl op' sz' xa xk` >>
      `rotate_result u fl op' sz' xa xk = rotate_result u' fl op' sz' xa xk`
        by (irule rotate_agrees >> gvs[shift_count_def, Abbr `xk`]) >>
      simp[])
  >~ [`Shift`]
  >- (rw[execute_with_def] >> rpt CASE_TAC >>
      qmatch_goalsub_abbrev_tac `shift_result u fl sz' op' a' k'` >>
      `shift_result u fl sz' op' a' k' = shift_result u' fl sz' op' a' k'`
        by (irule shift_agrees >> gvs[shift_count_def, Abbr `k'`]) >>
      simp[]) >>
  simp[execute_with_def]
QED

(* No instruction but DIV, IDIV, BSF, BSR and 8- and 16-bit SHL and SHR
   takes CF from u. *)
Theorem binop_ignores_undefined_cf:
  binop_result (u with CF := x) = binop_result u
Proof
  rw[FUN_EQ_THM, binop_result_def]
QED

Theorem shift_ignores_undefined_cf:
  sz = S32 ∨ sz = S64 ⇒ ∀f. shift_result (u with CF := x) f sz = shift_result u f sz
Proof
  rw[] >> rw[FUN_EQ_THM, shift_result_def, size_bytes_def, masked_count_bound]
QED

Theorem imul_ignores_undefined_cf:
  imul_result (u with CF := x) = imul_result u
Proof
  rw[FUN_EQ_THM, imul_result_def]
QED

Theorem mul_wide_ignores_undefined_cf:
  mul_wide (u with CF := x) = mul_wide u
Proof
  rw[FUN_EQ_THM, mul_wide_def]
QED

Theorem shift_double_ignores_undefined_cf:
  shift_double_result (u with CF := x) = shift_double_result u
Proof
  rw[FUN_EQ_THM, shift_double_result_def]
QED

Theorem crc32_flags_unchanged:
  execute_with ops u (Crc32 sz d src) len s = Next t ⇒ t.flags = s.flags
Proof
  simp[execute_with_def] >> CASE_TAC >> strip_tac >> gvs[write_reg_def]
QED

Theorem pbinop_flags_unchanged:
  execute_with ops u (Pbinop op d x) len s = Next t ⇒ t.flags = s.flags
Proof
  rw[execute_with_def] >> simp[write_xmm_def]
QED

Theorem ptest_flags_defined:
  execute_with ops u (Ptest d x) len s = Next t ⇒
  t.flags = <| CF := (¬read_xmm ops s d && read_xmm ops s x = 0w);
               PF := F; AF := F; ZF := (read_xmm ops s d && read_xmm ops s x = 0w);
               SF := F; OF := F |>
Proof
  rw[execute_with_def] >> simp[ptest_flags_def]
QED

Theorem rotate_ignores_undefined_cf:
  rotate_result (u with CF := x) = rotate_result u
Proof
  REWRITE_TAC[FUN_EQ_THM] >> rpt gen_tac >>
  REWRITE_TAC[rotate_result_def, eflags_accfupds]
QED

Theorem bit_count_ignores_undefined_cf:
  bit_count_result (u with CF := x) op = bit_count_result u op
Proof
  Cases_on `op` >> rw[FUN_EQ_THM, bit_count_result_def]
QED

Theorem bmi_flags_ignores_undefined_cf:
  bmi_flags (u with CF := x) = bmi_flags u
Proof
  rw[FUN_EQ_THM, bmi_flags_def]
QED

Theorem bextr_flags_ignores_undefined_cf:
  bextr_flags (u with CF := x) = bextr_flags u
Proof
  rw[FUN_EQ_THM, bextr_flags_def]
QED

Theorem execute_ignores_undefined_cf:
  (∀sg sz r. i ≠ Div sg sz r) ∧ (∀rv sz r src. i ≠ BitScan rv sz r src) ∧
  (∀op sz d cnt. i = Shift op sz d cnt ⇒ sz = S32 ∨ sz = S64) ⇒
  execute_with ops (u with CF := x) i len s = execute_with ops u i len s
Proof
  Cases_on `i` >> simp[]
  >~ [`Shift`]
  >- (rw[] >> simp[execute_with_def, shift_ignores_undefined_cf])
  >~ [`ShiftX`]
  >- (qspecl_then [`u with CF := x`, `u`] assume_tac shift_result_fst >>
      asm_simp_tac (srw_ss()) [execute_with_def]) >>
  REWRITE_TAC[execute_with_def, string_step_def, binop_ignores_undefined_cf,
              imul_ignores_undefined_cf,
              mul_wide_ignores_undefined_cf, shift_double_ignores_undefined_cf,
              rotate_ignores_undefined_cf, bit_count_ignores_undefined_cf,
              bmi_flags_ignores_undefined_cf, bextr_flags_ignores_undefined_cf] >>
  simp[]
QED

Theorem step_ignores_undefined_cf:
  (∀sg sz r n. decode (read_bytes functional_storage (fetchable functional_storage 15 s s.rip)
                         s s.rip) ≠ Decoded (Div sg sz r) n) ∧
  (∀rv sz r src n. decode (read_bytes functional_storage (fetchable functional_storage 15 s s.rip)
                             s s.rip) ≠ Decoded (BitScan rv sz r src) n) ∧
  (∀op sz d cnt n. decode (read_bytes functional_storage (fetchable functional_storage 15 s s.rip)
                             s s.rip) = Decoded (Shift op sz d cnt) n ⇒ sz = S32 ∨ sz = S64) ⇒
  step (u with CF := x) s = step u s
Proof
  rw[step_def, step_with_def] >> CASE_TAC >> simp[] >>
  irule execute_ignores_undefined_cf >> metis_tac[]
QED
