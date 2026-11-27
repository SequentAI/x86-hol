(* An executable instance of x86Isa over sparse maps, translated for cv_eval,
   with a kernel-checked refinement of the function-valued step. *)
Theory x86IsaCv
Ancestors x86Isa x86Aes RoundOp Mult tables words cv_std sptree
Libs cv_transLib wordsLib

Type finite_state = ``:(word64 spt, word8 spt, perm spt, word128 spt) x86_machine``

Definition no_access_def:
  no_access = <| read := F; write := F; execute := F |>
End

Definition lookup_word_def:
  lookup_word default tree (address : 'a word) =
    case lookup (w2n address) tree of NONE => default | SOME value => value
End

Definition insert_word_def:
  insert_word (address : 'a word) value tree = insert (w2n address) value tree
End

Definition finite_storage_def:
  finite_storage = <|
    get_reg := (λf (r:word4). lookup_word (0w:word64) f r);
    put_reg := (λ(r:word4) (v:word64) f. insert_word r v f);
    get_xmm := (λf (r:word4). lookup_word (0w:word128) f r);
    put_xmm := (λ(r:word4) (v:word128) f. insert_word r v f);
    get_byte := (λf (a:word64). lookup_word (0w:word8) f a);
    put_byte := (λ(a:word64) (v:word8) f. insert_word a v f);
    get_perm := (λf (a:word64). lookup_word no_access f a)
  |>
End

Definition abstract_state_def:
  abstract_state (s:finite_state) : x86_state =
    <| regs := lookup_word 0w s.regs;
       xmm := lookup_word 0w s.xmm;
       rip := s.rip;
       flags := s.flags;
       df := s.df;
       mem := lookup_word 0w s.mem;
       perms := lookup_word no_access s.perms |>
End

Definition abstract_result_def:
  abstract_result (Next s) = Next (abstract_state s) ∧
  abstract_result (Fault reason) = Fault reason
End

Theorem lookup_word_insert[simp]:
  lookup_word default (insert_word a v tree) =
    (a =+ v) (lookup_word default tree)
Proof
  rw[FUN_EQ_THM, lookup_word_def, insert_word_def, lookup_insert,
     combinTheory.APPLY_UPDATE_THM] >> Cases_on `x = a` >> gvs[]
QED

Triviality abstract_reads:
  read_reg functional_storage (abstract_state s) r = read_reg finite_storage s r ∧
  read_xmm functional_storage (abstract_state s) x = read_xmm finite_storage s x ∧
  functional_storage.get_byte (abstract_state s).mem a = finite_storage.get_byte s.mem a ∧
  functional_storage.get_perm (abstract_state s).perms a = finite_storage.get_perm s.perms a ∧
  (abstract_state s).rip = s.rip ∧
  (abstract_state s).flags = s.flags ∧
  (abstract_state s).df = s.df
Proof
  simp[read_reg_def, read_xmm_def, functional_storage_def, finite_storage_def,
       abstract_state_def]
QED

Triviality abstract_updates:
  (abstract_state s with rip := p) = abstract_state (s with rip := p) ∧
  (abstract_state s with flags := f) = abstract_state (s with flags := f) ∧
  (abstract_state s with df := d) = abstract_state (s with df := d) ∧
  write_reg functional_storage r v (abstract_state s) =
    abstract_state (write_reg finite_storage r v s) ∧
  write_xmm functional_storage x w (abstract_state s) =
    abstract_state (write_xmm finite_storage x w s)
Proof
  simp[write_reg_def, write_xmm_def, functional_storage_def, finite_storage_def,
       abstract_state_def]
QED

Triviality abstract_write_bytes:
  ∀bs a s. write_bytes functional_storage bs a (abstract_state s) =
           abstract_state (write_bytes finite_storage bs a s)
Proof
  Induct >> simp[write_bytes_def] >> rpt gen_tac >>
  first_x_assum (fn th => REWRITE_TAC [GSYM th]) >>
  AP_TERM_TAC >>
  simp[abstract_state_def, functional_storage_def, finite_storage_def]
QED

Triviality abstract_read_bytes:
  ∀n s a. read_bytes functional_storage n (abstract_state s) a =
          read_bytes finite_storage n s a
Proof
  Induct >> simp[read_bytes_def, abstract_reads]
QED

Triviality abstract_access_ok:
  ∀n s k a. access_ok functional_storage k n (abstract_state s) a =
            access_ok finite_storage k n s a
Proof
  Induct >> simp[access_ok_def, abstract_reads]
QED

Triviality abstract_fetchable:
  ∀n s a. fetchable functional_storage n (abstract_state s) a =
          fetchable finite_storage n s a
Proof
  Induct >> simp[fetchable_def, abstract_reads]
QED

Triviality abstract_address_of:
  address_of functional_storage (abstract_state s) len a = address_of finite_storage s len a
Proof
  Cases_on `a` >> simp[address_of_def, abstract_reads] >>
  rpt CASE_TAC >> simp[abstract_reads]
QED

Triviality abstract_load:
  load functional_storage n a (abstract_state s) = load finite_storage n a s
Proof
  simp[load_def, abstract_access_ok, abstract_read_bytes]
QED

Triviality abstract_store:
  store functional_storage n a v (abstract_state s) =
    abstract_result (store finite_storage n a v s)
Proof
  rw[store_def, abstract_access_ok, abstract_write_bytes, abstract_result_def]
QED

Triviality abstract_load128:
  load128 functional_storage a (abstract_state s) = load128 finite_storage a s
Proof
  simp[load128_def, abstract_access_ok, abstract_read_bytes]
QED

Triviality abstract_store128:
  store128 functional_storage a v (abstract_state s) =
    abstract_result (store128 finite_storage a v s)
Proof
  rw[store128_def, abstract_access_ok, abstract_write_bytes, abstract_result_def]
QED

Triviality abstract_write_sized:
  write_sized functional_storage sz r v (abstract_state s) =
    abstract_state (write_sized finite_storage sz r v s)
Proof
  simp[write_sized_def, abstract_reads, abstract_updates]
QED

Triviality abstract_push:
  push functional_storage sz v (abstract_state s) =
    abstract_result (push finite_storage sz v s)
Proof
  PURE_REWRITE_TAC [push_def, LET_THM] >> BETA_TAC >>
  REWRITE_TAC [abstract_reads, abstract_store] >>
  Cases_on `store finite_storage (size_bytes sz) (read_reg finite_storage s 4w - n2w (size_bytes sz)) v s` >>
  simp[abstract_result_def, abstract_updates]
QED

Triviality abstract_enter_frames:
  ∀k fp s. enter_frames functional_storage sz k fp (abstract_state s) =
           abstract_result (enter_frames finite_storage sz k fp s)
Proof
  Induct >> simp[enter_frames_def, abstract_result_def, abstract_load, abstract_push] >>
  rpt gen_tac >> rpt CASE_TAC >> gvs[abstract_result_def]
QED

Triviality abstract_read_operand:
  read_operand functional_storage sz (abstract_state s) len d =
    read_operand finite_storage sz s len d
Proof
  Cases_on `d` >> simp[read_operand_def, abstract_reads, abstract_load, abstract_address_of]
QED

Triviality abstract_write_operand:
  write_operand functional_storage sz (abstract_state s) len d v =
    abstract_result (write_operand finite_storage sz s len d v)
Proof
  Cases_on `d` >>
  simp[write_operand_def, abstract_reads, abstract_updates, abstract_store,
       abstract_address_of, abstract_result_def, abstract_write_sized]
QED

Triviality abstract_next_rip:
  next_rip len (abstract_result r) = abstract_result (next_rip len r)
Proof
  Cases_on `r` >> simp[next_rip_def, abstract_result_def, abstract_reads, abstract_updates]
QED

Triviality abstract_read_aligned_xmm:
  read_aligned_xmm functional_storage (abstract_state s) len src =
    read_aligned_xmm finite_storage s len src
Proof
  Cases_on `src` >>
  simp[read_aligned_xmm_def, abstract_reads, abstract_address_of, abstract_load128]
QED

Triviality abstract_string_step:
  string_step functional_storage u op sz (abstract_state s) =
    abstract_result (string_step finite_storage u op sz s)
Proof
  Cases_on `op` >>
  simp[string_step_def, abstract_reads, abstract_load, abstract_store] >>
  rpt CASE_TAC >>
  gvs[abstract_result_def, abstract_updates, abstract_write_sized, abstract_reads]
QED

Triviality case_abstract_result:
  (case abstract_result r of Next t => g t | Fault e => Fault e) =
    (case r of Next t => g (abstract_state t) | Fault e => Fault e)
Proof
  Cases_on `r` >> simp[abstract_result_def]
QED

Triviality abstract_execute:
  execute_with functional_storage u i len (abstract_state s) =
    abstract_result (execute_with finite_storage u i len s)
Proof
  Cases_on `i` >>
  simp[execute_with_def, abstract_reads, abstract_access_ok, abstract_read_bytes,
       abstract_address_of, abstract_read_operand, abstract_load, abstract_load128,
       abstract_read_aligned_xmm, abstract_write_sized, abstract_push,
       abstract_enter_frames, abstract_string_step] >>
  rpt CASE_TAC >>
  gvs[abstract_result_def, abstract_updates, abstract_write_operand, abstract_store,
      abstract_store128, abstract_next_rip, abstract_reads, abstract_write_sized,
      abstract_push, abstract_enter_frames, abstract_string_step] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[abstract_updates, abstract_write_operand, abstract_next_rip, abstract_result_def,
     next_rip_def, abstract_reads, abstract_write_sized, abstract_push] >>
  gvs[case_abstract_result] >> rpt CASE_TAC >>
  gvs[abstract_result_def, abstract_write_operand, abstract_next_rip]
QED

Definition step_cv_def:
  step_cv u s = step_with finite_storage u s
End

Theorem step_cv_refines:
  step u (abstract_state s) = abstract_result (step_cv u s)
Proof
  simp[step_def, step_cv_def, step_with_def, abstract_reads, abstract_fetchable,
       abstract_read_bytes] >>
  qabbrev_tac `n = fetchable finite_storage 15 s s.rip` >>
  Cases_on `decode (read_bytes finite_storage n s s.rip)` >>
  rw[abstract_result_def, abstract_execute]
QED

(* Specialise the shared definitions to finite_storage before translation,
   removing the higher-order storage argument. *)
Definition cv_read_reg_def:
  cv_read_reg s r = read_reg finite_storage s r
End

Definition cv_write_reg_def:
  cv_write_reg r v s = write_reg finite_storage r v s
End

Definition cv_read_xmm_def:
  cv_read_xmm s x = read_xmm finite_storage s x
End

Definition cv_write_xmm_def:
  cv_write_xmm x v s = write_xmm finite_storage x v s
End

Definition cv_read_bytes_def:
  cv_read_bytes 0 (s:finite_state) (a:word64) = [] ∧
  cv_read_bytes (SUC n) s a = lookup_word 0w s.mem a :: cv_read_bytes n s (a + 1w)
End

Triviality cv_read_bytes_eq:
  ∀n s a. cv_read_bytes n s a = read_bytes finite_storage n s a
Proof
  Induct >> simp[cv_read_bytes_def, read_bytes_def, finite_storage_def]
QED

Definition cv_access_ok_def:
  (cv_access_ok k 0 (s:finite_state) (a:word64) ⇔ T) ∧
  (cv_access_ok k (SUC n) s a ⇔
    allowed k (lookup_word no_access s.perms a) ∧ cv_access_ok k n s (a + 1w))
End

Triviality cv_access_ok_eq:
  ∀n k s a. cv_access_ok k n s a ⇔ access_ok finite_storage k n s a
Proof
  Induct >> simp[cv_access_ok_def, access_ok_def, finite_storage_def]
QED

Definition cv_fetchable_def:
  cv_fetchable 0 (s:finite_state) (a:word64) = 0n ∧
  cv_fetchable (SUC n) s a =
    if allowed Execute (lookup_word no_access s.perms a) then SUC (cv_fetchable n s (a + 1w))
    else 0
End

Triviality cv_fetchable_eq:
  ∀n s a. cv_fetchable n s a = fetchable finite_storage n s a
Proof
  Induct >> simp[cv_fetchable_def, fetchable_def, finite_storage_def]
QED

Definition cv_write_bytes_def:
  cv_write_bytes [] (a:word64) (s:finite_state) = s ∧
  cv_write_bytes (b::bs) a s = cv_write_bytes bs (a + 1w) (s with mem := insert_word a b s.mem)
End

Triviality cv_write_bytes_eq:
  ∀bs a s. cv_write_bytes bs a s = write_bytes finite_storage bs a s
Proof
  Induct >> simp[cv_write_bytes_def, write_bytes_def, finite_storage_def]
QED

Definition cv_address_of_def:
  cv_address_of s len a = address_of finite_storage s len a
End

Definition cv_load_def:
  cv_load n a s = load finite_storage n a s
End

Definition cv_store_def:
  cv_store n a v s = store finite_storage n a v s
End

Definition cv_load128_def:
  cv_load128 a s = load128 finite_storage a s
End

Definition cv_store128_def:
  cv_store128 a v s = store128 finite_storage a v s
End

Definition cv_read_aligned_xmm_def:
  cv_read_aligned_xmm s len src = read_aligned_xmm finite_storage s len src
End

Definition cv_read_operand_def:
  cv_read_operand sz s len d = read_operand finite_storage sz s len d
End

Definition cv_write_operand_def:
  cv_write_operand sz s len d v = write_operand finite_storage sz s len d v
End

Definition cv_write_sized_def:
  cv_write_sized sz r v s = write_sized finite_storage sz r v s
End

Definition cv_push_def:
  cv_push sz v s = push finite_storage sz v s
End

Definition cv_enter_frames_def:
  cv_enter_frames sz 0 (fp:word64) (s:finite_state) = Next s ∧
  cv_enter_frames sz (SUC k) fp s =
    let fp' = fp - n2w (size_bytes sz) in
      case cv_load (size_bytes sz) fp' s of
        NONE => Fault Load
      | SOME v =>
          case cv_push sz v s of
            Next t => cv_enter_frames sz k fp' t
          | Fault f => Fault f
End

Triviality cv_enter_frames_eq:
  ∀k sz fp s. cv_enter_frames sz k fp s = enter_frames finite_storage sz k fp s
Proof
  Induct >> simp[cv_enter_frames_def, enter_frames_def, cv_load_def, cv_push_def]
QED

Definition cv_string_step_def:
  cv_string_step u op sz s = string_step finite_storage u op sz s
End

Definition cv_execute_def:
  cv_execute u i len s = execute_with finite_storage u i len s
End

val aliases = [cv_read_reg_def, cv_write_reg_def, cv_read_xmm_def, cv_write_xmm_def,
               cv_read_bytes_eq, cv_access_ok_eq, cv_fetchable_eq, cv_write_bytes_eq,
               cv_address_of_def, cv_load_def, cv_store_def, cv_load128_def,
               cv_store128_def, cv_read_aligned_xmm_def, cv_read_operand_def,
               cv_write_operand_def, cv_write_sized_def, cv_push_def, cv_enter_frames_eq,
               cv_string_step_def, cv_execute_def, step_cv_def];

Triviality finite_storage_apply:
  finite_storage.get_reg f r = lookup_word 0w f r ∧
  finite_storage.put_reg r v f = insert_word r v f ∧
  finite_storage.get_xmm x g = lookup_word 0w x g ∧
  finite_storage.put_xmm g w x = insert_word g w x ∧
  finite_storage.get_byte m a = lookup_word 0w m a ∧
  finite_storage.put_byte a b m = insert_word a b m ∧
  finite_storage.get_perm p a = lookup_word no_access p a
Proof
  simp[finite_storage_def]
QED

fun specialise_clause th =
  let
    val eq = SPEC_ALL th
    val arg = hd (snd (strip_comb (lhs (concl eq))))
    val storage = ``finite_storage``
    val theta = match_type (type_of arg) (type_of storage)
  in
    INST [inst theta arg |-> storage] (INST_TYPE theta eq)
    |> PURE_REWRITE_RULE (map (GSYM o SPEC_ALL) aliases)
    |> SIMP_RULE (srw_ss()) [finite_storage_apply]
    |> PURE_REWRITE_RULE (map (GSYM o SPEC_ALL) aliases)
  end;

fun translate th =
  cv_auto_trans (PURE_REWRITE_RULE [lookup_word_def, insert_word_def] th);

fun translate_specialised th =
  translate (LIST_CONJ (map specialise_clause (CONJUNCTS (SPEC_ALL th))));

val aes_sbox_pre_def = cv_auto_trans_pre "aes_sbox_pre" Sbox_def;
val aes_inv_sbox_pre_def = cv_auto_trans_pre "aes_inv_sbox_pre" InvSbox_def;

val byte_bound = SIMP_RULE (srw_ss()) [] (INST_TYPE [alpha |-> ``:8``] w2n_lt);

Theorem aes_sbox_pre[cv_pre]:
  aes_sbox_pre x
Proof
  simp[aes_sbox_pre_def, byte_bound]
QED

Theorem aes_inv_sbox_pre[cv_pre]:
  aes_inv_sbox_pre x
Proof
  simp[aes_inv_sbox_pre_def, byte_bound]
QED

(* Instantiate the upstream higher-order maps at their fixed round operations. *)
fun translate_aes_map def map_def =
  cv_auto_trans (SIMP_RULE std_ss [map_def] (AP_THM def
    (mk_var ("s", dom_rng (type_of (lhs (concl def))) |> #1))));

val () = app cv_auto_trans
  [to_state_def, from_state_def, ShiftRows_def, InvShiftRows_def,
   xmm_to_aes_def, aes_pack_column_def, aes_to_xmm_def];
val () = app (fn def => translate_aes_map def genSubBytes_def) [SubBytes_def, InvSubBytes_def];
val () = app (cv_auto_trans o REWRITE_RULE [mult_unroll]) [MultCol_def, InvMultCol_def];
val () = app (fn def => translate_aes_map def genMixColumns_def) [MixColumns_def, InvMixColumns_def];
val () = app cv_auto_trans [aes_round_result_def, aes_imc_result_def, sub_word_def,
                             aes_keygen_assist_def];

val () = cv_auto_trans decode_def;
val () = app cv_auto_trans [lane32_def, lanes32_def, lane64_def, lanes64_def, paddd_def,
                            paddq_def, bytes_eq_def, byte_signs_def, phaddd_def,
                            pcmpgtq_lane_def, mul32_def, pmul_even_def, sat16_def,
                            sat_pair_def, pack_dwords_def, lane16_def, lane8_def, words32_def,
                            madd_pair_def, pmaddwd_def, maddubs_word_def, pmaddubsw_def,
                            sat8_def, sat_quad_def, pack_words_def, byte_lane_def,
                            byte_quad_def, byte_lanes_def, avg16_def, pavgw_def,
                            arithmeticTheory.ABS_DIFF_def, sad8_def, psadbw_def,
                            minpos_aux_def, phminposuw_def, pbinop_result_def,
                            insert_lane32_def, pshufd_def, word16_at_def, pshufw_def,
                            pshufb_def, pshift_def, psrad_def,
                            ptest_flags_def, crc32c_bit_def, crc32c_bits_def, pshiftdq_def,
                            clmul_def, pclmul_def, palignr_def, pdep_aux_def, pext_aux_def,
                            pblendvb_def, pcmpd_lane_def, pcmpd_def, pwiden_byte_def,
                            pwiden_pair_def, pwiden_def];
val () = app translate [cv_read_bytes_def, cv_access_ok_def, cv_fetchable_def,
                        cv_write_bytes_def];
val () = app translate_specialised
  [read_reg_def, write_reg_def, read_xmm_def, write_xmm_def, address_of_def, load_def,
   store_def, load128_def, store128_def, read_aligned_xmm_def, write_sized_def, read_operand_def,
   write_operand_def, push_def];
val () = translate cv_enter_frames_def;
val () = app translate_specialised [string_step_def, execute_with_def, step_with_def];
