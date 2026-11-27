(* Checks the model against the execution cases observed on x86-64 hardware
   (x86ExecCases): for each case, cv_eval runs step_cv from the case's state
   to the int3 the hardware stopped at, and compares registers, XMM registers
   and flags, or
   the fault raised, and the data window and watched stack bytes where it
   stopped (before the faulting step on a fault). The undefined-flag argument
   is set to the observed flags, so each check shows the observation is an
   outcome the model allows. *)
Theory x86ExecTest
Ancestors x86IsaCv x86ExecCases
Libs cv_transLib wordsLib

Definition flags_of_word_def:
  flags_of_word (w:word64) =
    <| CF := word_bit 0 w; PF := word_bit 2 w; AF := word_bit 4 w;
       ZF := word_bit 6 w; SF := word_bit 7 w; OF := word_bit 11 w |>
End

Definition word_of_flags_def:
  word_of_flags f : word64 =
    (if f.CF then 0x1w else 0w) || (if f.PF then 0x4w else 0w) ||
    (if f.AF then 0x10w else 0w) || (if f.ZF then 0x40w else 0w) ||
    (if f.SF then 0x80w else 0w) || (if f.OF then 0x800w else 0w)
End

Definition put_many_def:
  put_many (address:num) [] tree = tree ∧
  put_many address (value::values) tree =
    put_many (address + 1) values (insert address value tree)
End

Definition fill_def:
  fill (address:num) 0 value tree = tree ∧
  fill address (SUC n) value tree = fill (address + 1) n value (insert address value tree)
End

Definition read_regs_def:
  read_regs 0 (r:num) tree = [] ∧
  read_regs (SUC n) r tree =
    (case lookup r tree of NONE => 0w:word64 | SOME v => v) :: read_regs n (r + 1) tree
End

Definition read_xmms_def:
  read_xmms 0 (r:num) tree = [] ∧
  read_xmms (SUC n) r tree =
    (case lookup r tree of NONE => 0w:word128 | SOME v => v) :: read_xmms n (r + 1) tree
End

Definition read_mem_def:
  read_mem (address:num) 0 tree = [] ∧
  read_mem address (SUC n) tree =
    (case lookup address tree of NONE => 0w:word8 | SOME v => v) ::
      read_mem (address + 1) n tree
End

(* The pages generate_exec.py maps: code at 0x100000 (R-X, int3s with the
   case's bytes at 0x100100), data at 0x200000 and stack at 0x300000 with
   the case's permissions, and the return address at the stack top 0x300FF8. *)
Definition test_mem_def:
  test_mem code data ret =
    put_many 0x300FF8 (le_bytes 8 ret)
      (put_many 0x200000 data (put_many 0x100100 code (fill 0x100000 4096 0xCCw LN)))
End

Definition test_perms_def:
  test_perms data_perm stack_perm =
    fill 0x300000 4096 stack_perm
      (fill 0x200000 4096 data_perm (fill 0x100000 4096 (perm T F T) LN))
End

Definition test_state_def:
  test_state code ((entry, regs, xmm, flags, data, ret, data_perm, stack_perm) : exec_input) =
    x86_machine (put_many 0 regs LN) (put_many 0 xmm LN) entry (flags_of_word flags) F
      (test_mem code data ret) (test_perms data_perm stack_perm) : finite_state
End

(* The fault that stopped the run, if any, and the last state reached:
   at stop, or before the faulting step. *)
Definition run_to_def:
  run_to stop fuel u (s:finite_state) =
    if s.rip = stop then (NONE, s)
    else case fuel of
           0 => (SOME Unsupported, s)
         | SUC n => case step_cv u s of
                      Next t => run_to stop n u t
                    | Fault k => (SOME k, s)
End

(* Enough steps for the longest case, chacha20_block with its 80 calls of
   qr (2,580 instructions). *)
Definition fuel_def:
  fuel = 3000n
End

(* The data window at 0x200000 and the bytes below the stack page's end
   0x301000. *)
Definition windows_agree_def:
  windows_agree data stack (t:finite_state) ⇔
    read_mem 0x200000 (LENGTH data) t.mem = data ∧
    read_mem (0x301000 - LENGTH stack) (LENGTH stack) t.mem = stack
End

Definition agrees_def:
  agrees ((code, input, outcome, data, stack) : exec_case) ⇔
    case outcome of
      Reached rip regs xmm flags mask =>
        (case run_to rip fuel (flags_of_word flags) (test_state code input) of
           (NONE, t) => read_regs 16 0 t.regs = regs ∧ read_xmms 16 0 t.xmm = xmm ∧
                        word_of_flags t.flags && mask = flags ∧
                        windows_agree data stack t
         | (SOME _, _) => F)
    | Faulted k =>
        (case run_to 0w fuel (flags_of_word 0w) (test_state code input) of
           (SOME k', t) => k' = k ∧ windows_agree data stack t
         | (NONE, _) => F)
End

val () = cv_auto_trans agrees_def;

fun check i =
  let
    val name = "exec_case_" ^ Int.toString i
    val def = DB.fetch "x86ExecCases" (name ^ "_def")
    val result = cv_eval (mk_comb (``agrees``, rhs (concl def)))
  in
    if aconv (rhs (concl result)) T then
      ignore (save_thm (name ^ "_agrees", EQT_ELIM (PURE_REWRITE_RULE [GSYM def] result)))
    else raise Fail (name ^ ": the model disagrees with the observed outcome")
  end;

val count = numSyntax.int_of_term (rhs (concl exec_case_count_def));
val () = List.app check (List.tabulate (count, I));

(* Fail-closed cases hardware can't show with the harness's fixed pages. *)
Definition place_def:
  place address bytes (s:finite_state) = s with mem := put_many address bytes s.mem
End

Definition set_perm_def:
  set_perm address p (s:finite_state) = s with perms := insert address p s.perms
End

Definition set_rip_def:
  set_rip address (s:finite_state) = s with rip := address
End

val () = cv_auto_trans place_def;
val () = cv_auto_trans set_rip_def;
val () = cv_auto_trans set_perm_def;

val start = ``test_state [] (0x100100w, REPLICATE 16 0w, REPLICATE 16 0w, 0w, [], 0w,
                             perm T T F, perm T T F)``;

fun check_fault name state reason =
  let
    val result = cv_eval ``step_cv (flags_of_word 0w) ^state``
    val expected = ``Fault ^reason : finite_state x86_result``
  in
    if aconv (rhs (concl result)) expected then ignore (save_thm (name, result))
    else raise Fail (name ^ ": expected " ^ term_to_string expected)
  end;

(* xor eax, eax with its second byte writable *)
val () = check_fault "fetch_rejects_writable_code"
  ``set_perm 0x100101 (perm T T T)
      (place 0x100100 [0x31w; 0xC0w] ^start)`` ``Fetch``;
(* xor eax, eax straddling the end of the code page *)
val () = check_fault "fetch_rejects_instruction_past_code"
  ``set_rip 0x100FFFw (place 0x100FFF [0x31w; 0xC0w] ^start)`` ``Fetch``;
(* 31 then 00, a xor to memory if the second byte were fetched *)
val () = check_fault "fetch_rejects_undecodable_instruction_past_code"
  ``set_rip 0x100FFFw (place 0x100FFF [0x31w; 0x00w] ^start)`` ``Fetch``;
(* ud2 *)
val () = check_fault "unmodelled_opcode_is_unsupported"
  ``place 0x100100 [0x0Fw; 0x0Bw] ^start`` ``Unsupported``;
(* 15 operand-size prefixes: no instruction within the 15-byte limit *)
val () = check_fault "prefixes_past_length_limit_are_unsupported"
  ``place 0x100100 (REPLICATE 15 0x66w) ^start`` ``Unsupported``;
(* ud2 in the last two bytes of the code page: no further byte is needed *)
val () = check_fault "unmodelled_opcode_at_end_of_code_is_unsupported"
  ``set_rip 0x100FFEw (place 0x100FFE [0x0Fw; 0x0Bw] ^start)`` ``Unsupported``;
(* nops RIP-relative and without base cut short by the end of the code
   page: their displacements lie past it, so the step faults on the fetch *)
val () = check_fault "nop_rip_relative_at_end_of_code_is_truncated"
  ``set_rip 0x100FFDw (place 0x100FFD [0x0Fw; 0x1Fw; 0x05w] ^start)`` ``Fetch``;
val () = check_fault "nop_without_base_at_end_of_code_is_truncated"
  ``set_rip 0x100FFCw (place 0x100FFC [0x0Fw; 0x1Fw; 0x04w; 0x25w] ^start)`` ``Fetch``;
(* 66, a REX byte and 0F at the end of the code page: the next byte decides
   between an SSE2 form (66 44 0F EF C1, pxor) and a rejected one, so the
   step faults on the fetch. *)
val () = check_fault "sse_prefix_rex_0f_at_end_of_code_is_truncated"
  ``set_rip 0x100FFDw (place 0x100FFD [0x66w; 0x44w; 0x0Fw] ^start)`` ``Fetch``;
(* The same with REX.W: the next byte decides between movq r64, xmm
   (66 48 0F 7E) and a rejected form. *)
val () = check_fault "sse_prefix_rex_w_0f_at_end_of_code_is_truncated"
  ``set_rip 0x100FFDw (place 0x100FFD [0x66w; 0x48w; 0x0Fw] ^start)`` ``Fetch``;
(* F3 REX.W 0F: the next byte decides between a bit count (F3 48 0F BC,
   tzcnt) and a rejected form, so the step faults on the fetch. *)
val () = check_fault "f3_rex_w_0f_at_end_of_code_is_truncated"
  ``set_rip 0x100FFDw (place 0x100FFD [0xF3w; 0x48w; 0x0Fw] ^start)`` ``Fetch``;
(* F3 with another legacy prefix, and REX.W 81, at the end of the code
   page: an opcode can still complete them (66 F3 0F BC, tzcnt; REX.W 81
   /r id), so the step faults on the fetch. *)
val () = check_fault "f3_66_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0xF3w; 0x66w] ^start)`` ``Fetch``;
val () = check_fault "two_e_f3_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0x2Ew; 0xF3w] ^start)`` ``Fetch``;
val () = check_fault "rex_w_81_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0x48w; 0x81w] ^start)`` ``Fetch``;
(* Prefixes an opcode can still complete: the step faults on the fetch. *)
val () = check_fault "f3_at_end_of_code_is_truncated"
  ``set_rip 0x100FFFw (place 0x100FFF [0xF3w] ^start)`` ``Fetch``;
val () = check_fault "f3_rex_w_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0xF3w; 0x48w] ^start)`` ``Fetch``;
val () = check_fault "sse_prefix_rex_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0x66w; 0x44w] ^start)`` ``Fetch``;
val () = check_fault "sse_prefix_rex_w_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0x66w; 0x48w] ^start)`` ``Fetch``;
val () = check_fault "nop_prefixes_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0x66w; 0x2Ew] ^start)`` ``Fetch``;
val () = check_fault "nop_group_digit_1_at_end_of_code_is_truncated"
  ``set_rip 0x100FFDw (place 0x100FFD [0x0Fw; 0x1Fw; 0x48w] ^start)`` ``Fetch``;
(* xor r/m32, r32; shl r/m32, cl; and r/m32, imm8; and mov m8, ah, each
   with a RIP-relative ModRM byte at the end of the code page: the
   displacement lies past it, so the step faults on the fetch *)
val () = check_fault "xor_to_memory_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0x31w; 0x05w] ^start)`` ``Fetch``;
val () = check_fault "shift_of_memory_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0xD3w; 0x25w] ^start)`` ``Fetch``;
val () = check_fault "and_imm_to_memory_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0x83w; 0x25w] ^start)`` ``Fetch``;
val () = check_fault "byte_store_from_ah_at_end_of_code_is_truncated"
  ``set_rip 0x100FFEw (place 0x100FFE [0x88w; 0x25w] ^start)`` ``Fetch``;
(* F2 and F3 together, which no opcode completes, at the end of the code
   page: rejected from the bytes there, not fetched further *)
val () = check_fault "f2_f3_at_end_of_code_is_unsupported"
  ``set_rip 0x100FFEw (place 0x100FFE [0xF2w; 0xF3w] ^start)`` ``Unsupported``;
(* mov %eax, 0xffefa(%rip), a store to 0x200000, with that byte readable,
   writable and executable: the model denies stores to executable memory. *)
val () = check_fault "store_rejects_executable_memory"
  ``set_perm 0x200000 (perm T T T)
      (place 0x100100 [0x89w; 0x05w; 0xFAw; 0xFEw; 0x0Fw; 0x00w] ^start)`` ``Store``;
(* The same store with that byte writable but neither readable nor
   executable: the model allows stores only to readable bytes. *)
val () = check_fault "store_rejects_unreadable_memory"
  ``set_perm 0x200000 (perm F T F)
      (place 0x100100 [0x89w; 0x05w; 0xFAw; 0xFEw; 0x0Fw; 0x00w] ^start)`` ``Store``;
(* movups %xmm0, 0xffef9(%rip), a 16-byte store to 0x200000, with only its
   last byte 0x20000F executable as well: the whole store is denied. *)
val () = check_fault "store128_rejects_executable_last_byte"
  ``set_perm 0x20000F (perm T T T)
      (place 0x100100 [0x0Fw; 0x11w; 0x05w; 0xF9w; 0xFEw; 0x0Fw; 0x00w] ^start)`` ``Store``;
