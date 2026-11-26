(* Checks the decoder against llvm-objdump (x86DecodeCases): on every
   vector it returns the instruction and length llvm-objdump reads, and it
   rejects every encoding outside the modelled slice. *)
Theory x86DecodeTest
Ancestors x86IsaCv x86DecodeCases
Libs cv_transLib wordsLib

Definition decode_agrees_def:
  (decode_agrees [] ⇔ T) ∧
  (decode_agrees ((bytes, expected)::rest) ⇔
     decode bytes = expected ∧ decode_agrees rest)
End

(* Each vector is decoded by cv_eval and compared by EVAL on its own, so a
   mismatch names its vector. *)
fun agrees entry =
  let
    val (bytes, expected) = pairSyntax.dest_pair entry
    val decoded = cv_eval ``decode ^bytes``
    val comparison = EVAL ``^(rhs (concl decoded)) = ^expected``
  in
    if aconv (rhs (concl comparison)) T then TRANS decoded (EQT_ELIM comparison)
    else raise Fail ("decode " ^ term_to_string bytes ^ " = " ^
                     term_to_string (rhs (concl decoded)) ^ ", expected " ^
                     term_to_string expected)
  end;

val agreements = map agrees (fst (listSyntax.dest_list (rhs (concl decode_cases_def))));

Theorem decode_cases_agree:
  decode_agrees decode_cases
Proof
  REWRITE_TAC (decode_agrees_def :: decode_cases_def :: agreements)
QED
