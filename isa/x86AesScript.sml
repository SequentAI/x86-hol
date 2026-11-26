(* Legacy AES-NI operates on the FIPS 197 block whose first byte is the
   least significant byte of the XMM register. RoundOp provides the FIPS
   operations, including GF(2^8) multiplication modulo 0x11B. *)
Theory x86Aes
Ancestors RoundOp words

Datatype:
  aes_round = AESENC | AESENCLAST | AESDEC | AESDECLAST
End

Definition xmm_to_aes_def:
  xmm_to_aes (x:word128) =
    to_state ((7 >< 0) x, (15 >< 8) x, (23 >< 16) x, (31 >< 24) x,
              (39 >< 32) x, (47 >< 40) x, (55 >< 48) x, (63 >< 56) x,
              (71 >< 64) x, (79 >< 72) x, (87 >< 80) x, (95 >< 88) x,
              (103 >< 96) x, (111 >< 104) x, (119 >< 112) x, (127 >< 120) x)
End

Definition aes_pack_column_def:
  aes_pack_column (a:word8) (b:word8) (c:word8) (d:word8) : word32 =
    d @@ ((c @@ ((b @@ a) : word16)) : word24)
End

Definition aes_to_xmm_def:
  aes_to_xmm state : word128 =
    let (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15) =
      from_state state in
    let c0 = aes_pack_column b0 b1 b2 b3;
        c1 = aes_pack_column b4 b5 b6 b7;
        c2 = aes_pack_column b8 b9 b10 b11;
        c3 = aes_pack_column b12 b13 b14 b15 in
      ((c3 @@ c2) : word64) @@ ((c1 @@ c0) : word64)
End

Definition aes_round_result_def:
  aes_round_result AESENC x k =
    aes_to_xmm (MixColumns (ShiftRows (SubBytes (xmm_to_aes x)))) ?? k ∧
  aes_round_result AESENCLAST x k =
    aes_to_xmm (ShiftRows (SubBytes (xmm_to_aes x))) ?? k ∧
  aes_round_result AESDEC x k =
    aes_to_xmm (InvMixColumns (InvSubBytes (InvShiftRows (xmm_to_aes x)))) ?? k ∧
  aes_round_result AESDECLAST x k =
    aes_to_xmm (InvSubBytes (InvShiftRows (xmm_to_aes x))) ?? k
End

Definition aes_imc_result_def:
  aes_imc_result x = aes_to_xmm (InvMixColumns (xmm_to_aes x))
End

(* FIPS 197 SubWord: the S-box on each byte of w. *)
Definition sub_word_def:
  sub_word (w:word32) =
    aes_pack_column (Sbox ((7 >< 0) w)) (Sbox ((15 >< 8) w))
                    (Sbox ((23 >< 16) w)) (Sbox ((31 >< 24) w))
End

(* AESKEYGENASSIST: SubWord of dwords 1 and 3 of x, each followed by its
   RotWord XOR the round constant imm. RotWord moves the first (least
   significant) byte last, a rotate right by 8. *)
Definition aes_keygen_assist_def:
  aes_keygen_assist (x:word128) (imm:word8) : word128 =
    let x1 = sub_word ((63 >< 32) x);
        x3 = sub_word ((127 >< 96) x);
        rcon = w2w imm : word32 in
      ((((x3 #>> 8) ?? rcon) @@ x3) : word64) @@ ((((x1 #>> 8) ?? rcon) @@ x1) : word64)
End
