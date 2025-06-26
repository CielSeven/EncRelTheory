Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem CommonAssertion ListLib.
From compcert.lib Require Import Integers.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type StoreLibSig (CRules: SeparationLogicSig) (DePredSig : DerivedPredSig CRules).

Import CRules.
Import DePredSig.
Local Open Scope sac.  

Theorem store_byte_eqm:
  forall p v v',
    Byte.eqm v v' ->
    store_byte p v |-- store_byte p v'.
Proof.
  unfold store_byte; intros.
  apply mstore_eqm; auto.
Qed.

Lemma store_int_store_char: forall p v,
  store_int p v --||--
  EX v1 v2 v3 v4: Z,
    [| merge_int v1 v2 v3 v4 v |] &&
    [| Int.min_signed <= v <= Int.max_signed |] &&
    [| aligned_4 p|] &&
    store_char p v1 **
    store_char (p + 1) v2 **
    store_char (p + 2) v3 **
    store_char (p + 3) v4.
Proof.
  intros.
  split.
  + unfold store_int, store_4byte.
    Intros z1 z2 z3 z4.
    Exists (Byte.signed (Byte.repr z1))
           (Byte.signed (Byte.repr z2))
           (Byte.signed (Byte.repr z3))
           (Byte.signed (Byte.repr z4)).
    unfold store_char.
    pose proof Byte.signed_range (Byte.repr z1).
    pose proof Byte.signed_range (Byte.repr z2).
    pose proof Byte.signed_range (Byte.repr z3).
    pose proof Byte.signed_range (Byte.repr z4).
    entailer!.
    - apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply store_byte_eqm, Byte.eqm_signed_repr.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_int in H. apply H.
    - unfold merge_int.
      pose proof Byte.eqm_mod_eq _ _ (Byte.eqm_signed_repr z1).
      pose proof Byte.eqm_mod_eq _ _ (Byte.eqm_signed_repr z2).
      pose proof Byte.eqm_mod_eq _ _ (Byte.eqm_signed_repr z3).
      pose proof Byte.eqm_mod_eq _ _ (Byte.eqm_signed_repr z4).
      change Byte.modulus with (2^8) in *.
      rewrite <- H5, <- H6, <- H7, <- H8.
      apply H0.
  + Intros v1 v2 v3 v4.
    unfold store_int, store_char.
    unfold store_4byte.
    Intros.
    Exists v1 v2 v3 v4.
    entailer!.
    unfold isvalidptr_int.
    unfold isvalidptr_char in *.
    repeat split ; try lia ; auto.
Qed.

Lemma undef_store_uint_undef_store_char : forall p,
  undef_store_uint p --||-- [| aligned_4 p |]  && undef_store_char p ** undef_store_char (p + 1) ** undef_store_char (p + 2) ** undef_store_char (p + 3).
Proof.
  intros.
  unfold undef_store_uint, undef_store_char. 
  unfold isvalidptr_int. unfold isvalidptr_char.
  split ; Intros ; entailer!.
Qed.

Lemma undef_store_int_undef_store_char : forall p,
  undef_store_int p --||-- [| aligned_4 p |]  && undef_store_char p ** undef_store_char (p + 1) ** undef_store_char (p + 2) ** undef_store_char (p + 3).
Proof.
  intros.
  unfold undef_store_int, undef_store_char. 
  unfold isvalidptr_int. unfold isvalidptr_char.
  split ; Intros ; entailer!.
Qed.

Lemma store_uint_store_char: forall p v,
  store_uint p v --||--
  EX v1 v2 v3 v4: Z,
    [| merge_int v1 v2 v3 v4 v |] &&
    [| 0 <= v <= Int.max_unsigned |] &&
    [| aligned_4 p|] &&
    store_char p v1 **
    store_char (p + 1) v2 **
    store_char (p + 2) v3 **
    store_char (p + 3) v4.
Proof.
  intros.
  split.
  + unfold store_uint, store_4byte.
    Intros z1 z2 z3 z4.
    Exists (Byte.signed (Byte.repr z1))
           (Byte.signed (Byte.repr z2))
           (Byte.signed (Byte.repr z3))
           (Byte.signed (Byte.repr z4)).
    unfold store_char.
    pose proof Byte.signed_range (Byte.repr z1).
    pose proof Byte.signed_range (Byte.repr z2).
    pose proof Byte.signed_range (Byte.repr z3).
    pose proof Byte.signed_range (Byte.repr z4).
    entailer!.
    - apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply derivable1_sepcon_mono.
      1: apply store_byte_eqm, Byte.eqm_signed_repr.
      apply store_byte_eqm, Byte.eqm_signed_repr.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    - apply H.
    - unfold merge_int.
      pose proof Byte.eqm_mod_eq _ _ (Byte.eqm_signed_repr z1).
      pose proof Byte.eqm_mod_eq _ _ (Byte.eqm_signed_repr z2).
      pose proof Byte.eqm_mod_eq _ _ (Byte.eqm_signed_repr z3).
      pose proof Byte.eqm_mod_eq _ _ (Byte.eqm_signed_repr z4).
      change Byte.modulus with (2^8) in *.
      rewrite <- H5, <- H6, <- H7, <- H8.
      apply H0.
  + Intros v1 v2 v3 v4.
    unfold store_uint, store_char.
    unfold store_4byte.
    Intros.
    Exists v1 v2 v3 v4.
    entailer!.
    unfold isvalidptr_int.
    unfold isvalidptr_char in *.
    repeat split ; try lia ; auto.
Qed.

Lemma store_byte_store_byte_noinit: forall p v,
  store_byte p v |-- store_byte_noninit p.
Proof.
  unfold store_byte, store_byte_noninit.
  intros.
  unfold derivable1.
  apply mstore_mstore_noninit.
Qed.

Lemma store_2byte_store_2byte_noinit: forall p v,
  store_2byte p v |-- store_2byte_noninit p.
Proof.
  unfold store_2byte, store_2byte_noninit.
  intros.
  Intros z1 z2.
  apply derivable1_sepcon_mono; apply store_byte_store_byte_noinit.
Qed.

Lemma store_4byte_store_4byte_noinit: forall p v,
  store_4byte p v |-- store_4byte_noninit p.
Proof.
  unfold store_4byte, store_4byte_noninit.
  intros.
  Intros z1 z2 z3 z4.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono; apply store_byte_store_byte_noinit.
Qed.

Lemma store_8byte_store_8byte_noinit: forall p v,
  store_8byte p v |-- store_8byte_noninit p.
Proof.
  unfold store_8byte, store_8byte_noninit.
  intros.
  Intros z1 z2 z3 z4.
  Intros z5 z6 z7 z8.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono.
  1: apply store_byte_store_byte_noinit.
  apply derivable1_sepcon_mono; apply store_byte_store_byte_noinit.
Qed.

Lemma store_ptr_undef_store_ptr: forall p v,
  store_ptr p v |-- undef_store_ptr p.
Proof.
  unfold store_ptr, undef_store_ptr.
  intros.
  entailer!.
  apply store_4byte_store_4byte_noinit.
Qed.

Lemma store_int_range : forall x v,
  (x # Int |-> v) |-- [| Int.min_signed <= v <= Int.max_signed |].
Proof.
  intros.
  unfold store_int.
  entailer!.
Qed.

Lemma store_int_undef_store_int: forall x v, 
  (x # Int |->v) |-- (x # Int |->_).
Proof.
  intros.
  unfold store_int, undef_store_int.
  entailer!.
  apply store_4byte_store_4byte_noinit.
Qed.

Lemma store_char_range : forall x v,
  (x # Char |-> v) |-- [| Byte.min_signed <= v <= Byte.max_signed |].
Proof.
  intros.
  unfold store_char.
  entailer!.
Qed.

Lemma store_char_undef_store_char: forall x v, 
  (x # Char |->v) |-- (x # Char |->_).
Proof.
  intros.
  unfold store_char, undef_store_char.
  entailer!.
  apply store_byte_store_byte_noinit.
Qed.

Lemma store_short_range : forall x v,
  (x # Short |-> v) |-- [| -32768 <= v <= 32767 |].
Proof. 
  intros.
  unfold store_short.
  entailer!.
Qed.

Lemma store_short_undef_store_short: forall x v, 
  (x # Short |->v) |-- (x # Short |->_).
Proof.
  intros.
  unfold store_short, undef_store_short.
  entailer!.
  apply store_2byte_store_2byte_noinit.
Qed.

Lemma store_int64_range : forall x v,
  (x # Int64 |-> v) |-- [| Int64.min_signed <= v <= Int64.max_signed |].
Proof.
  intros.
  unfold store_int64.
  entailer!.
Qed.

Lemma store_int64_undef_store_int64: forall x v, 
  (x # Int64 |->v) |-- (x # Int64 |->_).
Proof.
  intros.
  unfold store_int64, undef_store_int64.
  entailer!.
  apply store_8byte_store_8byte_noinit.
Qed.

Lemma store_uint_range : forall x v,
  (x # UInt |-> v) |-- [| 0 <= v <= Int.max_unsigned |].
Proof.
  intros.
  unfold store_uint.
  entailer!.
Qed.  

Lemma store_uint_undef_store_uint: forall x v, 
  (x # UInt |->v) |-- (x # UInt |->_).
Proof.
  intros.
  unfold store_uint, undef_store_uint.
  entailer!.
  apply store_4byte_store_4byte_noinit.
Qed.

Lemma store_uchar_range : forall x v,
  (x # UChar |-> v) |-- [| 0 <= v <= Byte.max_unsigned |].
Proof.
  intros.
  unfold store_uchar.
  entailer!.
Qed.

Lemma store_uchar_undef_store_uchar: forall x v, 
  (x # UChar |->v) |-- (x # UChar |->_).
Proof.
  intros.
  unfold store_uchar, undef_store_uchar.
  entailer!.
  apply store_byte_store_byte_noinit.
Qed.

Lemma store_ushort_range : forall x v,
  (x # UShort |-> v) |-- [| 0 <= v <= 65535 |].
Proof.
  intros.
  unfold store_ushort.
  entailer!.
Qed.

Lemma store_ushort_undef_store_ushort: forall x v, 
  (x # UShort |->v) |-- (x # UShort |->_).
Proof.
  intros.
  unfold store_ushort, undef_store_ushort.
  entailer!.
  apply store_2byte_store_2byte_noinit.
Qed.

Lemma store_uint64_range : forall x v,
  (x # UInt64 |-> v) |-- [| 0 <= v <= Int64.max_unsigned |].
Proof.
  intros.
  unfold store_uint64.
  entailer!.
Qed.  

Lemma store_uint64_undef_store_uint64: forall x v, 
  (x # UInt64 |->v) |-- (x # UInt64 |->_).
Proof.
  intros.
  unfold store_uint64, undef_store_uint64.
  entailer!.
  apply store_8byte_store_8byte_noinit.
Qed.

Lemma poly_store_poly_undef_store: forall x ty v,
  poly_store ty x v |-- poly_undef_store ty x.
Proof.
  intros.
  destruct ty; simpl.
  + unfold Invalid_store; entailer!.
  + unfold Invalid_store; entailer!.
  + unfold Invalid_store; entailer!.
  + unfold Invalid_store; entailer!.
  + apply store_int_undef_store_int.
  + apply store_char_undef_store_char.
  + apply store_int64_undef_store_int64.
  + apply store_short_undef_store_short.
  + apply store_uint_undef_store_uint.
  + apply store_uchar_undef_store_uchar.
  + apply store_uint64_undef_store_uint64.
  + apply store_ushort_undef_store_ushort.
  + apply store_ptr_undef_store_ptr.
Qed.

Lemma dup_mstore: forall x v1 v2,
  mstore x v1 ** mstore x v2 |-- [| False |].
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_mstore_noninit x).
  apply derivable1_sepcon_mono;
  unfold derivable1;
  apply (mstore_mstore_noninit).
Qed.

Lemma dup_store_byte_noninit: forall x, 
  store_byte_noninit x ** store_byte_noninit x |-- [| False |].
Proof.
  intros.
  unfold store_byte_noninit.
  apply dup_mstore_noninit.
Qed.

Lemma dup_store_byte: forall x v1 v2,
  store_byte x v1 ** store_byte x v2 |-- [| False |].
Proof.
  intros.
  unfold store_byte.
  apply dup_mstore.
Qed.

Lemma dup_store_2bytes_noninit: forall x,
  store_2byte_noninit x ** store_2byte_noninit x |-- [| False |].
Proof.
  intros.
  unfold store_2byte_noninit.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ ([|False|] ** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  eapply derivable1_trans. apply derivable1_sepcon_comm.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ ([|False|] ** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  apply dup_store_byte_noninit.
Qed.

Lemma dup_store_2bytes: forall x v1 v2,
  store_2byte x v1 ** store_2byte x v2 |-- [| False |].
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_store_2bytes_noninit x).
  apply derivable1_sepcon_mono;
  apply store_2byte_store_2byte_noinit.
Qed.

Lemma dup_store_4bytes_noninit: forall x,
  store_4byte_noninit x ** store_4byte_noninit x |-- [| False |].
Proof.
  intros.
  unfold store_4byte_noninit.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ ([|False|] ** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  eapply derivable1_trans. apply derivable1_sepcon_comm.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ ([|False|] ** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  apply dup_store_byte_noninit.
Qed.

Lemma dup_store_4bytes: forall x v1 v2,
  store_4byte x v1 ** store_4byte x v2 |-- [| False |].
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_store_4bytes_noninit x).
  apply derivable1_sepcon_mono;
  apply store_4byte_store_4byte_noinit.
Qed.

Lemma dup_store_8bytes_noninit: forall x,
  store_8byte_noninit x ** store_8byte_noninit x |-- [| False |].
Proof.
  intros.
  unfold store_8byte_noninit.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ ([|False|] ** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  eapply derivable1_trans. apply derivable1_sepcon_comm.
  eapply derivable1_trans. apply derivable1_sepcon_assoc1.
  apply (derivable1_trans _ ([|False|] ** TT)). 2: entailer!.
  apply derivable1_sepcon_mono. 2: entailer!.
  apply dup_store_byte_noninit.
Qed.

Lemma dup_store_8bytes: forall x v1 v2,
  store_8byte x v1 ** store_8byte x v2 |-- [| False |].
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_store_8bytes_noninit x).
  apply derivable1_sepcon_mono;
  apply store_8byte_store_8byte_noinit.
Qed.

Lemma dup_undef_store_int: forall x,
  (x # Int |->_) ** (x # Int |->_) |-- [| False |].
Proof.
  intros.
  unfold undef_store_int.
  eapply derivable1_trans.
  2: apply (dup_store_4bytes_noninit x).
  apply derivable1_sepcon_mono; entailer!.
Qed.

Lemma dup_store_int: forall x v1 v2,
  (x # Int |-> v1) ** (x # Int |-> v2) |-- [| False |].
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_undef_store_int x).
  apply derivable1_sepcon_mono; apply store_int_undef_store_int.
Qed.

Lemma dup_undef_store_ptr: forall x,
  (x # Ptr |->_) ** (x # Ptr |->_) |-- [| False |].
Proof.
  intros.
  unfold undef_store_ptr.
  eapply derivable1_trans.
  2: apply (dup_store_4bytes_noninit x).
  apply derivable1_sepcon_mono; entailer!.
Qed.

Lemma dup_store_ptr: forall x v1 v2,
  (x # Ptr |-> v1) ** (x # Ptr |-> v2) |-- [| False |].
Proof.
  intros.
  eapply derivable1_trans.
  2: apply (dup_undef_store_ptr x).
  apply derivable1_sepcon_mono; apply store_ptr_undef_store_ptr.
Qed.

Lemma store_byte_cast : forall x v , store_byte x v |-- store_byte x (signed_last_nbits v 8).
Proof.
  intros. 
  apply store_byte_eqm.
  apply UByte_cast_correct.
Qed.

Lemma store_byte_cast' : forall x v , store_byte x v |-- store_byte x (unsigned_last_nbits v 8).
Proof.
  intros. 
  apply store_byte_eqm.
  apply Byte_cast_correct.
Qed.

Lemma store_char_cast : forall x v , x # Char |-> v |-- x # UChar |-> unsigned_last_nbits v 8.
Proof.
  intros.
  unfold store_char, store_uchar.
  entailer!.
  - sep_apply store_byte_cast'. entailer!.
  - pose proof (unsigned_Lastnbits_range v 8). lia.
  - pose proof (unsigned_Lastnbits_range v 8).  
    replace Byte.max_unsigned with (2 ^ 8 - 1) by reflexivity.
    lia.
Qed.

Lemma store_uchar_cast : forall x v , x # UChar |-> v |-- x # Char |-> signed_last_nbits v 8.
Proof.
  intros.
  unfold store_char, store_uchar.
  entailer!.
  - sep_apply store_byte_cast. entailer!.
  - pose proof (signed_Lastnbits_range v 8).
    replace Byte.max_signed with (2 ^ 7 - 1) by reflexivity. lia.  
  - pose proof (signed_Lastnbits_range v 8). 
    replace Byte.min_signed with (- 2 ^ 7) by reflexivity. lia.
Qed.

Lemma store_short_cast : forall x v , x # Short |-> v |-- x # UShort |-> unsigned_last_nbits v 16.
Proof.
  intros.
  unfold store_short, store_ushort.
  entailer!.
  - unfold store_2byte.
    Intros z1 z2.
    sep_apply (store_byte_cast' x).
    sep_apply (store_byte_cast' (x + 1)).
    entailer!.
    Exists (unsigned_last_nbits z1 8).
    Exists (unsigned_last_nbits z2 8).
    entailer!.
    unfold merge_short in *.
    rewrite <- !unsigned_Lastnbits_mod_correct ; lia.
  - pose proof (unsigned_Lastnbits_range v 16). lia.
  - pose proof (unsigned_Lastnbits_range v 16). 
    lia.
Qed.

Lemma store_ushort_cast : forall x v , x # UShort |-> v |-- x # Short |-> signed_last_nbits v 16.
Proof.
  intros.
  unfold store_short, store_ushort.
  entailer!.
  - unfold store_2byte.
    Intros z1 z2.
    sep_apply (store_byte_cast x).
    sep_apply (store_byte_cast (x + 1)).
    entailer!.
    Exists (signed_last_nbits z1 8).
    Exists (signed_last_nbits z2 8).
    entailer!.
    unfold merge_short in *.
    rewrite <- !signed_Lastnbits_mod_correct ; lia.
  - pose proof (signed_Lastnbits_range v 16). lia.
  - pose proof (signed_Lastnbits_range v 16). lia. 
Qed. 

Lemma store_int_cast : forall x v , x # Int |-> v |-- x # UInt |-> unsigned_last_nbits v 32.
Proof.
  intros.
  unfold store_int, store_uint.
  entailer!.
  - unfold store_4byte. 
    Intros z1 z2 z3 z4.
    sep_apply (store_byte_cast' x).
    sep_apply (store_byte_cast' (x + 1)).
    sep_apply (store_byte_cast' (x + 2)).
    sep_apply (store_byte_cast' (x + 3)).
    Exists (unsigned_last_nbits z1 8).
    Exists (unsigned_last_nbits z2 8).
    Exists (unsigned_last_nbits z3 8).
    Exists (unsigned_last_nbits z4 8).
    entailer!.
    unfold merge_int in *.
    rewrite <- !unsigned_Lastnbits_mod_correct ; lia.
  - pose proof (unsigned_Lastnbits_range v 32). lia.  
  - pose proof (unsigned_Lastnbits_range v 32). 
    replace Int.max_unsigned with (2 ^ 32 - 1) by reflexivity. lia.
Qed.

Lemma store_uint_cast : forall x v , x # UInt |-> v |-- x # Int |-> signed_last_nbits v 32.
Proof.
  intros.
  unfold store_int, store_uint.
  entailer!.
  - unfold store_4byte. 
    Intros z1 z2 z3 z4.
    sep_apply (store_byte_cast x).
    sep_apply (store_byte_cast (x + 1)).
    sep_apply (store_byte_cast (x + 2)).
    sep_apply (store_byte_cast (x + 3)).
    Exists (signed_last_nbits z1 8).
    Exists (signed_last_nbits z2 8).
    Exists (signed_last_nbits z3 8).
    Exists (signed_last_nbits z4 8).
    entailer!.
    unfold merge_int in *.
    rewrite <- !signed_Lastnbits_mod_correct ; lia.
  - pose proof (signed_Lastnbits_range v 32).
    replace Int.max_signed with (2 ^ 31 - 1) by reflexivity. lia.  
  - pose proof (signed_Lastnbits_range v 32). 
    replace Int.min_signed with (- 2 ^ 31) by reflexivity. lia.
Qed.

Lemma store_int64_cast : forall x v , x # Int64 |-> v |-- x # UInt64 |-> unsigned_last_nbits v 64.
Proof.
  intros.
  unfold store_int64, store_uint64.
  entailer!.
  - unfold store_8byte. 
    Intros z1 z2 z3 z4.
    Intros z5 z6 z7 z8.
    sep_apply (store_byte_cast' x).
    sep_apply (store_byte_cast' (x + 1)).
    sep_apply (store_byte_cast' (x + 2)).
    sep_apply (store_byte_cast' (x + 3)).
    sep_apply (store_byte_cast' (x + 4)).
    sep_apply (store_byte_cast' (x + 5)).
    sep_apply (store_byte_cast' (x + 6)).
    sep_apply (store_byte_cast' (x + 7)).
    Exists (unsigned_last_nbits z1 8).
    Exists (unsigned_last_nbits z2 8).
    Exists (unsigned_last_nbits z3 8).
    Exists (unsigned_last_nbits z4 8).
    Exists (unsigned_last_nbits z5 8).
    Exists (unsigned_last_nbits z6 8).
    Exists (unsigned_last_nbits z7 8).
    Exists (unsigned_last_nbits z8 8).
    entailer!.
    unfold merge_int64 in *.
    rewrite <- !unsigned_Lastnbits_mod_correct ; lia.
  - pose proof (unsigned_Lastnbits_range v 64). lia.
  - pose proof (unsigned_Lastnbits_range v 64).
    replace Int64.max_unsigned with (2 ^ 64 - 1) by reflexivity. lia. 
Qed.

Lemma store_uint64_cast : forall x v , x # UInt64 |-> v |-- x # Int64 |-> signed_last_nbits v 64.
Proof.
  intros.
  unfold store_int64, store_uint64.
  entailer!.
  - unfold store_8byte. 
    Intros z1 z2 z3 z4.
    Intros z5 z6 z7 z8.
    sep_apply (store_byte_cast x).
    sep_apply (store_byte_cast (x + 1)).
    sep_apply (store_byte_cast (x + 2)).
    sep_apply (store_byte_cast (x + 3)).
    sep_apply (store_byte_cast (x + 4)).
    sep_apply (store_byte_cast (x + 5)).
    sep_apply (store_byte_cast (x + 6)).
    sep_apply (store_byte_cast (x + 7)).
    Exists (signed_last_nbits z1 8).
    Exists (signed_last_nbits z2 8).
    Exists (signed_last_nbits z3 8).
    Exists (signed_last_nbits z4 8).
    Exists (signed_last_nbits z5 8).
    Exists (signed_last_nbits z6 8).
    Exists (signed_last_nbits z7 8).
    Exists (signed_last_nbits z8 8).
    entailer!.
    unfold merge_int64 in *.
    rewrite <- !signed_Lastnbits_mod_correct ; lia.
  - pose proof (signed_Lastnbits_range v 64).
    replace Int64.max_signed with (2 ^ 63 - 1) by reflexivity. lia. 
  - pose proof (signed_Lastnbits_range v 64).
    replace Int64.min_signed with (- 2 ^ 63) by reflexivity. lia.
Qed.

Lemma valid_store_char : forall x v, x # Char |-> v |-- [| Byte.min_signed <= v <= Byte.max_signed /\ isvalidptr_char x |].
Proof.
  intros.
  unfold store_char.
  entailer!.
Qed.

Lemma valid_store_uchar : forall x v, x # UChar |-> v |-- [| 0 <= v <= Byte.max_unsigned /\ isvalidptr_char x |].
Proof.
  intros.
  unfold store_uchar.
  entailer!.
Qed.

Lemma valid_undef_store_char : forall x, x # Char |->_ |-- [| isvalidptr_char x |].
Proof.
  intros.
  unfold undef_store_char.
  entailer!.
Qed.

Lemma valid_undef_store_uchar : forall x, x # UChar |->_ |-- [| isvalidptr_char x |].
Proof.
  intros.
  unfold undef_store_uchar.
  entailer!.
Qed.

Lemma valid_store_short : forall x v, x # Short |-> v |-- [| -32768 <= v <= 32767 /\ isvalidptr_short x |].
Proof.
  intros.
  unfold store_short.
  entailer!.
Qed.

Lemma valid_store_ushort : forall x v, x # UShort |-> v |-- [| 0 <= v <= 65535 /\ isvalidptr_short x |].
Proof.
  intros.
  unfold store_ushort.
  entailer!.
Qed.

Lemma valid_undef_store_short : forall x, x # Short |->_ |-- [| isvalidptr_short x |].
Proof.
  intros.
  unfold undef_store_short.
  entailer!.
Qed.

Lemma valid_undef_store_ushort : forall x, x # UShort |->_ |-- [| isvalidptr_short x |].
Proof.
  intros.
  unfold undef_store_ushort.
  entailer!.
Qed.

Lemma valid_store_int : forall x v, x # Int |-> v |-- [| Int.min_signed <= v <= Int.max_signed /\ isvalidptr_int x |].
Proof.
  intros.
  unfold store_int.
  entailer!.
Qed.

Lemma valid_store_uint : forall x v, x # UInt |-> v |-- [| 0 <= v <= Int.max_unsigned /\ isvalidptr_int x |].
Proof.
  intros.
  unfold store_uint.
  entailer!.
Qed.

Lemma valid_undef_store_int : forall x, x # Int |->_ |-- [| isvalidptr_int x |].
Proof.
  intros.
  unfold undef_store_int.
  entailer!.
Qed.

Lemma valid_undef_store_uint : forall x, x # UInt |->_ |-- [| isvalidptr_int x |].
Proof.
  intros.
  unfold undef_store_uint.
  entailer!.
Qed.

Lemma valid_store_int64 : forall x v, x # Int64 |-> v |-- [| Int64.min_signed <= v <= Int64.max_signed /\ isvalidptr_int64 x |].
Proof.
  intros.
  unfold store_int64.
  entailer!.
Qed.

Lemma valid_store_uint64 : forall x v, x # UInt64 |-> v |-- [| 0 <= v <= Int64.max_unsigned /\ isvalidptr_int64 x |].
Proof.
  intros.
  unfold store_uint64.
  entailer!.
Qed.

Lemma valid_undef_store_int64 : forall x, x # Int64 |->_ |-- [| isvalidptr_int64 x |].
Proof.
  intros.
  unfold undef_store_int64.
  entailer!.
Qed.

Lemma valid_undef_store_uint64 : forall x, x # UInt64 |->_ |-- [| isvalidptr_int64 x |].
Proof.
  intros.
  unfold undef_store_uint64.
  entailer!.
Qed.

Lemma valid_store_ptr : forall x v, x # Ptr |-> v |-- [| isvalidptr x /\ 0 <= v /\ v <= Int.max_unsigned|].
Proof.
  intros.
  unfold store_ptr.
  entailer!.
Qed.

Lemma valid_undef_store_ptr : forall x, x # Ptr |->_ |-- [| isvalidptr x |].
Proof.
  intros.
  unfold undef_store_ptr.
  entailer!.
Qed.

Lemma store_int_align4 : forall x v, x # Int |-> v |-- store_align4_n 1.
Proof.
  intros.
  unfold store_int , store_align4_n.
  Intros. Exists [x]. 
  sep_apply store_4byte_store_4byte_noinit.
  simpl.
  entailer!. unfold isvalidptr_int , aligned_4 in H.
  constructor ; auto ; try lia.
  constructor.
Qed.

Lemma store_uint_align4 : forall x v, x # UInt |-> v |-- store_align4_n 1.
Proof.
  intros.
  unfold store_uint, store_align4_n. simpl.
  Intros. Exists [x]. 
  sep_apply store_4byte_store_4byte_noinit.
  simpl.
  entailer!.
  unfold isvalidptr_int , aligned_4 in H.
  constructor ; auto ; try lia.
  constructor.
Qed.

Lemma store_int64_align1 : forall x v, x # Int64 |-> v |-- store_align4_n 2.
Proof.
  intros.
  unfold store_int64, store_align4_n. simpl.
  Intros. Exists (x :: [x + 4]). 
  sep_apply store_8byte_store_8byte_noinit.
  simpl.
  entailer!.
  - unfold store_8byte_noninit.
    unfold store_4byte_noninit. 
    replace (x + 4 + 1) with (x + 5) by lia.
    replace (x + 4 + 2) with (x + 6) by lia.
    replace (x + 4 + 3) with (x + 7) by lia.
    entailer!.
  - unfold isvalidptr_int64 in H. unfold isvalidptr. 
    unfold aligned_4 in *. 
    repeat split ; try lia. 
    rewrite <- Zplus_mod_idemp_l.
    destruct H as [[? [? ?]] [? ?]].
    rewrite H1. reflexivity.
  - unfold isvalidptr_int64 in H. unfold isvalidptr. 
    unfold aligned_4 in *. 
    repeat split ; try lia.
  - unfold isvalidptr_int64, aligned_4 in H. 
    repeat constructor ; try lia. 
Qed.

Lemma store_uint64_align1 : forall x v, x # UInt64 |-> v |-- store_align4_n 2.
Proof.
  intros.
  unfold store_uint64, store_align4_n. simpl.
  Intros. Exists (x :: [x + 4]). 
  sep_apply store_8byte_store_8byte_noinit.
  simpl.
  entailer!.
  - unfold store_8byte_noninit.
    unfold store_4byte_noninit. 
    replace (x + 4 + 1) with (x + 5) by lia.
    replace (x + 4 + 2) with (x + 6) by lia.
    replace (x + 4 + 3) with (x + 7) by lia.
    entailer!.
  - unfold isvalidptr_int64 in H. unfold isvalidptr. 
    unfold aligned_4 in *. 
    repeat split ; try lia. 
    rewrite <- Zplus_mod_idemp_l.
    destruct H as [[? [? ?]] [? ?]].
    rewrite H1. reflexivity.
  - unfold isvalidptr_int64 in H. unfold isvalidptr. 
    unfold aligned_4 in *. 
    repeat split ; try lia.
  - unfold isvalidptr_int64, aligned_4 in H. 
    repeat constructor ; try lia. 
Qed.

Lemma store_ptr_align4 : forall x v, x # Ptr |-> v |-- store_align4_n 1.
Proof.
  intros.
  unfold store_ptr, store_align4_n. simpl.
  Intros. Exists [x]. 
  sep_apply store_4byte_store_4byte_noinit.
  simpl. 
  entailer!.
  unfold isvalidptr , aligned_4 in H.
  constructor ; auto ; try lia.
  constructor.
Qed.

Lemma store_4byte_valid : forall x y, store_4byte_noninit x ** store_4byte_noninit y |-- [| x + 3 < y \/ y + 3 < x |].
Proof.
  intros.
  unfold store_4byte_noninit.
  destruct (Z_lt_ge_dec (x + 3) y).
  - entailer!. 
  - destruct (Z_lt_ge_dec (y + 3) x).
    + entailer!.
    + assert (x = y - 3 \/ x = y - 2 \/ x = y - 1 \/ x = y \/ x = y + 1 \/ x = y + 2 \/ x = y + 3) by lia.
      destruct H as [? | [? | [? | [? | [? | [? | ?]]]]]] ; subst.
      * replace (y - 3 + 3) with y by lia. 
        prop_apply (dup_store_byte_noninit y). Intros. lia.
      * replace (y - 2 + 2) with y by lia. 
        prop_apply (dup_store_byte_noninit y). Intros. lia. 
      * replace (y - 1 + 1) with y by lia. 
        prop_apply (dup_store_byte_noninit y). Intros. lia.
      * prop_apply (dup_store_byte_noninit y). Intros. lia.
      * prop_apply (dup_store_byte_noninit (y + 1)). Intros. lia.
      * prop_apply (dup_store_byte_noninit (y + 2)). Intros. lia.
      * prop_apply (dup_store_byte_noninit (y + 3)). Intros. lia. 
Qed.

Lemma store_align4_valid : forall x l, store_align4_list l ** store_4byte_noninit x |-- [| Forall (fun x' => x + 3 < x' \/ x' + 3 < x) l |].
Proof.
  intros.
  induction l; simpl in *. 
  - entailer!.
  - Intros.
    prop_apply (store_4byte_valid a x). Intros.
    prop_apply IHl. Intros.
    entailer!.
    constructor ; auto.
    destruct H0; auto.
Qed.

Lemma store_align4_merge : forall n m, store_align4_n n ** store_align4_n m |-- store_align4_n (n + m).
Proof.
  intros.
  unfold store_align4_n. Intros l1 l2. 
  Exists (l1 ++ l2). destruct H , H0. 
  revert dependent l2. revert dependent n. revert m.
  induction H1 ; simpl in * ; intros ; auto.
  - entailer!. cbv in H. lia.  
  - rewrite Zlength_cons in *.
    specialize (IHinterval_list m (n - 1) (ltac:(lia)) l2 H4 H5).
    Intros.
    sep_apply IHinterval_list. Intros.
    destruct H7.
    prop_apply (store_align4_valid x (l ++ l2)). Intros.
    entailer!.
    constructor ; auto.
Qed. 

Lemma store_align4_n_valid : forall n, store_align4_n n |-- [| n <= Int.max_unsigned / 4 + 1|].
Proof.
  intros.
  unfold store_align4_n.
  Intros l.
  destruct H.
  rewrite <- H.
  entailer!.
  replace Int.max_unsigned with (4294967295) in * by reflexivity.
  pose proof interval_list_range l 3 0 4294967295 (ltac:(lia)) (ltac:(lia)) H0.
  simpl in *.
  lia.
Qed.

End StoreLibSig.