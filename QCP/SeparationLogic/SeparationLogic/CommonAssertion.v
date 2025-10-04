Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import String.
Require Import Permutation.

From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From compcert.lib Require Import Coqlib Integers.

From SimpleC.SL Require Import Mem.
From SimpleC.SL Require Export IntLib.
From AUXLib Require Export ListLib.
From SimpleC.SL Require Export CNotation.

Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.

Module Type BasePredSig (Import Names: LanguageSig) (Import DerivedNames: DerivedNamesSig Names).
Parameter mstore: addr -> Z -> expr.
Parameter mstore_noninit: addr -> expr.
Axiom mstore_mstore_noninit:
  forall p v s,
    mstore p v s ->
    mstore_noninit p s.

Axiom mstore_eqm:
  forall p v v',
    Byte.eqm v v' ->
    derivable1 (mstore p v) (mstore p v').

Axiom dup_mstore_noninit: 
  forall x,
    derivable1
      (sepcon (mstore_noninit x) (mstore_noninit x))
      (coq_prop False).
End BasePredSig.

Module Type SeparationLogicSig :=
  LanguageSig <+ 
  DerivedNamesSig <+
  PrimitiveRuleSig <+
  LogicTheoremSig' <+
  BasePredSig.

Definition aligned_2 (x : Z) : Prop := x mod 2 = 0.

Definition aligned_4 (x : Z) : Prop := x mod 4 = 0.

Definition aligned_8 (x : Z) : Prop := x mod 8 = 0.

Definition isvalidptr_char (x : Z) : Prop :=
  x >= 0 /\ x <= Int.max_unsigned.

Definition isvalidptr_short (x : Z) : Prop := 
  x >= 0 /\ x + 1 <= Int.max_unsigned /\ aligned_2 x.  

Definition isvalidptr_int (x : Z) : Prop :=
  x >= 0 /\ x + 3 <= Int.max_unsigned /\ aligned_4 x.

Definition isvalidptr_int64 (x : Z) : Prop :=
  x >= 0 /\ x + 7 <= Int.max_unsigned /\ aligned_4 x.

Definition isvalidptr (x : Z) : Prop :=
  x >= 0 /\ x + 3 <= Int.max_unsigned /\ aligned_4 x.

(* In the folloing definition, "mod" is the math modulo,
   a mod b always has the same sign with b (see Z.mod_bound_pos
   and Z.mod_neg_bound). In comparison, "%" is the C/C++
   modulo, a % b always has the same sign with a.*)

Definition merge_short (x1 x2 y: Z): Prop :=
  y mod (2^16) =
  x1 mod (2^8) * (2^8) +
  x2 mod (2^8).

Example merge_short_255_255_neg_1:
  merge_short 255 255 (-1).
Proof. reflexivity. Qed.

Example merge_short_255_neg1_neg_1:
  merge_short 255 (-1) (-1).
Proof. reflexivity. Qed.

Definition merge_int (x1 x2 x3 x4 y: Z): Prop :=
  y mod (2^32) =
  x1 mod (2^8) * (2^24) +
  x2 mod (2^8) * (2^16) +
  x3 mod (2^8) * (2^8) +
  x4 mod (2^8).

Definition merge_int64 (x1 x2 x3 x4 x5 x6 x7 x8 y: Z): Prop :=
  y mod (2^64) =
  x1 mod (2^8) * (2^56) +
  x2 mod (2^8) * (2^48) +
  x3 mod (2^8) * (2^40) +
  x4 mod (2^8) * (2^32) +
  x5 mod (2^8) * (2^24) +
  x6 mod (2^8) * (2^16) +
  x7 mod (2^8) * (2^8) +
  x8 mod (2^8).

Theorem merge_int_equiv : 
forall (x1 x2 x3 x4 : Z) (v1 v2 v3 v4 : Z), forall z, 
-128 <= x1 < 128 -> -128 <= x2 < 128 ->
-128 <= x3 < 128 -> -128 <= x4 < 128 ->
-128 <= v1 < 128 -> -128 <= v2 < 128 ->
-128 <= v3 < 128 -> -128 <= v4 < 128 ->
merge_int x1 x2 x3 x4 z -> merge_int v1 v2 v3 v4 z ->
x1 = v1 /\ x2 = v2 /\ x3 = v3 /\ x4 = v4.
Proof.
  intros.
  unfold merge_int in *. 
  replace (2 ^ 8) with 256 in * by (unfold Z.pow; simpl; auto).
  rewrite H7 in H8. clear H7.
  rewrite <-! Z.add_assoc in H8.
  pose proof (Z.mod_pos_bound v2 256 (ltac : (lia))) as valid_v2.
  pose proof (Z.mod_pos_bound v3 256 (ltac : (lia))) as valid_v3.
  pose proof (Z.mod_pos_bound v4 256 (ltac : (lia))) as valid_v4.
  pose proof (Z.mod_pos_bound x2 256 (ltac : (lia))) as valid_x2.
  pose proof (Z.mod_pos_bound x3 256 (ltac : (lia))) as valid_x3.
  pose proof (Z.mod_pos_bound x4 256 (ltac : (lia))) as valid_x4.
  assert (x1 mod 256 = v1 mod 256).
  {
    assert ((x1 mod 256 * 2 ^ 24 + (x2 mod 256 * 2 ^ 16 + (x3 mod 256 * 256 + x4 mod 256))) / 2 ^ 24 = (v1 mod 256 * 2 ^ 24 + (v2 mod 256 * 2 ^ 16 + (v3 mod 256 * 256 + v4 mod 256))) / 2 ^ 24) by (rewrite H8 ; reflexivity).
    rewrite !Z.div_add_l in H7 ; try lia.
  }
  assert (x1 = v1).
  { 
    rewrite Zmod_eq_full in H7 ; try lia.
    rewrite Zmod_eq_full in H7 ; try lia.
  }
  subst.
  apply Z.add_reg_l in H8. clear H7.
  assert (x2 mod 256 = v2 mod 256).
  {
    assert ((x2 mod 256 * 2 ^ 16 + (x3 mod 256 * 256 + x4 mod 256)) / 2 ^ 16 = (v2 mod 256 * 2 ^ 16 + (v3 mod 256 * 256 + v4 mod 256)) / 2 ^ 16) by (rewrite H8 ; reflexivity).
    rewrite !Z.div_add_l in H7 ; try lia.
  }
  assert (x2 = v2).
  { 
    rewrite Zmod_eq_full in H7 ; try lia.
    rewrite Zmod_eq_full in H7 ; try lia.
  }
  subst.
  apply Z.add_reg_l in H8. clear H7.
  assert (x3 mod 256 = v3 mod 256).
  {
    assert ((x3 mod 256 * 256 + x4 mod 256) / 256 = (v3 mod 256 * 256 + v4 mod 256) / 256) by (rewrite H8 ; reflexivity).
    rewrite !Z.div_add_l in H7 ; try lia.
  }
  assert (x3 = v3).
  { 
    rewrite Zmod_eq_full in H7 ; try lia.
    rewrite Zmod_eq_full in H7 ; try lia.
  }
  subst.
  apply Z.add_reg_l in H8. clear H7.
  repeat split ; try lia.
  rewrite Zmod_eq_full in H8 ; try lia.
  rewrite Zmod_eq_full in H8 ; try lia.
Qed.

Theorem merge_uint_equiv : 
forall (x1 x2 x3 x4 : Z) (v1 v2 v3 v4 : Z), forall z, 
0 <= x1 < 256 -> 0 <= x2 < 256 ->
0 <= x3 < 256 -> 0 <= x4 < 256 ->
0 <= v1 < 256 -> 0 <= v2 < 256 ->
0 <= v3 < 256 -> 0 <= v4 < 256 ->
merge_int x1 x2 x3 x4 z -> merge_int v1 v2 v3 v4 z ->
x1 = v1 /\ x2 = v2 /\ x3 = v3 /\ x4 = v4.
Proof.
  intros.
  unfold merge_int in *. 
  replace (2 ^ 8) with 256 in * by (unfold Z.pow; simpl; auto).
  rewrite H7 in H8. clear H7.
  rewrite <-! Z.add_assoc in H8.
  rewrite ! Z.mod_small in H8 ; try lia.
Qed.

Module Type DerivedPredSig (CRules: SeparationLogicSig). 

Arguments CRules.exp {A}.

Definition store_byte : addr -> Z -> CRules.expr := CRules.mstore.

Definition store_2byte (x : addr) (v : Z) : CRules.expr := 
  CRules.exp (fun z1 => 
  CRules.exp (fun z2 =>
    CRules.andp 
    (CRules.coq_prop (merge_short z1 z2 v))
    (CRules.sepcon (store_byte x z1) (store_byte (x+1) z2))
  )).
Definition store_4byte (x : addr) (v : Z) : CRules.expr :=
  CRules.exp (fun z1 => 
  CRules.exp (fun z2 =>
  CRules.exp (fun z3 =>
  CRules.exp (fun z4 =>
    CRules.andp 
    (CRules.coq_prop (merge_int z1 z2 z3 z4 v))
    (CRules.sepcon (store_byte x z1)
      (CRules.sepcon (store_byte (x+1) z2)
        (CRules.sepcon (store_byte (x+2) z3) (store_byte (x+3) z4))  
    )
  ))))).
     
Definition store_8byte (x : addr) (v : Z) : CRules.expr :=
  CRules.exp (fun z1 => 
  CRules.exp (fun z2 =>
  CRules.exp (fun z3 =>
  CRules.exp (fun z4 =>
  CRules.exp (fun z5 => 
  CRules.exp (fun z6 =>
  CRules.exp (fun z7 =>
  CRules.exp (fun z8 =>
    CRules.andp 
    (CRules.coq_prop (merge_int64 z1 z2 z3 z4 z5 z6 z7 z8 v))
    (CRules.sepcon (store_byte x z1)
      (CRules.sepcon (store_byte (x+1) z2)
        (CRules.sepcon (store_byte (x+2) z3) 
          (CRules.sepcon (store_byte (x+3) z4)
            (CRules.sepcon (store_byte (x+4) z5)
              (CRules.sepcon (store_byte (x+5) z6)
                (CRules.sepcon (store_byte (x+6) z7) (store_byte (x+7) z8) 
                )
              )
            )
          )
        )  
      )
    )
  )))))))).

Definition store_byte_noninit : addr -> CRules.expr := CRules.mstore_noninit.

Definition store_2byte_noninit (x : addr) : CRules.expr := 
  CRules.sepcon (store_byte_noninit x) (store_byte_noninit (x+1)).

Definition store_4byte_noninit (x : addr) : CRules.expr :=
  CRules.sepcon (store_byte_noninit x)
    (CRules.sepcon (store_byte_noninit (x+1))
      (CRules.sepcon (store_byte_noninit (x+2)) (store_byte_noninit (x+3)))).

Definition store_8byte_noninit (x : addr) : CRules.expr :=
  (CRules.sepcon (store_byte_noninit x)
  (CRules.sepcon (store_byte_noninit (x+1))
    (CRules.sepcon (store_byte_noninit (x+2)) 
      (CRules.sepcon (store_byte_noninit (x+3))
        (CRules.sepcon (store_byte_noninit (x+4))
          (CRules.sepcon (store_byte_noninit (x+5))
            (CRules.sepcon (store_byte_noninit (x+6)) (store_byte_noninit (x+7))))))))).
  
(* The following are notations *)  
Declare Scope sac_scope.
Delimit Scope sac_scope with sac.
Local Open Scope sac_scope.

Notation "'emp'" := (CRules.emp) : sac_scope.
Notation "x |-- y" := (CRules.derivable1 x y) (at level 70, no associativity) : sac_scope.
Notation "x --||-- y" := (CRules.logic_equiv x y) (at level 60, no associativity) : sac_scope.
Notation "x -* y" := (CRules.wand x y) (at level 45, right associativity) : sac_scope.
Notation "x --> y" := (CRules.impp x y) : sac_scope.
Notation "x || y" := (CRules.orp x y) : sac_scope.
Notation "x && y" := (CRules.andp x y) : sac_scope.
Notation "x ** y" := (CRules.sepcon x y) (at level 31, left associativity) : sac_scope.
Notation " [| P |] " := (CRules.coq_prop P) (at level 29, no associativity) :sac_scope.
Notation " 'TT' " := (CRules.truep) (at level 34, no associativity) : sac_scope.
Notation "'EX' x , p " :=
  (CRules.exp (fun x => p))
    (at level 45, x binder, right associativity) : sac_scope.
Notation "'EX' x : t , p " :=
  (CRules.exp (fun x : t => p))
    (at level 45, x binder, right associativity) : sac_scope.
Notation "'EX' x .. y , p" :=
  (CRules.exp (fun x => .. (CRules.exp (fun y => p)) ..))
    (at level 45, x binder, right associativity) : sac_scope.
Notation "'ALL' x , p " :=
  (CRules.allp _ (fun x => p))
    (at level 45, x binder, right associativity) : sac_scope.
Notation "'ALL' x : t , p " :=
  (CRules.allp _ (fun x : t => p))
    (at level 45, x binder, right associativity) : sac_scope.
Notation "'ALL' x .. y , p" :=
  (CRules.allp _ (fun x => .. (CRules.allp _ (fun y => p)) ..))
    (at level 45, x binder, right associativity) : sac_scope.

Definition store_char (x : addr) (v : Z) :=
  [| isvalidptr_char x /\ v <= Byte.max_signed /\ v >= Byte.min_signed |] && store_byte x v.

Definition undef_store_char (x : addr) :=
  [| isvalidptr_char x |] && store_byte_noninit x.

Definition store_uchar (x : addr) (v : Z) :=
  [| isvalidptr_char x /\ v >= 0 /\ v <= Byte.max_unsigned |] && 
  store_byte x v.

Definition undef_store_uchar (x : addr) :=
  [| isvalidptr_char x |] && store_byte_noninit x.

Definition store_short (x : addr) (v : Z) :=
  [| isvalidptr_short x /\ v <= 32767 /\ v >= -32768 |] && store_2byte x v.

Definition undef_store_short (x : addr) :=
  [| isvalidptr_short x |] && store_2byte_noninit x.

Definition store_ushort (x : addr) (v : Z) :=
  [| isvalidptr_short x /\ v >= 0 /\ v <= 65535 |] &&
  store_2byte x v.

Definition undef_store_ushort (x : addr) :=
  [| isvalidptr_short x |] && store_2byte_noninit x.

Definition store_int (x : addr) (v : Z) :=
  [| isvalidptr_int x /\ v <= Int.max_signed /\ v >= Int.min_signed |] && store_4byte x v.

Definition undef_store_int (x : addr) :=
  ([| isvalidptr_int x |] && store_4byte_noninit x).

Definition store_uint (x : addr) (v : Z) :=
  [| isvalidptr_int x /\ v >= 0 /\ v <= Int.max_unsigned |] && 
  store_4byte x v.

Definition undef_store_uint (x : addr) :=
  [| isvalidptr_int x |] && store_4byte_noninit x.

Definition store_int64 (x : addr) (v : Z) :=
  [| isvalidptr_int64 x /\ v <= Int64.max_signed /\ v >= Int64.min_signed |] && store_8byte x v.

Definition undef_store_int64 (x : addr) :=
  [| isvalidptr_int64 x |] && store_8byte_noninit x.

Definition store_uint64 (x : addr) (v : Z) :=
  [| isvalidptr_int64 x /\ v >= 0 /\ v <= Int64.max_unsigned |] && 
  store_8byte x v.

Definition undef_store_uint64 (x : addr) :=
  [| isvalidptr_int64 x |] && store_8byte_noninit x.

Definition store_ptr (x : addr) (v : Z) := 
  [| isvalidptr x /\ v >= 0 /\ v <= Int.max_unsigned |] && 
  store_4byte x v.

Definition undef_store_ptr (x : addr) :=
  [| isvalidptr x |] && store_4byte_noninit x.

Definition Invalid_store (x : addr) (v : Z) :=
  [| False |].

Definition Invalid_undef_store (x : addr) :=
  [| False |].

Definition dup_data_at_error (x : addr) := 
  [| False |].

Definition dup_data_at_error_prop : Prop := True.

Fixpoint store_array_rec {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (lo hi: Z) (l: list A): CRules.expr :=
  match l with
  | nil     => [| lo = hi |] && [| l = nil |] && emp
  | a :: l0 => storeA x lo a ** store_array_rec storeA x (lo + 1) hi l0
  end.

Fixpoint store_array_missing_i_rec {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (i lo hi: Z) (l: list A): CRules.expr :=
  match l with
  | nil     => [| False |]
  | a :: l0 => [| i = lo |] && store_array_rec storeA x (lo + 1) hi l0 ||
               [| i > lo |] && storeA x lo a ** store_array_missing_i_rec storeA x i (lo + 1) hi l0
  end.

Definition store_array {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (n: Z) (l: list A): CRules.expr :=
  store_array_rec storeA x 0 n l.

Fixpoint store_undef_array_rec (storeA : addr -> Z -> CRules.expr) (x: addr) (lo hi: Z) (n: nat): CRules.expr :=
  match n with 
    | O => [| lo = hi |] && emp 
    | S n' => storeA x lo ** store_undef_array_rec storeA x (lo + 1) hi n'
  end.

Fixpoint store_undef_array_missing_i_rec (storeA : addr -> Z -> CRules.expr) (x: addr) (i lo hi: Z) (n: nat): CRules.expr :=
  match n with 
    | O => [| False |]
    | S n' => [| i = lo |] && store_undef_array_rec storeA x (lo + 1) hi n' ||
               [| i > lo |] && storeA x lo ** store_undef_array_missing_i_rec storeA x i (lo + 1) hi n'
  end.

Definition store_undef_array (storeA : addr -> Z -> CRules.expr) (x: addr) (n: Z): CRules.expr :=
  store_undef_array_rec storeA x 0 n (Z.to_nat n).

Fixpoint store_align4_list (l : list Z) := 
  match l with 
    | nil => emp
    | x :: l' => [| isvalidptr x |] && store_4byte_noninit x ** store_align4_list l'
  end.

Definition store_align4_n (n : Z) :=
  EX l, [| Zlength l = n /\ interval_list 3 0 Int.max_unsigned l |] && store_align4_list l.

Notation "x # 'Char' |-> v" := (store_char x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'UChar' |-> v" := (store_uchar x v ) (at level 25, no associativity):sac_scope.
Notation "x # 'Short' |-> v" := (store_short x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'UShort' |-> v" := (store_ushort x v) (at level 25, no associativity):sac_scope.
Notation "x # 'Int' |-> v" := ( store_int x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'UInt' |-> v" := ( store_uint x v ) (at level 25, no associativity):sac_scope.
Notation "x # 'Int64' |-> v" := ( store_int64 x v) (at level 25, no associativity):sac_scope.
Notation "x # 'UInt64' |-> v" := ( store_uint64 x v) (at level 25, no associativity):sac_scope.
Notation "x # 'Ptr' |-> v" := (store_ptr x v) (at level 25, no associativity):sac_scope.

Notation " x # 'Char' |->_" := (undef_store_char x) (at level 25, no associativity) : sac_scope.
Notation "x # 'UChar' |->_" := (undef_store_uchar x) (at level 25, no associativity):sac_scope.
Notation "x # 'Short' |->_" := (undef_store_short x) (at level 25, no associativity) : sac_scope.
Notation "x # 'UShort' |->_" := (undef_store_ushort x) (at level 25, no associativity):sac_scope.
Notation "x # 'Int' |->_" := (undef_store_int x) (at level 25, no associativity) : sac_scope.
Notation "x # 'UInt' |->_" := (undef_store_uint x) (at level 25, no associativity):sac_scope.
Notation "x # 'Int64' |->_" := (undef_store_int64 x) (at level 25, no associativity):sac_scope.
Notation "x # 'UInt64' |->_" := (undef_store_uint64 x) (at level 25, no associativity):sac_scope.
Notation "x # 'Ptr' |->_" := (undef_store_ptr x) (at level 25, no associativity):sac_scope.

Definition poly_store (ty : front_end_type) := 
  match ty with 
    | FET_int => store_int
    | FET_char => store_char
    | FET_int64 => store_int64
    | FET_short => store_short
    | FET_uint => store_uint
    | FET_uchar => store_uchar
    | FET_uint64 => store_uint64
    | FET_ushort => store_ushort
    | FET_ptr => store_ptr 
    | _ => Invalid_store
  end.

Definition poly_undef_store (ty : front_end_type) := 
  match ty with 
    | FET_int => undef_store_int
    | FET_char => undef_store_char
    | FET_int64 => undef_store_int64
    | FET_short => undef_store_short
    | FET_uint => undef_store_uint
    | FET_uchar => undef_store_uchar
    | FET_uint64 => undef_store_uint64
    | FET_ushort => undef_store_ushort
    | FET_ptr => undef_store_ptr
    | _ => Invalid_undef_store
  end.

Notation "x # ty |-> v" := (poly_store ty x v) (at level 25, no associativity) : sac_scope.
Notation "x # ty |->_" := (poly_undef_store ty x) (at level 25, no associativity) : sac_scope.

(*TODO: to be rewrite *)
Definition struct_padding (x : lvalue_expr) (struct_name : string) : CRules.expr := emp.

Definition union_padding (x : lvalue_expr) (union_name field_name : string) : CRules.expr := emp.

Notation " 'Padding' x struct_name " := (struct_padding x struct_name) (at level 25, no associativity) : sac_scope.

Notation " 'Padding' x union_name . field_name " := (union_padding x union_name field_name) (at level 25, no associativity) : sac_scope.

Import CRules.

(* The following are derived rules *)

Arguments derivable1s_exp_l {A} _ _ _ .
Arguments derivable1s_allp_r {A} _ _ _ .
Arguments derivable1s_exp_r {A} _ _ _ .
Arguments derivable1s_allp_l {A} _ _ _ .

Lemma coq_prop_andp_left : forall (P : Prop) (Q R : expr), (P -> Q |-- R) -> [| P |] && Q |-- R.
Proof.
  unfold andp, coq_prop, derivable1 ; intros. apply H ; tauto.
Qed.

Lemma coq_prop_andp_right : forall (P : Prop) (Q R : expr), R |-- Q -> P -> R |-- [| P |] && Q.
Proof.
  unfold andp, coq_prop, derivable1 ; intros.
  specialize (H m). tauto.
Qed.

Lemma coq_prop_imply : forall (P Q : Prop), (P -> Q) -> [| P |] |-- [| Q |].
Proof.
  intros.
  unfold coq_prop, derivable1 ; intros ; tauto.
Qed.

Lemma coq_prop_False_left : forall (P : Prop) Q, (P -> False) -> [| P |] |-- Q.
Proof.
  intros.
  unfold coq_prop, derivable1 ; intros ; tauto.
Qed.

Lemma orp_sepcon_left : forall P Q R, (P || Q) ** R |-- (P ** R) || (Q ** R).
Proof.
  intros.
  unfold orp, sepcon, derivable1; intros.
  my_destruct H.
  - left. exists x ,x0. tauto.
  - right. exists x, x0. tauto.
Qed. 

Lemma orp_sepcon_right : forall P Q R, P ** (Q || R) |-- (P ** Q) || (P ** R).
Proof.
  intros.
  unfold orp, sepcon, derivable1; intros.
  my_destruct H.
  - left. exists x ,x0. tauto.
  - right. exists x, x0. tauto.
Qed.

Lemma orp_sepcon_left' : forall P Q R, (P ** R) || (Q ** R) |-- (P || Q) ** R.
Proof.
  intros.
  unfold orp, sepcon, derivable1; intros.
  my_destruct H.
  - exists x ,x0. tauto.
  - exists x, x0. tauto.
Qed. 

Lemma orp_sepcon_right' : forall P Q R, (P ** Q) || (P ** R) |-- P ** (Q || R).
Proof.
  intros.
  unfold orp, sepcon, derivable1; intros.
  my_destruct H.
  - exists x ,x0. tauto.
  - exists x, x0. tauto.
Qed.

Lemma orp_sepcon_left_equiv : forall P Q R, (P || Q) ** R --||-- (P ** R) || (Q ** R).
Proof.
  intros.
  split ; [apply orp_sepcon_left | apply orp_sepcon_left'].
Qed.

Lemma orp_sepcon_right_equiv : forall P Q R, P ** (Q || R) --||-- (P ** Q) || (P ** R).
Proof.
  intros.
  split ; [apply orp_sepcon_right | apply orp_sepcon_right'].
Qed.

Lemma exp_right_exists : forall {A: Type} P (Q: A -> expr),
 (exists x, P |-- Q x) -> P |-- EX x, Q x.
Proof.
  unfold derivable1, exp;intros.
  destruct H.
  eexists. intuition auto. Qed.

Lemma derivable1_imp : forall P Q st, P |-- Q ->  P st -> Q st.
Proof.
  unfold derivable1; intros.
  intuition auto.
Qed.

Lemma derivable1_andp_mono : forall x1 x2 y1 y2 : expr, x1 |-- x2 -> y1 |-- y2 -> x1 && y1 |-- x2 && y2.
Proof.
  unfold derivable1, andp; intros * H H0 * [? ?].
  split;intuition auto.
Qed.

Lemma ex_logic_equiv_andp:
  forall {A : Type} (P : A -> expr) (Q :  expr),
  (EX y, P y) && Q  --||-- EX x : A, P x && Q.
Proof.
  unfold andp, logic_equiv, exp, derivable1;split;intros;my_destruct H ; eauto.
Qed.

Lemma wand_equiv : forall P Q P' Q',
  P --||-- P' ->
  Q --||-- Q' ->
  P -* Q --||-- P' -* Q'.
Proof.
  unfold wand, logic_equiv, derivable1 in *.
  split; intros; destruct H, H0.
  specialize (H1 _ _ H2).
  apply H0, H1, H4, H3.
  specialize (H1 _ _ H2).
  apply H5, H1, H, H3.
Qed.

Lemma ex_logic_equiv_sepcon:
  forall {A : Type} (P : A -> expr) (Q : expr),
  (EX y, P y) ** Q  --||-- EX x : A, P x ** Q.
Proof.
  unfold sepcon, logic_equiv, exp, derivable1;split;intros;my_destruct H.
  - do 3 eexists. split; eauto.
  - do 2 eexists. split;eauto.
Qed.

Lemma prop_add_left : forall P Q, P |-- [| Q |] -> P --||-- [| Q |] && P.
Proof.
  unfold coq_prop, logic_equiv, derivable1, andp ; intros.
  split ; try tauto ; split ; auto.
  eapply H. eauto.
Qed.

Lemma truep_andp_left_equiv : forall P, TT && P --||-- P.
Proof.
  intros.
  unfold logic_equiv, andp, truep, derivable1; split; intros ; tauto.
Qed.

Lemma truep_andp_right_equiv : forall P, P && TT --||-- P.
Proof.
  intros.
  unfold logic_equiv, andp, truep, derivable1; split; intros ; tauto.
Qed.

Lemma sepcon_emp_equiv : 
  forall x, x ** emp --||-- x.
Proof.
  intros. split.
  apply derivable1_sepcon_emp_l.
  apply derivable1_sepcon_emp_r.
Qed.

Lemma sepcon_cancel_res_emp : 
  forall P Q, emp |-- Q -> P |-- P ** Q.
Proof.
  intros.
  rewrite <- sepcon_emp_equiv at 1.
  apply derivable1_sepcon_mono.
  apply derivable1_refl.
  auto.
Qed.

Lemma sepcon_cancel_end : 
  forall P Q R, P |-- R -> emp |-- Q -> P |-- R ** Q.
Proof.
  intros.
  rewrite <- sepcon_emp_equiv at 1.
  apply derivable1_sepcon_mono ; auto.
Qed.

Lemma sepcon_prop_equiv : 
forall P Q,
P ** ([| Q |]) --||-- [| Q |] && P ** TT.
Proof.
  unfold logic_equiv, sepcon, andp, truep, coq_prop, derivable1;
  split;intros.
  - my_destruct H.
    split ; auto.
    do 2 eexists. split;eauto.
  - my_destruct H.
    do 2 eexists. split;eauto.
Qed.

Lemma exp_exp_right: forall {A: Type} P (Q : A -> expr),
  (exists x, P |-- Q x) -> 
  P |-- EX x, Q x.
Proof.
  intros.
  unfold exp, derivable1 in *.
  destruct H. intros.
  exists x. auto.
Qed.

Lemma exp_allp_left: forall {A: Type} (P: A -> expr) Q,
  (exists x, P x |-- Q) -> 
  ALL x, P x|-- Q.
Proof.
  intros.
  unfold exp, allp, derivable1 in *.
  destruct H. intros. auto.
Qed.

Lemma exp_allp_swap: forall {A B : Type} (P : A -> B -> expr), EX x, ALL y, P x y |-- ALL y, EX x, P x y.
Proof.
  intros.
  unfold exp, allp, derivable1; intros.
  destruct H. exists x. auto.
Qed.

Lemma allp_allp_swap: forall {A B : Type} (P : A -> B -> expr), ALL x, ALL y, P x y |-- ALL y, ALL x, P x y.
Proof.
  intros.
  unfold exp, allp, derivable1; intros.
  auto.
Qed.

Definition derivable1_wand_sepcon_adjoint := derivable1s_wand_sepcon_adjoint.

(* The following are ltac to simplify proof *)

Inductive all_list : Type :=
  | norm_asrt : expr -> all_list
  | dependent_asrt : forall (A : Type), (A -> expr) -> all_list.

Ltac All_listasrts_rec P L :=
  match P with 
  | ?A ** ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in 
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?A && ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?A -* ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?A || ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | @exp ?t ?A => constr:(cons (dependent_asrt t A) L)
  | @allp ?t ?A => constr:(L)
  | TT => constr:(L)
  | emp => constr:(L)
  | ?x => constr:(cons (norm_asrt x) L)
  end.

Ltac All_listasrts P :=
  let l:= (All_listasrts_rec P (@nil all_list)) in 
  constr:(l).

Ltac Rename_rec l Tac :=
  match l with 
  | nil => Tac 
  | ?x :: ?l' => 
    let a := fresh "v" in
    match x with 
      | norm_asrt ([| ?B |]) => pose (a := B) ; change B with a
      | norm_asrt ?v => pose (a := v) ; change v with a
      | dependent_asrt _ ?B => pose (a := B) ; change B with a
    end; Rename_rec l' Tac ; subst a
  end. 

Ltac Rename Tac:= 
  match goal with 
  | |- ?P |-- ?Q => 
    let L1 := All_listasrts P in 
    let L2 := All_listasrts Q in
    let l := eval cbn [List.app] in (List.app L1 L2) in
      Rename_rec l Tac
  | |- ?P --||-- ?Q => 
    let L1 := All_listasrts P in 
    let L2 := All_listasrts Q in
    let l := eval cbn [List.app] in (List.app L1 L2) in
      Rename_rec l Tac
  | _ => idtac 
  end.

Ltac pure_Rename_rec l :=
  match l with 
  | nil => idtac 
  | ?x :: ?l' => 
    let a := fresh "v" in
    match x with 
      | norm_asrt ([| ?B |]) => pose (a := B) ; change B with a
      | norm_asrt ?v => pose (a := v) ; change v with a
      | dependent_asrt _ ?B => pose (a := B) ; change B with a
    end; pure_Rename_rec l'
  end. 

Ltac pure_Rename := 
  match goal with 
  | |- ?P |-- ?Q => 
    let L1 := All_listasrts P in 
    let L2 := All_listasrts Q in
    let l := eval cbn [List.app] in (List.app L1 L2) in
      pure_Rename_rec l
  end.

Ltac sepcon_lift'' p :=
  match goal with 
  | |- ?P |-- ?Q  => match Q with 
                    | context [?x ** p] => rewrite (logic_equiv_sepcon_comm x p) 
                    | context [?x ** (p ** ?y) ] => rewrite (logic_equiv_sepcon_swap x p y) 
                    end
  | |- ?P |-- ?Q  => match P with 
                    | context [?x ** p] => rewrite (logic_equiv_sepcon_comm x p) 
                    | context [?x ** (p ** ?y) ] => rewrite (logic_equiv_sepcon_swap x p y) 
                    end
  end.

Ltac sepcon_lift' p := sepcon_lift'' p ;
  repeat progress (sepcon_lift'' p).

Ltac find_lift x Hp :=
  match Hp with 
  | ?A && ?B => find_lift x A
  | ?A && ?B => find_lift x B
  | ?A ** ?B => find_lift x A
  | ?A ** ?B => find_lift x B
  | ?P => match P with 
          | x => sepcon_lift' P 
          end
  end. 

Ltac pure_find_lift x Hp :=
  match Hp with 
  | ?A ** ?B => pure_find_lift x A
  | ?A ** ?B => pure_find_lift x B
  | x => idtac
  end. 

Ltac sepcon_lift p :=
  match goal with 
  | |- ?P |-- ?Q => find_lift p P
  | |- _ => idtac end;
  match goal with 
  | |- ?P |-- ?Q => find_lift p Q 
  | |- _ => idtac 
  end.

Ltac derivable1_refl_tac := apply (derivable1_refl _).

Ltac sepcon_cancel' P := 
   match P with 
  | ?x ** ?P' => match goal with 
                 | |- x ** P' |-- x ** _ => eapply derivable1_sepcon_mono ; [derivable1_refl_tac | ];sepcon_cancel' P'
                 | |- _ |-- ?Q => pure_find_lift x Q ;
                sepcon_lift x; eapply derivable1_sepcon_mono ; [derivable1_refl_tac | ];
                sepcon_cancel' P'
                end
  | ?x ** ?P' => sepcon_cancel' P'
  | ?x => sepcon_lift x;
          match goal with
            | |- x |-- x => derivable1_refl_tac
            | |- x ** ?P |-- x ** _  => eapply derivable1_sepcon_mono ; [derivable1_refl_tac | ]
            | |- x |-- x ** _ => eapply sepcon_cancel_res_emp 
          end 
  | _ => idtac
   end.

Ltac sepcon_cancel := 
  match goal with 
  | |- ?x |-- ?x => derivable1_refl_tac
  | |- ?x ** _ |-- ?x ** _ => eapply derivable1_sepcon_mono ; [derivable1_refl_tac | ];sepcon_cancel 
  | |- ?P |-- EX _ , _ => idtac 
  | |- ?P |-- _ => sepcon_cancel' P 
  end.

Ltac get_head t :=
  match constr:(t) with
  | ?A  ?B => get_head A
  | ?A => A
  end.

Ltac unfold_term t :=
  let o := get_head t in
  pattern t;
  match goal with [ |- ?a ?b] => 
    let b := (eval unfold o in b) in change (a b) end;
  simpl. 

Ltac poly_store_unfold :=
  match goal with 
    | |- context [@poly_store FET_int] => unfold_term (@poly_store FET_int)
    | |- context [@poly_store FET_char] => unfold_term (@poly_store FET_char)
    | |- context [@poly_store FET_int64] => unfold_term (@poly_store FET_int64)
    | |- context [@poly_store FET_short] => unfold_term (@poly_store FET_short)
    | |- context [@poly_store FET_uint] => unfold_term (@poly_store FET_uint)
    | |- context [@poly_store FET_uchar] => unfold_term (@poly_store FET_uchar)
    | |- context [@poly_store FET_uint64] => unfold_term (@poly_store FET_uint64)
    | |- context [@poly_store FET_ushort] => unfold_term (@poly_store FET_ushort)
    | |- context [@poly_store FET_ptr] => unfold_term (@poly_store FET_ptr)
    | |- context [@poly_undef_store FET_int] => unfold_term (@poly_undef_store FET_int)
    | |- context [@poly_undef_store FET_char] => unfold_term (@poly_undef_store FET_char)
    | |- context [@poly_undef_store FET_int64] => unfold_term (@poly_undef_store FET_int64)
    | |- context [@poly_undef_store FET_short] => unfold_term (@poly_undef_store FET_short)
    | |- context [@poly_undef_store FET_uint] => unfold_term (@poly_undef_store FET_uint)
    | |- context [@poly_undef_store FET_uchar] => unfold_term (@poly_undef_store FET_uchar)
    | |- context [@poly_undef_store FET_uint64] => unfold_term (@poly_undef_store FET_uint64)
    | |- context [@poly_undef_store FET_ushort] => unfold_term (@poly_undef_store FET_ushort)
    | |- context [@poly_undef_store FET_ptr] => unfold_term (@poly_undef_store FET_ptr)
    | |- _ => idtac
    end.

Ltac TT_simpl := repeat rewrite truep_andp_left_equiv; repeat rewrite truep_andp_right_equiv.

Ltac andp_assoc_change := 
  repeat progress match goal with 
  | |- context [ (?P && ?Q) && ?R ] => rewrite (logic_equiv_andp_assoc P Q R)
  end.

Ltac sepcon_assoc_change :=
  repeat progress match goal with 
    | |- context [ ?P ** ?Q ** ?R ] => rewrite <- (logic_equiv_sepcon_assoc P Q R)
  end.

Ltac coq_prop_lift :=
  repeat progress match goal with 
  | |- context [ ([| ?P |] && ?Q) ** ?R ] => rewrite (logic_equiv_coq_prop_andp_sepcon P Q R)
  | |- context [ ?P ** ([| ?Q |] && ?R) ] => rewrite (logic_equiv_sepcon_coq_prop_andp P Q R)
  | |- context [ ?P ** [| ?Q |] ] => rewrite (sepcon_prop_equiv P Q)
  end.

Ltac asrt_easysimpl := TT_simpl; andp_assoc_change; coq_prop_lift.

Ltac andp_lift'' p :=
  match goal with 
  | |- ?P |-- ?Q  => match Q with 
                    | context [?x && p] => rewrite (logic_equiv_andp_comm x p) 
                    | context [?x && (p && ?y) ] => rewrite (logic_equiv_andp_swap x p y) 
                    | context [?x && p ** ?q ] => rewrite (logic_equiv_andp_comm x (p ** q)) 
                    | context [?x && (p ** ?q  && ?y) ] => rewrite (logic_equiv_andp_swap x (p ** q) y) 
                    end
  | |- ?P |-- ?Q  => match P with 
                    | context [?x && p] => rewrite (logic_equiv_andp_comm x p) 
                    | context [?x && (p && ?y) ] => rewrite (logic_equiv_andp_swap x p y) 
                    | context [?x && p ** ?q ] => rewrite (logic_equiv_andp_comm x (p ** q)) 
                    | context [?x && (p ** ?q  && ?y) ] => rewrite (logic_equiv_andp_swap x (p ** q) y) 
                    end
  end.

Ltac andp_lift' p := andp_lift'' p ;
  repeat progress (andp_lift'' p).
  
Ltac andp_lift p := asrt_easysimpl; try (sepcon_lift p);
match goal with 
  | |- ?P |-- ?Q => andp_lift' p
end.

Ltac asrt_complex_simpl :=
  repeat progress match goal with 
    | |- context [ (_ ** _ ) && ?P ] => andp_lift P
    | |- context [ ?P ** emp ] => rewrite (sepcon_emp_equiv P)
    | |- context [ emp ** ?P ] => rewrite (logic_equiv_sepcon_comm emp P); rewrite (sepcon_emp_equiv P)
    | |- context [( [| ?B |] && ?Q) && ?R] => rewrite (logic_equiv_andp_assoc ([| B |]) Q R )
    | |- context [( [| ?B |] && ?Q) ** ?R] => rewrite (logic_equiv_coq_prop_andp_sepcon B Q R )
    | |- context [( ?P && [| ?B |]) && ?R] => 
      rewrite (logic_equiv_andp_comm P ([| B |])) ;
      rewrite (logic_equiv_andp_assoc ([| B |]) P R)
    | |- context [( ?P && [| ?B |]) ** ?R] =>
      rewrite (logic_equiv_andp_comm P ([| B |])) ; 
      rewrite (logic_equiv_coq_prop_andp_sepcon B P R )
    | |- context [?P ** ([| ?B |] && ?R)] => rewrite (logic_equiv_sepcon_coq_prop_andp P B R)
    | |- context [?P ** ([| ?B |]) ] => rewrite (sepcon_prop_equiv P B)
    | |- context [([| ?B |]) ** ?P ] => rewrite (logic_equiv_sepcon_comm ([| B |]) P)
    | |- context [ (@exp ?t ?P) && ?Q ] => rewrite (ex_logic_equiv_andp _ Q)
    | |- context [ (@exp ?t ?P) ** ?Q ] => rewrite (ex_logic_equiv_sepcon _ Q)
    | |- context [ @exp ?t ?P ] => try andp_lift (@exp t P) ; try sepcon_lift (@exp t P)
    | |- context [ (?P || ?Q) ** ?R ] => rewrite (orp_sepcon_left P Q R)
    | |- context [ ?P ** (?Q || ?R) ] => rewrite (orp_sepcon_right P Q R)
    end.

Ltac asrt_simpl_pure := asrt_easysimpl; asrt_complex_simpl.

Ltac asrt_simpl := try poly_store_unfold ; Rename asrt_simpl_pure.

Ltac andp_cancel' P := 
  match P with 
  | ?x && ?P' => andp_lift x;eapply derivable1_andp_mono ; [derivable1_refl_tac | ];
                andp_cancel' P'
  | ?x && ?P' => andp_cancel' P'
  | ?x => apply (derivable1_refl x) ||  eapply (derivable1_andp_elim1 x) ||  (eapply (derivable1_andp_elim2 _ x)) || sepcon_cancel
  end.

Ltac andp_cancel'' :=
  match goal with 
  | |- ?x |-- ?x => derivable1_refl_tac 
  | |- ?x && _ |-- ?x && _ => eapply derivable1_andp_mono ; [derivable1_refl_tac | ];andp_cancel''
  | |- _ |-- ?P => andp_cancel' P
  end.

Ltac solve_auto B := 
  solve [try subst B ; auto] || idtac.

Ltac andp_cancel := asrt_simpl_pure;
    match goal with 
   | |- ?P |-- ?Q || ?R => idtac 
   | |- ?P || ?Q |-- ?R => idtac
   | |- ?P |-- ?Q =>  match P with 
                      | context [ [| ?B |]] => try andp_lift ( [| B |]); eapply coq_prop_andp_left; intros; andp_cancel
                      end
   | |- ?P |-- ?Q  => match Q with 
                      | context [ [| ?B |]] => try andp_lift ( [| B |]); simple eapply (coq_prop_andp_right);[  andp_cancel | solve_auto B ]
                      end
   | |- [| ?P |] |-- [| ?Q |] => apply coq_prop_imply ; solve_auto Q
   | |- _ |-- [| ?Q |] => apply (derivable1s_coq_prop_r Q); solve_auto Q
   | |- [| ?P |] |-- ?Q => eapply derivable1s_coq_prop_l; intros; andp_cancel
   | |- _ |-- TT => apply derivable1_truep_intros ; auto
   | |- _ => andp_cancel''
    end.

Ltac pureIntros_without_rename := asrt_simpl_pure;
repeat progress (match goal with 
| |- ?P |-- ?Q => (match P with 
                    | context [ [| ?B |]] => apply (coq_prop_andp_left B); intros
                  end)
end) ; sepcon_assoc_change .

Ltac pureIntros := try poly_store_unfold ; Rename pureIntros_without_rename.

Ltac left_intro v:=
  asrt_simpl;
  eapply derivable1s_exp_l;
  intro v.

Ltac left_intro_any:=
  asrt_simpl;
  eapply derivable1s_exp_l;
  intros .

Ltac right_intro v:=
  asrt_simpl;
  eapply derivable1s_allp_r;
  intro v.

Ltac right_intro_any:=
  asrt_simpl;
  eapply derivable1s_allp_r;
  intros.

Ltac reexists :=
  match goal with 
    | |- ?P |-- (@exp ?T ?Q) => eapply exp_exp_right
    | _ => eapply exp_exp_right
  end.

Ltac rexists v:=
  match goal with 
    | |- ?P |-- (@exp ?T ?Q) => refine (@derivable1s_exp_r T _ _ v _)
    | _ => refine (derivable1s_exp_r _ _ v _)
  end.

Ltac lexists v :=
  match goal with 
  | |- exists _, _ => exists v
  | |- @allp ?T ?P |-- _ => refine (@derivable1s_allp_l T _ _ v _)
  | _ => refine (derivable1s_allp_l _ _ v _) 
  end.
  

Ltac simpl_auto := 
  solve [auto | lia | nia | int_auto].

Ltac simpl_entail := match goal with
  | |- ?Q /\ ?R => split;[simpl_entail| simpl_entail]
  | |-  _ =>  simpl_auto || idtac  end.

Ltac entailer_pure := asrt_simpl_pure; sepcon_assoc_change; andp_cancel.

Tactic Notation "cancel" := Rename sepcon_cancel.
Tactic Notation "entailer!"  := try poly_store_unfold ; Rename entailer_pure; simpl_entail.
Tactic Notation "Intros" := pureIntros. 
Tactic Notation "Intro_any" := pureIntros ; left_intro_any ; pureIntros.
Tactic Notation "Intros" simple_intropattern(x0):= pureIntros ;  left_intro x0;pureIntros.
Tactic Notation "Intros" simple_intropattern(x0) simple_intropattern(x1) := pureIntros ; left_intro x0; left_intro x1;pureIntros.
Tactic Notation "Intros" simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) := pureIntros ; left_intro x0; left_intro x1; left_intro x2;pureIntros.
Tactic Notation "Intros" simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) := pureIntros ; left_intro x0; left_intro x1; left_intro x2; left_intro x3;pureIntros.
Tactic Notation "Intros" simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) := pureIntros ; left_intro x0; left_intro x1; left_intro x2; left_intro x3; left_intro x4;pureIntros.
Tactic Notation "Intros_r_any" := right_intro_any; pureIntros.
Tactic Notation "Intros_r" simple_intropattern(x0):= right_intro x0;pureIntros.
Tactic Notation "Intros_r" simple_intropattern(x0) simple_intropattern(x1) := right_intro x0; right_intro x1;pureIntros.
Tactic Notation "Intros_r" simple_intropattern(x0) simple_intropattern(x1)
                          simple_intropattern(x2) simple_intropattern(x3)
                          simple_intropattern(x4) simple_intropattern(x5)
                          simple_intropattern(x6) simple_intropattern(x7)
                          simple_intropattern(x8) := 
  right_intro x0; right_intro x1;right_intro x2; right_intro x3;right_intro x4; right_intro x5;
  right_intro x6; right_intro x7;right_intro x8; pureIntros.

Tactic Notation "eExists" := asrt_simpl; reexists ; eexists.  
Tactic Notation "Exists" uconstr(x0) := asrt_simpl;rexists x0.
Tactic Notation "Exists" uconstr(x0) uconstr(x1) := asrt_simpl;rexists x0;asrt_simpl;rexists x1.
Tactic Notation "Exists" uconstr(x0) uconstr(x1) uconstr(x2) := asrt_simpl;rexists x0;asrt_simpl;rexists x1;asrt_simpl;rexists x2.
Tactic Notation "Exists" uconstr(x0) uconstr(x1) uconstr(x2) uconstr(x3) := asrt_simpl;rexists x0;asrt_simpl;rexists x1;asrt_simpl;rexists x2;asrt_simpl;rexists x3.
Tactic Notation "Exists" uconstr(x0) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) := asrt_simpl;rexists x0;asrt_simpl;rexists x1;asrt_simpl;rexists x2;asrt_simpl;rexists x3;asrt_simpl;rexists x4.

Tactic Notation "Exists_l" uconstr(x0) := asrt_simpl;lexists x0.
Tactic Notation "Exists_l" uconstr(x0) uconstr(x1) := asrt_simpl;lexists x0;asrt_simpl;lexists x1.
Tactic Notation "Exists_l" uconstr(x0) uconstr(x1) uconstr(x2) := asrt_simpl;lexists x0;asrt_simpl;lexists x1;asrt_simpl;lexists x2.
Tactic Notation "Exists_l" uconstr(x0) uconstr(x1) uconstr(x2) uconstr(x3) := asrt_simpl;lexists x0;asrt_simpl;lexists x1;asrt_simpl;lexists x2;asrt_simpl;lexists x3.
Tactic Notation "Exists_l" uconstr(x0) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) := asrt_simpl;lexists x0;asrt_simpl;lexists x1;asrt_simpl;lexists x2;asrt_simpl;lexists x3;asrt_simpl;lexists x4.

Tactic Notation "normalize"  := asrt_simpl.

Tactic Notation "Left" := rewrite <- derivable1_orp_intros1.
Tactic Notation "Right" := rewrite <- derivable1_orp_intros2.
Tactic Notation "Split" := apply derivable1_orp_elim.

Notation "'Assertion'" := (expr) (at level 1).

Ltac L_sepcon_lift'' p :=
  match goal with 
  | |- ?P |-- ?Q  => match P with 
                    | context [?x ** p] => rewrite (logic_equiv_sepcon_comm x p) 
                    | context [?x ** (p ** ?y) ] => rewrite (logic_equiv_sepcon_swap x p y) 
                    end
  end.

Ltac L_sepcon_lift' p := L_sepcon_lift'' p ;
  repeat progress (L_sepcon_lift'' p).

Ltac sep_lift_L_aux L :=
  match L with 
  | nil => idtac 
  | cons ?p ?l' => try (L_sepcon_lift' p); sep_lift_L_aux l'
  end.

Ltac sep_lift_L L :=
  let revl := eval cbn [List.rev List.app] in (List.rev L) in sep_lift_L_aux revl.

Ltac sep_apply_L L h:=
  let n := eval compute in (List.length L) in 
  match n with 
  | O => fail "nil list"
  | _ => asrt_simpl; sep_lift_L L; try rewrite !derivable1_sepcon_assoc1; rewrite h
  end.

Ltac prop_rewrite h:= rewrite (prop_add_left _ _ h) at 1.

Ltac prop_apply_L L h:=
  let n := eval compute in (List.length L) in 
  match n with 
  | O => fail "nil list"
  | _ => asrt_simpl; sep_lift_L L; try rewrite !derivable1_sepcon_assoc1; prop_rewrite h
  end.

Ltac unify_asrt x Q :=
  match Q with 
  | ?A ** ?B => (unify_asrt x A)
  | ?A ** ?B => unify_asrt x B
  | ?y => unify x y
  end.

Ltac unify_asrts P Q :=
  match P with 
  | ?A ** ?B => (unify_asrts A Q); (unify_asrts B Q)
  | ?x => unify_asrt x Q 
  end.


Ltac unify_prewithgoal  P :=
  match goal with 
  | |- ?Q  |-- _ => unify_asrts P Q 
  end.

Ltac  sepconlistasrts_rec P L :=
  match P with 
  | ?A ** ?B => let L1  :=  (sepconlistasrts_rec A (@nil expr)) in 
                let L2 :=  (sepconlistasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?x => constr:(cons x L)
  end.

Ltac sepconlistasrts P :=
  let l:= (sepconlistasrts_rec P (@nil expr)) in 
  constr:(l).

Ltac sep_apply H :=
  (let h:= fresh "Hlemma" in pose proof H as h;
  let rec find_lemmapre_rec h :=
   (lazymatch type of h with
  | forall x:?T, _ => lazymatch type of T with
                      | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                      | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                              find_lemmapre_rec h
                      end
  | ?T -> _ => lazymatch type of T with
                | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                      find_lemmapre_rec h
                end
  | ?P |-- ?Q => unify_prewithgoal P;
                  match type of h with 
                  | ?P |-- _ =>  let L:= (sepconlistasrts P) in sep_apply_L L h;clear  h
                  end
  | ?P --||-- ?Q => find_lemmapre_rec (P |-- Q)
  end) in find_lemmapre_rec h) ; sepcon_assoc_change.

Ltac prop_apply H :=
  (let h:= fresh "Hlemma" in pose proof H as h;
  try repeat rewrite <- logic_equiv_coq_prop_and in h;
  let rec find_lemmapre_rec h :=
   (lazymatch type of h with
  | forall x:?T, _ => lazymatch type of T with
                      | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                      | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                              find_lemmapre_rec h
                      end
  | ?T -> _ => lazymatch type of T with
                | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                      find_lemmapre_rec h
                end
  | ?P |-- [| ?Q |] => unify_prewithgoal P;
                  match type of h with 
                  | ?P |-- _ =>  let L:= (sepconlistasrts P) in prop_apply_L L h;clear  h
                  end
  end) in find_lemmapre_rec h) ; sepcon_assoc_change.
    
Ltac Unfold :=
match goal with
  | |- ?P => try unfold P
end.

Ltac Intros_R'' :=
match goal with
  | |- _ |-- ALL p _ , _ => Intros_r p
end.

Ltac Intros_R' :=
match goal with
  | |- _ |-- ALL p , _ => Intros_r p
end.

Ltac Intros_R :=
try (repeat progress Intros_R''); try Intros_R'.

Ltac apply_sepcon_adjoint :=
match goal with
  | |- ?P |-- ?Q -* ?R => destruct (derivable1s_wand_sepcon_adjoint P Q R) as [H_wand_currying H_wand_decurrying];
                          apply H_wand_currying; clear H_wand_currying H_wand_decurrying
end.

Lemma sepcon_emp_logic_equiv' : forall x : Assertion, emp ** x --||-- x.
intros. split ; entailer!.
Qed.

Ltac elim_emp :=
repeat progress (try (rewrite sepcon_emp_equiv || rewrite sepcon_emp_logic_equiv')).

Lemma elim_wand_emp_emp : emp --||-- emp -* emp.
Proof.
  split.
  - apply derivable1s_wand_sepcon_adjoint. elim_emp. apply derivable1_refl.
  - rewrite <- logic_equiv_sepcon_emp.
    apply derivable1_wand_elim1.
Qed.

Ltac wand_elim := 
  repeat progress (
    try rewrite <- elim_wand_emp_emp;
    elim_emp;
    try apply_sepcon_adjoint;
    try Intros_R
  ).

Ltac pre_process_pure :=
  pureIntros_without_rename ;
  wand_elim;
  asrt_simpl_pure.

Ltac pre_process :=
  try Unfold;
  intros; poly_store_unfold;
  Rename pre_process_pure ; 
  try (solve [entailer!]).

Tactic Notation "pre_process_default" := pre_process.
  
End DerivedPredSig.
