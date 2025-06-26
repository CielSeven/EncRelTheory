Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.

From SetsClass Require Import SetsClass.
From AUXLib Require Import Axioms Feq Idents  List_lemma int_auto VMap ListLib.
From compcert.lib Require Import Integers.

From EncRelSeq Require Import  callsem basicasrt contexthoare_imp.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ImpTactics ImpHoareTactics ImpEHoareTactics.



Section arrayrules.

Import ImpRules.
Context (pm : Perm.t).

Local Open Scope asrt_scope.

Fixpoint store_array_rec {A : Type} (storeA : addr -> Z -> A -> assertion) (x: addr ) (lo hi: Z) (l: list A): assertion :=
  match l with
  | nil     => !! (lo = hi ) && !! (l = nil ) && emp
  | a :: l0 => storeA x lo a ** store_array_rec storeA x (lo + 1) hi l0
  end.

Fixpoint store_array_missing_i_rec {A : Type} (storeA : addr -> Z -> A -> assertion) (x: addr) (i lo hi: Z) (l: list A): assertion :=
  match l with
  | nil     => !! (False)
  | a :: l0 => !! (i = lo ) && store_array_rec storeA x (lo + 1) hi l0 ||
               !! (i > lo ) && storeA x lo a ** store_array_missing_i_rec storeA x i (lo + 1) hi l0
  end.

Definition store_array {A : Type} (storeA : addr -> Z -> A -> assertion) (x: addr) (n: Z) (l: list A): assertion :=
  store_array_rec storeA x 0 n l.

Lemma store_array_rec_length: forall {A : Type} storeA x lo hi (l : list A),
  store_array_rec storeA x lo hi l |-- !! (Z.of_nat (length l) = hi - lo).
Proof.
  intros.
  revert lo; induction l; simpl store_array_rec ; intros.
  + quick_entailer!.
  + sep_apply IHl.
    quick_entailer!.
Qed.

Lemma store_array_length: forall {A : Type} storeA x n (l : list A),
  store_array storeA x n l |-- !! (Z.of_nat (length l) = n).
Proof.
  intros.
  unfold store_array.
  sep_apply (store_array_rec_length storeA).
  quick_entailer!. 
Qed.

Lemma store_array_Zlength: forall {A : Type} storeA x n (l : list A),
  store_array storeA x n l |-- !! (Zlength l = n ).
Proof.
  intros. rewrite Zlength_correct.
  apply store_array_length.
Qed.

Lemma store_array_split: forall {A : Type} storeA x n m (l : list A) a,
  0 <= n < m ->
  store_array storeA x m l |-- storeA x n (Znth n l a) ** store_array_missing_i_rec storeA x n 0 m l.
Proof.
  intros.
  revert H.
  unfold store_array.
  replace n with (n - 0) at 4 by lia.
  set (lo := 0); clearbody lo; rename m into hi.
  revert lo; induction l; intros; simpl; intros.
  + quick_entailer!.
  + pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
    - rewrite <- derivable1_orp_intros2.
      sep_apply IHl; [ | lia ].
      rewrite Znth_cons by lia.
      replace (n - (lo + 1)) with (n - lo - 1) by lia.
      quick_entailer!.
    - rewrite <- derivable1_orp_intros1.
      subst n.
      replace (lo - lo) with 0 by lia.
      quick_entailer!.
Qed.

Lemma store_array_missing_i_rec_replace: forall {A : Type} storeA x n m (l : list A) a,
  0 <= n < m ->
  store_array_missing_i_rec storeA x n 0 m l |-- store_array_missing_i_rec storeA x n 0 m (replace_Znth n a l).
Proof.
  intros.
  revert H.
  assert ( (replace_Znth n a l) = replace_Znth (n - 0) a l). { replace n with (n - 0) at 1 by lia. reflexivity. }
  rewrite H. clear H.
  set (lo := 0).
  assert (0 <= lo) by lia.
  clearbody lo; rename m into hi.
  revert lo n hi H; induction l; intros; simpl; intros.
  + quick_entailer!.
  + pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
    - rewrite replace_Znth_cons by lia.
      apply derivable1_orp_elim;unfoldimpmodel.
      quick_entailer!.
      sep_apply (IHl (lo + 1) (n) hi); [ | lia | lia ].
      simpl.
      rewrite <- derivable1_orp_intros2.
      replace (n - (lo + 1)) with (n - lo - 1) by lia.
      quick_entailer!.
    - apply derivable1_orp_elim;unfoldimpmodel.
      2: quick_entailer!.
      subst n.
      replace (lo - lo) with 0 by lia.
      simpl.
      rewrite <- derivable1_orp_intros1.
      quick_entailer!.
Qed.

Lemma store_array_merge: forall {A : Type} storeA x n m a (l: list A),
  0 <= n < m -> 
  storeA x n a ** store_array_missing_i_rec storeA x n 0 m l |-- store_array storeA x m (replace_Znth n a l).
Proof.
  intros.
  unfold store_array.
  replace n with (n - 0) at 3 by lia.
  revert H.
  set (lo := 0); clearbody lo.
  revert lo; induction l; intros; simpl.
  + quick_entailer!.
  + rewrite derivable1_sepcon_comm.
    apply derivable1_wand_sepcon_adjoint.
    apply derivable1_orp_elim;
    apply derivable1_wand_sepcon_adjoint.
    - unfoldimpmodel.
      Intros.
      subst n.
      replace (lo - lo) with 0 by lia.
      simpl.
      quick_entailer!.
    - unfoldimpmodel.
      Intros.
      sep_apply IHl; [ | lia ].
      quick_entailer!.
      rewrite replace_Znth_cons by lia.
      replace (n - (lo + 1)) with (n - lo - 1) by lia.
      simpl.
      quick_entailer!.
Qed.

Lemma store_array_rec_base {A: Type}:
  forall x m k n l (storeA: addr -> A -> assertion) f, 
    0 <= m -> 0 <= m + k -> 
    f = (fun (x0 : addr) (lo: Z) (a0: A) => storeA (x0 + lo) a0) ->
    store_array_rec f x (m+k) n l --||--
    store_array_rec f (x + k) m (n-k) l.
Proof.
  intros * Hm Hk; intros; revert m k n Hm Hk; induction l; intros.
  - simpl. apply logic_equiv_derivable1. 
    split;  
    quick_entailer!.
  - rewrite H; simpl.
    apply logic_equiv_derivable1;unfoldimpmodel. 
    split.
    + prop_apply (@store_array_rec_length A).
      Intros. 
      assert (((x + k) + m ) =   (x + ((m + k)))) by lia.
      rewrite H1. 
      rewrite <- H.
      replace (m+k+1) with (m+1+k) by lia.
      rewrite IHl; quick_entailer!.
    + prop_apply (@store_array_rec_length A).
      Intros. 
      assert (((x + k) + m ) =   (x + ((m + k)))) by lia.
      rewrite H1. 
      rewrite <- H.
      replace (m+k+1) with (m+1+k) by lia.
      rewrite IHl; quick_entailer!.
Qed.

Lemma store_array_rec_divide {A: Type}:
  forall m n l x  (storeA: addr -> A -> assertion) f,
    0 <= m <= n -> Zlength l = n ->
    f = (fun (x0 : addr) (lo: Z) (a0: A) => storeA (x0 + lo) a0) ->
    store_array_rec f x 0 n l --||--
    store_array_rec f x 0 m (sublist 0 m l) ** store_array_rec f x m n (sublist m n l).
Proof.
  intros * H Hl H0.
  revert x m n H Hl.
  induction l; intros.
  - rewrite H0; repeat rewrite sublist_of_nil.
    eapply logic_equiv_derivable1.
    simpl; split; quick_entailer!.
  - rewrite H0; unfold store_array.
    destruct (Z_lt_ge_dec m 1).
    + assert (m = 0) by lia; subst m.
      rewrite sublist_nil by lia.
      rewrite sublist_self by easy.
      eapply logic_equiv_derivable1.
      simpl; split; quick_entailer!.
    + rewrite sublist_cons1 by lia.
      simpl.
      replace 1 with (0+1) at 1 by lia.
      rewrite store_array_rec_base by (lia || auto).
      rewrite H0 in IHl; unfold store_array.
      rewrite sublist_cons2 by lia.
      unfold store_array in IHl.
      pose proof Hl as Hl2.
      change (a::l) with ((a::nil)++l) in Hl2.
      rewrite Zlength_app in Hl2; replace (Zlength (a::nil)) with 1 in Hl2 by easy.
      rewrite (IHl (x + 1) (m-1)); try lia.
      replace 0 with (1 + (-1)) at 2 by lia.
      replace (m -1) with (m + (-1)) at 3 by lia.
      repeat rewrite store_array_rec_base by (lia || auto).
      replace  ((x + 1) + (-1)) with x. 
      replace (m - 1 - -1) with m by lia.
      replace (n -1 - -1) with n by lia.
      eapply logic_equiv_derivable1.
      unfoldimpmodel;split; quick_entailer!.
      lia.
Qed.

Lemma store_array_divide {A: Type}:
  forall x n l m (storeA: addr -> A -> assertion) f g,
    0 <= m <= n -> Zlength l = n ->
    f = (fun (x0 : addr) (lo: Z) (a0: A) => storeA (x0 + lo) a0) ->
    g = store_array f ->
    g x n l --||-- 
    g x m (sublist 0 m l) ** g (x + m) (n-m) (sublist m n l).
Proof.
  intros; rewrite H2; unfold store_array.
  rewrite store_array_rec_divide; eauto.
  unfold store_array; eapply logic_equiv_derivable1.
  unfoldimpmodel; split; quick_entailer!.
  - replace m with (0+m) at 1 by lia.
    rewrite store_array_rec_base by (lia || eauto).
    reflexivity.
  - replace m with (0+m) at 4 by lia.
    rewrite store_array_rec_base by (lia || eauto).
    reflexivity.
Qed.
End arrayrules.


Section intarrayrules.

Import ImpRules.
Context (pm : Perm.t).

Local Open Scope asrt_scope.

Definition store_offset_int64  : addr -> Z -> Z -> assertion :=
  fun x lo a =>  !! (a <= Int64.max_signed /\ a >= Int64.min_signed) && 
                (vPV (x + lo) @ vint ↦ₗ a $ pm).

Definition store_int_array_rec (x: addr) (lo hi: Z) (l: list Z): assertion :=
  store_array_rec store_offset_int64 x lo hi l. 

Definition store_int_array_missing_i_rec  (x: addr) (i lo hi: Z) (l: list Z): assertion := 
  store_array_missing_i_rec store_offset_int64 x i lo hi l.

Definition store_int_array (x: addr) (n: Z) (l: list Z): assertion :=
  store_array store_offset_int64 x n l.


Lemma store_int_array_rec_length: forall x lo hi l,
  store_int_array_rec x lo hi l |-- !! (Z.of_nat (length l) = hi - lo).
Proof.
  intros.
  unfold store_int_array_rec.
  sep_apply (store_array_rec_length store_offset_int64). quick_entailer!.
Qed.

Lemma store_int_array_length: forall x n l,
  store_int_array x n l |-- !! (Z.of_nat (length l) = n ).
Proof.
  intros.
  unfold store_int_array.
  sep_apply store_int_array_rec_length.
  quick_entailer!. 
Qed.

Lemma store_int_array_Zlength: forall x n l,
  store_int_array x n l |-- !! (Zlength l = n).
Proof.
  intros; unfold store_int_array.
  apply store_array_Zlength.
Qed.

Lemma store_int_array_split: forall x n m l,
  0 <= n < m ->
  store_int_array x m l |-- store_offset_int64 x n (Znth n l 0) ** store_int_array_missing_i_rec x n 0 m l.
Proof.
  intros.
  unfold store_int_array, store_int_array_missing_i_rec.
  sep_apply (store_array_split store_offset_int64). quick_entailer!.
  lia.
Qed.

Lemma store_int_array_merge: forall x n m a l,
  0 <= n < m ->
  store_offset_int64 x n a ** store_int_array_missing_i_rec x n 0 m l |-- store_int_array x m (replace_Znth n a l).
Proof.
  intros.
  unfold store_int_array, store_int_array_missing_i_rec.
  sep_apply (store_array_merge store_offset_int64). quick_entailer!.
  lia.
Qed.

Lemma store_int_array_splitmerge: forall x n m l,
  0 <= n < m ->
  store_int_array x m l --||-- store_offset_int64 x n (Znth n l 0) ** store_int_array_missing_i_rec x n 0 m l.
Proof.
  intros.
  apply logic_equiv_derivable1.
  split;
  unfoldimpmodel.
  apply store_array_split;auto.
  erewrite store_int_array_merge;auto.
  rewrite replace_Znth_Znth.
  reflexivity.
Qed.

Definition store_int64  : addr -> Z ->  assertion :=
  fun x  a =>  !! (a <= Int64.max_signed /\ a >= Int64.min_signed) && 
                (vPV x @ vint ↦ₗ a $ pm).

Lemma store_int_array_divide:
  forall x n l m,
    0 <= m <= n -> Zlength l = n -> 
    store_int_array x n l --||-- 
    store_int_array x m (sublist 0 m l) ** store_int_array (x + m) (n-m) (sublist m n l).
Proof.
  intros; unfold store_int_array. 
  eapply store_array_divide with (storeA := store_int64); eauto.
  auto.
Qed.


End intarrayrules.


Section  chararrayrules.

Import ImpRules.
Context (pm : Perm.t).

Local Open Scope asrt_scope.


Definition store_offset_char  : addr -> Z -> Z -> assertion :=
  fun x lo a =>  !! (a <= Byte.max_signed /\ a >= Byte.min_signed) && 
                (vPV (x + lo) @ vint ↦ₗ a $ pm).

Definition store_char_array_rec (x: addr) (lo hi: Z) (l: list Z): assertion :=
  store_array_rec store_offset_char x lo hi l. 

Lemma store_char_array_rec_length: forall x lo hi l,
  store_char_array_rec x lo hi l |-- !! (Z.of_nat (length l) = hi - lo ).
Proof.
  intros.
  unfold store_char_array_rec.
  sep_apply (store_array_rec_length store_offset_char). quick_entailer!.
Qed.

Definition store_char_array_missing_i_rec (x: addr) (i lo hi: Z) (l: list Z): assertion := 
  store_array_missing_i_rec store_offset_char x i lo hi l.

Definition store_char_array (x: addr) (n: Z) (l: list Z): assertion :=
  store_array store_offset_char x n l.

Lemma store_char_array_length: forall x n l,
  store_char_array x n l |-- !! (Z.of_nat (length l) = n).
Proof.
  intros.
  unfold store_char_array.
  sep_apply store_char_array_rec_length.
  quick_entailer!. 
Qed.

Lemma store_char_array_Zlength: forall x n l,
  store_char_array x n l |-- !! (Zlength l = n).
Proof.
  intros; unfold store_char_array.
  apply store_array_Zlength.
Qed.

Lemma store_char_array_split: forall x n m l,
  0 <= n < m ->
  store_char_array x m l |-- !! ((Znth n l 0) <= Byte.max_signed /\ (Znth n l 0) >= Byte.min_signed) && 
                (vPV (x + n) @ vint ↦ₗ (Znth n l 0) $ pm) ** store_char_array_missing_i_rec x n 0 m l.
Proof.
  intros.
  unfold store_char_array, store_char_array_missing_i_rec.
  sep_apply (store_array_split (fun x lo a => !! (a <= Byte.max_signed /\ a >= Byte.min_signed) && 
  (vPV (x + lo) @ vint ↦ₗ a $ pm))). quick_entailer!.
  lia.
Qed.

Lemma store_char_array_merge: forall x n m a l,
  0 <= n < m ->
  (a <= Byte.max_signed /\ a >= Byte.min_signed) -> 
  isvalidptr (x + n) ->
  (PV (x + n) @ vint ↦ₗ a $ pm) ** store_char_array_missing_i_rec x n 0 m l |-- store_char_array x m (replace_Znth n a l).
Proof.
  intros.
  unfold store_char_array, store_char_array_missing_i_rec.
  eapply derivable1_trans.
  2: eapply (store_array_merge (fun x lo a => !! (a <= Byte.max_signed /\ a >= Byte.min_signed) && 
  (vPV (x + lo) @ vint ↦ₗ a $ pm))).
  2: lia.
  unfoldimpmodel. quick_entailer!.
Qed.

  
End  chararrayrules.

Import ImpRules.
Local Open Scope asrt_scope.
Section  arraysubstrules.


Context {A: Type}.
Context (pm : Perm.t).
Context (storeA : (addr -> Z -> A -> assertion)).
Context (HstoreA_Local:  (forall x n start i a, subst_local x n (storeA start i a) --||--  storeA start i a) ).
Context (HstoreA_Global:  (forall x n start i a, subst_global x n (storeA start i a) --||--  storeA start i a) ).

Lemma subst_local_store_array_rec: forall (l : list A)  start lo hi x n,
   subst_local x n (store_array_rec storeA start lo hi l) --||-- store_array_rec storeA start lo hi l.
Proof.
  induction l;intros.
  - simpl.
    rewrite ! subst_local_and.
    rewrite ! subst_local_pure.
    rewrite subst_local_emp.
    apply logic_equiv_refl.
  - simpl.
    erewrite ! subst_local_sepcon.
    erewrite HstoreA_Local.
    rewrite IHl by eauto.
    reflexivity.
Qed.

Lemma subst_local_store_array_missing_i_rec: forall (l : list A) start i lo hi x n,
  subst_local x n (store_array_missing_i_rec storeA start i lo hi l) --||-- store_array_missing_i_rec storeA start i lo hi l.
Proof.
  induction l;intros.
  - simpl.
    rewrite ! subst_local_pure.
    apply logic_equiv_refl.
  - simpl.
    erewrite ! subst_local_or.
    rewrite ! subst_local_and.
    erewrite ! subst_local_sepcon.
    rewrite ! subst_local_pure.
    erewrite ! HstoreA_Local.
    rewrite IHl by eauto.
    rewrite subst_local_store_array_rec.
    reflexivity.
Qed.

Lemma subst_local_store_array: forall (l : list A) start n x v,
  subst_local x v (store_array storeA start n l) --||-- (store_array storeA start n l).
Proof.
  intros.
  unfold store_array.
  erewrite subst_local_store_array_rec.
  reflexivity.
Qed.

Lemma subst_global_store_array_rec: forall (l : list A)  start lo hi x n, 
  subst_global x n (store_array_rec storeA start lo hi l) --||-- store_array_rec storeA start lo hi l.
Proof.
  induction l;intros.
  - simpl.
    rewrite ! subst_global_and.
    rewrite ! subst_global_pure.
    rewrite subst_global_emp.
    reflexivity.
  - simpl.
    erewrite ! subst_global_sepcon.
    erewrite HstoreA_Global.
    rewrite IHl by eauto.
    reflexivity.
Qed.

Lemma subst_global_store_array_missing_i_rec: forall (l : list A) start i lo hi x n,
  subst_global x n (store_array_missing_i_rec storeA start i lo hi l) --||-- store_array_missing_i_rec storeA start i lo hi l.
Proof.
  induction l;intros.
  - simpl.
    rewrite ! subst_global_pure.
    apply logic_equiv_refl.
  - simpl.
    erewrite ! subst_global_or.
    rewrite ! subst_global_and.
    erewrite ! subst_global_sepcon.
    rewrite ! subst_global_pure.
    erewrite ! HstoreA_Global.
    rewrite IHl by eauto.
    rewrite subst_global_store_array_rec.
    reflexivity.
Qed.

Lemma subst_global_store_array: forall (l : list A) start n x v,
  subst_global x v (store_array storeA start n l) --||-- (store_array storeA start n l).
Proof.
  intros.
  unfold store_array.
  erewrite subst_global_store_array_rec.
  reflexivity.
Qed.

End  arraysubstrules.


Section  intarraysubstrules.

Context (pm : Perm.t).

Lemma  subst_local_intstore: forall (x : var) (n:value) (start : addr) (i a : Z),
  subst_local x n (store_offset_int64 pm start i a) --||-- store_offset_int64 pm start i a.
Proof.
  unfold store_offset_int64. intros.
  rewrite ! subst_local_and.
  rewrite ! subst_local_pure.
  rewrite subst_local_pv.
  reflexivity.
Qed.

Lemma subst_local_store_int_array_rec: forall l start lo hi x n,
   subst_local x n (store_int_array_rec pm start lo hi l) --||-- store_int_array_rec pm start lo hi l.
Proof.
  intros.
  unfold store_int_array_rec.
  erewrite subst_local_store_array_rec.
  reflexivity.
  apply subst_local_intstore.
Qed.

Lemma subst_local_store_int_array_missing_i_rec: forall l start i lo hi x n,
  subst_local x n (store_int_array_missing_i_rec pm start i lo hi l) --||-- store_int_array_missing_i_rec pm start i lo hi l.
Proof.
  intros.
  unfold store_int_array_missing_i_rec.
  erewrite subst_local_store_array_missing_i_rec.
  reflexivity.
  apply subst_local_intstore.
Qed.

Lemma subst_local_store_int_array: forall l start n x v,
  subst_local x v (store_int_array pm start n l) --||-- (store_int_array pm start n l).
Proof.
  intros.
  unfold store_int_array.
  erewrite subst_local_store_array.
  reflexivity.
  apply subst_local_intstore.
Qed.

Lemma  subst_global_intstore: forall (x : var) (n:value) (start : addr) (i a : Z),
  subst_global x n (store_offset_int64 pm start i a) --||-- store_offset_int64 pm start i a.
Proof.
  unfold store_offset_int64. intros.
  rewrite ! subst_global_and.
  rewrite ! subst_global_pure.
  rewrite subst_global_pv.
  reflexivity.
Qed.

Lemma subst_global_store_int_array_rec: forall l start lo hi x n,
   subst_global x n (store_int_array_rec pm start lo hi l) --||-- store_int_array_rec pm start lo hi l.
Proof.
  intros.
  unfold store_int_array_rec.
  erewrite subst_global_store_array_rec.
  reflexivity.
  apply subst_global_intstore.
Qed.

Lemma subst_global_store_int_array_missing_i_rec: forall l start i lo hi x n,
  subst_global x n (store_int_array_missing_i_rec pm start i lo hi l) --||-- store_int_array_missing_i_rec pm start i lo hi l.
Proof.
  intros.
  unfold store_int_array_missing_i_rec.
  erewrite subst_global_store_array_missing_i_rec.
  reflexivity.
  apply subst_global_intstore.
Qed.

Lemma subst_global_store_int_array: forall l start n x v,
  subst_global x v (store_int_array pm start n l) --||-- (store_int_array pm start n l).
Proof.
  intros.
  unfold store_int_array.
  erewrite subst_global_store_array.
  reflexivity.
  apply subst_global_intstore.
Qed.


Lemma closedgvars_store_int_array : forall l start n vs,
  closed_wrt_gvars vs (store_int_array pm start n l).
Proof.
  unfold store_int_array, store_array.
  set (lo:= 0). clearbody lo. intros l. revert lo.
  induction l;intros.
  - simpl. 
    solve_closedgvars idtac.
  - simpl.
    unfold store_offset_int64 at 1.
    solve_closedgvars idtac.
    apply IHl.
Qed.

End  intarraysubstrules.


Section  chararraysubstrules.

Context (pm : Perm.t).

Lemma  subst_local_charstore: forall (x : var) (n:value) (start : addr) (i a : Z),
  subst_local x n (store_offset_char pm start i a) --||-- store_offset_char pm start i a.
Proof.
  unfold store_offset_char. intros.
  rewrite ! subst_local_and.
  rewrite ! subst_local_pure.
  rewrite subst_local_pv.
  reflexivity.
Qed.

Lemma subst_local_store_char_array_rec: forall l start lo hi x n,
   subst_local x n (store_char_array_rec pm start lo hi l) --||-- store_char_array_rec pm start lo hi l.
Proof.
  intros.
  unfold store_char_array_rec.
  erewrite subst_local_store_array_rec.
  reflexivity.
  apply subst_local_charstore.
Qed.

Lemma subst_local_store_char_array_missing_i_rec: forall l start i lo hi x n,
  subst_local x n (store_char_array_missing_i_rec pm start i lo hi l) --||-- store_char_array_missing_i_rec pm start i lo hi l.
Proof.
  intros.
  unfold store_char_array_missing_i_rec.
  erewrite subst_local_store_array_missing_i_rec.
  reflexivity.
  apply subst_local_charstore.
Qed.

Lemma subst_local_store_char_array: forall l start n x v,
  subst_local x v (store_char_array pm start n l) --||-- (store_char_array pm start n l).
Proof.
  intros.
  unfold store_char_array.
  erewrite subst_local_store_array.
  reflexivity.
  apply subst_local_charstore.
Qed.

Lemma  subst_global_charstore: forall (x : var) (n:value) (start : addr) (i a : Z),
  subst_global x n (store_offset_char pm start i a) --||-- store_offset_char pm start i a.
Proof.
  unfold store_offset_char. intros.
  rewrite ! subst_global_and.
  rewrite ! subst_global_pure.
  rewrite subst_global_pv.
  reflexivity.
Qed.

Lemma subst_global_store_char_array_rec: forall l start lo hi x n,
   subst_global x n (store_char_array_rec pm start lo hi l) --||-- store_char_array_rec pm start lo hi l.
Proof.
  intros.
  unfold store_char_array_rec.
  erewrite subst_global_store_array_rec.
  reflexivity.
  apply subst_global_charstore.
Qed.

Lemma subst_global_store_char_array_missing_i_rec: forall l start i lo hi x n,
  subst_global x n (store_char_array_missing_i_rec pm start i lo hi l) --||-- store_char_array_missing_i_rec pm start i lo hi l.
Proof.
  intros.
  unfold store_char_array_missing_i_rec.
  erewrite subst_global_store_array_missing_i_rec.
  reflexivity.
  apply subst_global_charstore.
Qed.

Lemma subst_global_store_char_array: forall l start n x v,
  subst_global x v (store_char_array pm start n l) --||-- (store_char_array pm start n l).
Proof.
  intros.
  unfold store_char_array.
  erewrite subst_global_store_array.
  reflexivity.
  apply subst_global_charstore.
Qed.


End  chararraysubstrules.

Ltac array_asrt_simpl := 
    repeat progress ( match goal with 
    | |- context [subst_local ?x ?xv (store_int_array_rec ?pm ?start ?lo ?hi ?l) ] => erewrite (subst_local_store_int_array_rec pm l start lo hi x xv)
    | |- context [subst_local ?x ?xv (store_int_array_missing_i_rec ?pm ?start ?i ?lo ?hi ?l) ] => erewrite (subst_local_store_int_array_missing_i_rec pm l start i lo hi x xv)
    | |- context [subst_local ?x ?xv (store_int_array ?pm ?start ?n ?l) ] => erewrite (subst_local_store_int_array pm l start n x xv)
    | |- context [subst_local ?x ?xv (store_char_array_rec ?pm ?start ?lo ?hi ?l) ] => erewrite (subst_local_store_char_array_rec pm l start lo hi x xv)
    | |- context [subst_local ?x ?xv (store_char_array_missing_i_rec ?pm ?start ?i ?lo ?hi ?l) ] => erewrite (subst_local_store_char_array_missing_i_rec pm l start i lo hi x xv)
    | |- context [subst_local ?x ?xv (store_char_array ?pm ?start ?n ?l) ] => erewrite (subst_local_store_char_array pm l start n x xv)
    | |- context [subst_global ?x ?xv (store_int_array_rec ?pm ?start ?lo ?hi ?l) ] => erewrite (subst_global_store_int_array_rec pm l start lo hi x xv)
    | |- context [subst_global ?x ?xv (store_int_array_missing_i_rec ?pm ?start ?i ?lo ?hi ?l) ] => erewrite (subst_global_store_int_array_missing_i_rec pm l start i lo hi x xv)
    | |- context [subst_global ?x ?xv (store_int_array ?pm ?start ?n ?l) ] => erewrite (subst_global_store_int_array pm l start n x xv)
    | |- context [subst_global ?x ?xv (store_char_array_rec ?pm ?start ?lo ?hi ?l) ] => erewrite (subst_global_store_char_array_rec pm l start lo hi x xv)
    | |- context [subst_global ?x ?xv (store_char_array_missing_i_rec ?pm ?start ?i ?lo ?hi ?l) ] => erewrite (subst_global_store_char_array_missing_i_rec pm l start i lo hi x xv)
    | |- context [subst_global ?x ?xv (store_char_array ?pm ?start ?n ?l) ] => erewrite (subst_global_store_char_array pm l start n x xv)
    end).

Module NormalImpHoareArrayRules.
Import NormalContextualImp.
Import NormalImpHoareRules.
Import NormalImpHoareTac.
Section  arrayhoarerules.
Context (pm : Perm.t).

Lemma hoare_LoadCharArrayElem : forall Δ x e1 e2 start i n l P,
  0 <= i < n ->
  P |--  EV e1 @ vptr ↦ₗ start ->
  P |--  EV e2 @ vint ↦ₗ i ->
  P |--  store_char_array pm start n l ** TT ->
  Δ ⊢ {{ P }} 
      CLoad x (EAdd e1  e2)
      {{EX v', !! (Znth i l 0 <= Byte.max_signed /\ Znth i l 0 >= Byte.min_signed) &&
        LV x @ vint ↦ₗ (Znth i l 0) && (subst_local x v' P)}} .
Proof.
  intros.
  rewrite store_char_array_split with (n:= i) in H2 by auto.
  eapply hoare_conseq_pre.
  + rewrite (prop_add_left P (Znth i l 0 <= Byte.max_signed /\ Znth i l 0 >= Byte.min_signed)).
    refl.
    eapply derivable1_trans.
    exact H2.
    unfoldimpmodel. quick_entailer!.
  +  
  eapply hoare_conseq_post'.
  - eapply hoare_LoadFull.
    * eapply aeval_expr_EAdd_ptr_derive.
      rewrite H0. quick_entailer!.  rewrite H1. quick_entailer!. 
    * eapply derivable1_trans. rewrite H2. refl.
      unfoldimpmodel.
      instantiate (1:= pm). instantiate (1:= (Znth i l 0, vint)).
      quick_entailer!.
  - Intros v'.
    Exists v'.
    quick_entailer!.  
Qed.

Lemma hoare_LoadIntArrayElem : forall Δ x e1 e2 start i n l P,
  0 <= i < n ->
  P |--  EV e1 @ vptr ↦ₗ start ->
  P |--  EV e2 @ vint ↦ₗ i ->
  P |--  store_int_array pm start n l ** TT ->
  Δ ⊢ {{ P }} 
      CLoad x (EAdd e1  e2)
      {{EX v', !! (Znth i l 0 <= Int64.max_signed /\ Znth i l 0 >= Int64.min_signed) &&
        LV x @ vint ↦ₗ (Znth i l 0) && (subst_local x v' P)}} .
Proof.
  intros.
  rewrite store_int_array_split with (n:= i) in H2 by auto.
  unfold store_offset_int64 in H2.
  eapply hoare_conseq_pre.
  + rewrite (prop_add_left P (Znth i l 0 <= Int64.max_signed /\ Znth i l 0 >= Int64.min_signed)).
    refl.
    eapply derivable1_trans.
    exact H2.
    unfoldimpmodel. quick_entailer!.
  +  
  eapply hoare_conseq_post'.
  - eapply hoare_LoadFull.
    * eapply aeval_expr_EAdd_ptr_derive.
      rewrite H0. quick_entailer!.  rewrite H1. quick_entailer!. 
    * eapply derivable1_trans. rewrite H2. refl.
      unfoldimpmodel.
      instantiate (1:= pm). instantiate (1:= (Znth i l 0, vint)).
      quick_entailer!.
  - Intros v'.
    Exists v'.
    quick_entailer!.  
Qed.



Lemma hoare_StoreIntArrayElem : forall Δ e1 e2 e3 start i v n l P p,
  0 <= i < n -> (Int64.min_signed <= v <= Int64.max_signed) ->
  P |--  EV e1 @ vptr ↦ₗ start ->
  P |--  EV e2 @ vint ↦ₗ i ->
  P |--  EV e3 @ vint ↦ₗ v ->
  P --||--  store_int_array ➀ start n l ** p ->
  Δ ⊢ {{ P }} 
      CStore (EAdd e1 e2) e3
      {{store_int_array ➀ start n (replace_Znth i v l) ** p}} .
Proof.
  intros * H Hrange. intros.
  erewrite (prop_add_left (store_int_array ➀ start n l)  (Zlength l = n)) in H3.
  2: apply store_int_array_Zlength.
  rewrite store_int_array_splitmerge with (n:= i) in H3 by auto.
  unfold store_offset_int64 in H3.
  eapply hoare_conseq_pre.
  + rewrite H3. refl.
  +
  hoare_simpl_pre.  
  eapply hoare_conseq_post'.
  - eapply hoare_Store'.
    * eapply aeval_expr_EAdd_ptr_derive.
      rewrite <- H0. rewrite H3. quick_entailer!.
      rewrite <- H1. rewrite H3. quick_entailer!.
    * rewrite <- H2. rewrite H3. quick_entailer!.
    * quick_entailer!.
    * reflexivity.
  - rewrite store_int_array_splitmerge with (n:= i)  by auto.
    unfold store_offset_int64.
    rewrite Znth_replace_Znth by lia.
    quick_entailer!.
    apply store_array_missing_i_rec_replace; auto.
Qed.


  
End  arrayhoarerules.

End NormalImpHoareArrayRules.


Module PracticalImpHoareArrayRules.
Import ContextualJoinStateGlobalEnv.
Import PracticalImpHoareRules.
Import PracticalImpHoareTac.

Section  arrayhoarerules.
Context (pm : Perm.t).

Lemma hoare_LoadCharArrayElem : forall Δ x e1 e2 start i n l P,
  0 <= i < n ->
  P |--  EV e1 @ vptr ↦ₗ start ->
  P |--  EV e2 @ vint ↦ₗ i ->
  P |--  store_char_array pm start n l ** TT ->
  Δ ⊢ {{ P }} 
      CLoad x (EAdd e1  e2)
      {{EX v', !! (Znth i l 0 <= Byte.max_signed /\ Znth i l 0 >= Byte.min_signed) &&
        LV x @ vint ↦ₗ (Znth i l 0) && (subst_local x v' P)}} .
Proof.
  intros.
  rewrite store_char_array_split with (n:= i) in H2 by auto.
  eapply hoare_conseq_pre.
  + rewrite (prop_add_left P (Znth i l 0 <= Byte.max_signed /\ Znth i l 0 >= Byte.min_signed)).
    refl.
    eapply derivable1_trans.
    exact H2.
    unfoldimpmodel. quick_entailer!.
  +  
  eapply hoare_conseq_post'.
  - eapply hoare_LoadFull.
    * eapply aeval_expr_EAdd_ptr_derive.
      rewrite H0. quick_entailer!.  rewrite H1. quick_entailer!. 
    * eapply derivable1_trans. rewrite H2. refl.
      unfoldimpmodel.
      instantiate (1:= pm). instantiate (1:= (Znth i l 0, vint)).
      quick_entailer!.
  - Intros v'.
    Exists v'.
    quick_entailer!.  
Qed.

Lemma hoare_LoadIntArrayElem : forall Δ x e1 e2 start i n l P,
  0 <= i < n ->
  P |--  EV e1 @ vptr ↦ₗ start ->
  P |--  EV e2 @ vint ↦ₗ i ->
  P |--  store_int_array pm start n l ** TT ->
  Δ ⊢ {{ P }} 
      CLoad x (EAdd e1  e2)
      {{EX v', !! (Znth i l 0 <= Int64.max_signed /\ Znth i l 0 >= Int64.min_signed) &&
        LV x @ vint ↦ₗ (Znth i l 0) && (subst_local x v' P)}} .
Proof.
  intros.
  rewrite store_int_array_split with (n:= i) in H2 by auto.
  unfold store_offset_int64 in H2.
  eapply hoare_conseq_pre.
  + rewrite (prop_add_left P (Znth i l 0 <= Int64.max_signed /\ Znth i l 0 >= Int64.min_signed)).
    refl.
    eapply derivable1_trans.
    exact H2.
    unfoldimpmodel. quick_entailer!.
  +  
  eapply hoare_conseq_post'.
  - eapply hoare_LoadFull.
    * eapply aeval_expr_EAdd_ptr_derive.
      rewrite H0. quick_entailer!.  rewrite H1. quick_entailer!. 
    * eapply derivable1_trans. rewrite H2. refl.
      unfoldimpmodel.
      instantiate (1:= pm). instantiate (1:= (Znth i l 0, vint)).
      quick_entailer!.
  - Intros v'.
    Exists v'.
    quick_entailer!.  
Qed.



Lemma hoare_StoreIntArrayElem : forall Δ e1 e2 e3 start i v n l P p,
  0 <= i < n -> (Int64.min_signed <= v <= Int64.max_signed) ->
  P |--  EV e1 @ vptr ↦ₗ start ->
  P |--  EV e2 @ vint ↦ₗ i ->
  P |--  EV e3 @ vint ↦ₗ v ->
  P --||--  store_int_array ➀ start n l ** p ->
  Δ ⊢ {{ P }} 
      CStore (EAdd e1 e2) e3
      {{store_int_array ➀ start n (replace_Znth i v l) ** p}} .
Proof.
  intros * H Hrange. intros.
  erewrite (prop_add_left (store_int_array ➀ start n l)  (Zlength l = n)) in H3.
  2: apply store_int_array_Zlength.
  rewrite store_int_array_splitmerge with (n:= i) in H3 by auto.
  unfold store_offset_int64 in H3.
  eapply hoare_conseq_pre.
  + rewrite H3. refl.
  +
  hoare_simpl_pre.  
  eapply hoare_conseq_post'.
  - eapply hoare_Store'.
    * eapply aeval_expr_EAdd_ptr_derive.
      rewrite <- H0. rewrite H3. quick_entailer!.
      rewrite <- H1. rewrite H3. quick_entailer!.
    * rewrite <- H2. rewrite H3. quick_entailer!.
    * quick_entailer!.
    * reflexivity.
  - rewrite store_int_array_splitmerge with (n:= i)  by auto.
    unfold store_offset_int64.
    rewrite Znth_replace_Znth by lia.
    quick_entailer!.
    apply store_array_missing_i_rec_replace; auto.
Qed.


  
End  arrayhoarerules.

End PracticalImpHoareArrayRules.