Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap ListLib.
From compcert.lib Require Import Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem CommonAssertion StoreAux.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type ArrayLibSig (CRules: SeparationLogicSig) (DePredSig : DerivedPredSig CRules) (SLibSig : StoreLibSig CRules DePredSig).

Import CRules.
Import DePredSig.
Import SLibSig.
Local Open Scope sac.  

Lemma store_array_rec_length: forall {A : Type} storeA x lo hi (l : list A),
  store_array_rec storeA x lo hi l |-- [| Z.of_nat (length l) = hi - lo |].
Proof.
  intros.
  revert lo; induction l; simpl store_array_rec ; intros.
  + entailer!. simpl in *; lia.
  + prop_apply IHl.
    entailer!. simpl in * ; lia.
Qed.

Lemma store_array_length: forall {A : Type} storeA x n (l : list A),
  store_array storeA x n l |-- [| Z.of_nat (length l) = n |].
Proof.
  intros.
  unfold store_array.
  prop_apply (store_array_rec_length storeA).
  entailer!. 
Qed.

Lemma store_array_Zlength: forall {A : Type} storeA x n (l : list A),
  store_array storeA x n l |-- [| Zlength l = n |].
Proof.
  intros. rewrite Zlength_correct.
  apply store_array_length.
Qed.

Lemma store_array_rec_split: forall {A : Type} storeA x lo n m (l : list A) a,
  lo <= n < m ->
  store_array_rec storeA x lo m l |-- storeA x n (Znth (n - lo) l a) ** store_array_missing_i_rec storeA x n lo m l.
Proof.
  intros.
  revert H.
  rename m into hi.
  revert lo; induction l; intros; simpl; intros.
  + entailer!.
  + pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
    - Right.
      sep_apply IHl; [ | lia ].
      rewrite Znth_cons by lia.
      replace (n - (lo + 1)) with (n - lo - 1) by lia.
      entailer!.
    - rewrite <- derivable1_orp_intros1.
      subst n.
      replace (lo - lo) with 0 by lia.
      entailer!.
Qed. 

Lemma store_array_split: forall {A : Type} storeA x n m (l : list A) a,
  0 <= n < m ->
  store_array storeA x m l |-- storeA x n (Znth n l a) ** store_array_missing_i_rec storeA x n 0 m l.
Proof.
  intros.
  revert H.
  unfold store_array.
  replace n with (n - 0) at 4 by lia.
  eapply store_array_rec_split.
Qed. 


Lemma store_array_rec_merge: forall {A : Type} storeA x lo n m a (l: list A),
  lo <= n < m -> 
  storeA x n a ** store_array_missing_i_rec storeA x n lo m l |-- store_array_rec storeA x lo m (replace_Znth (n - lo) a l).
Proof.
  intros.
  revert H.
  revert lo; induction l; intros; simpl.
  + entailer!.
  + rewrite derivable1_sepcon_comm.
    apply derivable1s_wand_sepcon_adjoint.
    Split;
    apply derivable1s_wand_sepcon_adjoint.
    - Intros.
      subst n.
      replace (lo - lo) with 0 by lia.
      simpl.
      entailer!.
    - Intros.
      sep_apply IHl; [ | lia ].
      entailer!.
      rewrite replace_Znth_cons by lia.
      replace (n - (lo + 1)) with (n - lo - 1) by lia.
      simpl.
      entailer!.
Qed.


Lemma store_array_merge: forall {A : Type} storeA x n m a (l: list A),
  0 <= n < m -> 
  storeA x n a ** store_array_missing_i_rec storeA x n 0 m l |-- store_array storeA x m (replace_Znth n a l).
Proof.
  intros.
  unfold store_array.
  replace n with (n - 0) at 3 by lia.
  eapply store_array_rec_merge;auto.
Qed.

Lemma store_array_rec_base {A: Type}:
  forall x m k n l size (storeA: addr -> A -> model -> Prop) f, 
    f = (fun (x0 : addr) (lo: Z) (a0: A) => storeA (x0 + lo * size) a0) ->
    store_array_rec f x (m+k) n l --||--
    store_array_rec f (x + k * size) m (n-k) l.
Proof.
  intros; revert m k; induction l; intros.
  - simpl; split; entailer!.
  - rewrite H; simpl.
    replace (x + k * size + m * size) with (x + (m + k) * size) by lia.
    rewrite <- H.
    replace (m+k+1) with (m+1+k) by lia.
    split; rewrite IHl; entailer!.
Qed.

Lemma store_array_rec_divide_aux {A: Type}:
  forall lo m n l x size (storeA: addr -> A -> model -> Prop) f,
    lo <= m <= n -> Zlength l = n - lo -> 
    f = (fun (x0 : addr) (lo: Z) (a0: A) => storeA (x0 + lo * size) a0) ->
    store_array_rec f x lo n l --||--
    store_array_rec f x lo m (sublist 0 (m - lo) l) ** store_array_rec f x m n (sublist (m -lo) (n -lo) l).
Proof.
  intros.
  rename H0 into Hl; rename H1 into H0.
  revert x lo m n H Hl.
  induction l; intros.
  - rewrite H0; repeat rewrite sublist_of_nil.
    simpl; split; entailer!.
  - rewrite H0; unfold store_array.
    destruct (Z_lt_ge_dec m (lo + 1)).
    + assert (m = lo) by lia; subst m.
      rewrite sublist_nil by lia.
      replace (lo - lo) with 0 by lia.
      rewrite sublist_self by easy.
      simpl; split; entailer!.
    + rewrite sublist_cons1 by lia.
      simpl.
      rewrite store_array_rec_base by auto.
      rewrite H0 in IHl; unfold store_array.
      rewrite sublist_cons2 by lia.
      unfold store_array in IHl.
      pose proof Hl as Hl2.
      change (a::l) with ([a]++l) in Hl2.
      rewrite Zlength_app in Hl2; replace (Zlength [a]) with 1 in Hl2 by easy.
      rewrite (IHl (x + 1 * size) lo (m-1)); try lia.
      replace (m -1) with (m + (-1)) at 3 by lia.
      repeat rewrite store_array_rec_base by auto.
      replace (x + 1*size + (-1)*size) with x by lia.
      replace (m - 1 - lo) with (m - lo - 1) by lia.
      replace (n -1 - -1) with n by lia.
      replace (n -1 - lo) with (n - lo - 1) by lia.
      split; entailer!.
Qed.


Lemma store_array_rec_divide {A: Type}:
  forall m n l x size (storeA: addr -> A -> model -> Prop) f,
    0 <= m <= n -> Zlength l = n -> 
    f = (fun (x0 : addr) (lo: Z) (a0: A) => storeA (x0 + lo * size) a0) ->
    store_array_rec f x 0 n l --||--
    store_array_rec f x 0 m (sublist 0 m l) ** store_array_rec f x m n (sublist m n l).
Proof.
  intros.
  erewrite store_array_rec_divide_aux with (lo := 0 ) (m := m) ; try lia.
  2: exact H1.
  replace (m - 0) with m by lia.
  replace (n - 0) with n by lia.
  reflexivity.
Qed.

Lemma store_array_divide {A: Type}:
  forall x n l m size (storeA: addr -> A -> model -> Prop) f g,
    0 <= m <= n -> Zlength l = n ->
    f = (fun (x0 : addr) (lo: Z) (a0: A) => storeA (x0 + lo * size) a0) ->
    g = store_array f ->
    g x n l --||-- 
    g x m (sublist 0 m l) ** g (x + m * size) (n-m) (sublist m n l).
Proof.
  intros; rewrite H2; unfold store_array.
  rewrite store_array_rec_divide; eauto.
  unfold store_array; split; entailer!.
  - replace m with (0+m) at 1 by lia.
    rewrite store_array_rec_base by eauto.
    reflexivity.
  - replace m with (0+m) at 4 by lia.
    rewrite store_array_rec_base by eauto.
    reflexivity.
Qed.

Lemma store_undef_array_rec_base :
  forall x m k n len size (storeA: addr -> Assertion) f, 
    f = (fun (x0 : addr) (lo: Z) => storeA (x0 + lo * size)) ->
    store_undef_array_rec f x (m+k) n len  --||--
    store_undef_array_rec f (x + k * size) m (n-k) len.
Proof.
  intros; revert m k; induction len; intros.
  - simpl; split; entailer!.
  - rewrite H; simpl.
    replace (x + k * size + m * size) with (x + (m + k) * size) by lia.
    rewrite <- H.
    replace (m+k+1) with (m+1+k) by lia.
    split; rewrite IHlen; entailer!.
Qed.

Lemma store_undef_array_divide : 
   forall x n m size (storeA: addr -> Assertion) f,
    0 <= m <= n ->  
    f = (fun (x0 : addr) (lo: Z) => storeA (x0 + lo * size)) ->
    store_undef_array f x n --||--
    store_undef_array f x m ** store_undef_array f (x + m * size) (n-m).
Proof.
  intros. unfold store_undef_array.
  remember (Z.to_nat n) as n0.
  remember (Z.to_nat m) as m0.
  replace (Z.to_nat (n - m)) with (n0 - m0)%nat by lia.
  replace (n - m) with (Z.of_nat (n0 - m0)) by lia.
  replace (m) with (Z.of_nat m0) by lia.
  replace (n) with (Z.of_nat n0) by lia.
  assert (O <= m0 <= n0)%nat by lia.
  clear Heqn0 Heqm0 H m n.
  rename m0 into m; rename n0 into n.
  generalize dependent n. 
  induction m.
  + simpl in * ; intros. replace (x + 0) with x by lia.
    replace (n - 0)%nat with n by lia.
    split ; entailer!.
  + intros.
    rewrite (IHm (S m) (ltac:(lia))).
    rewrite (IHm n) by lia. clear IHm.
    replace (Z.of_nat (n - S m)) with (Z.of_nat n - Z.of_nat (S m)) by lia.
    replace (Z.of_nat (n - m)) with (Z.of_nat n - Z.of_nat m) by lia.
    replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
    repeat rewrite <- store_undef_array_rec_base by eauto.
    repeat rewrite Z.add_0_l.
    replace (S m - m)%nat with 1%nat by lia.
    replace (n - m)%nat with (S (n - S m)) by lia.
    subst f ; simpl. 
    split  ; replace (x + Z.of_nat m * size + 0) with (x + Z.of_nat m * size) by lia ;
    entailer!.      
Qed.

Module IntArrayLib.

Definition store_int_array_rec (x: addr) (lo hi: Z) (l: list Z): Assertion :=
  store_array_rec (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a) x lo hi l.
  
Definition store_undef_int_array_rec (x: addr) (lo hi: Z): Assertion :=
  store_undef_array_rec (fun x lo => (x + lo * sizeof(INT)) # Int |->_ ) x lo hi (Z.to_nat (hi - lo)).

Lemma store_int_array_rec_length: forall x lo hi l,
  store_int_array_rec x lo hi l |-- [| Z.of_nat (length l) = hi - lo |].
Proof.
  intros.
  unfold store_int_array_rec.
  sep_apply (store_array_rec_length (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
Qed.

Lemma store_int_array_rec_Zlength: forall x lo hi l,
  store_int_array_rec x lo hi l |-- [| Zlength l = hi - lo |].
Proof.
  intros.
  sep_apply store_int_array_rec_length.
  rewrite Zlength_correct.
  entailer!.
Qed.


Definition store_int_array_missing_i_rec (x: addr) (i lo hi: Z) (l: list Z): Assertion := 
  store_array_missing_i_rec (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a) x i lo hi l.

Definition store_undef_int_array_missing_i_re (x: addr) (i lo hi: Z) : Assertion :=
  store_undef_array_missing_i_rec (fun x lo => (x + lo * sizeof(INT)) # Int |->_ ) x i lo hi (Z.to_nat (hi - lo)).

Definition store_int_array (x: addr) (n: Z) (l: list Z): Assertion :=
  store_array (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a) x n l.

Definition store_undef_int_array (x: addr) (n: Z): Assertion :=
  store_undef_array (fun x lo => (x + lo * sizeof(INT)) # Int |->_ ) x n.

Lemma store_int_array_length: forall x n l,
  store_int_array x n l |-- [| Z.of_nat (length l) = n |].
Proof.
  intros.
  unfold store_int_array.
  sep_apply store_int_array_rec_length.
  entailer!. 
Qed.

Lemma store_int_array_Zlength: forall x n l,
  store_int_array x n l |-- [| Zlength l = n |].
Proof.
  intros.
  unfold store_int_array.
  apply store_array_Zlength.
Qed.

Lemma store_int_array_range : forall x n l,
  store_int_array x n l |-- [| forall a, In a l -> Int.min_signed <= a <= Int.max_signed |].
Proof.
  intros.
  unfold store_int_array.
  unfold store_array.
  remember 0 as lo.
  rename n into hi.
  clear Heqlo. revert lo hi. 
  induction l ; intros. 
  - entailer!.
  - simpl. prop_apply IHl.
    prop_apply store_int_range.
    entailer!.
    intros. destruct H1 ; auto.
    subst. auto. 
Qed.

Lemma store_int_array_rec_split: forall x lo n m l,
  lo <= n < m ->
  store_int_array_rec x lo m l |-- store_int (x + n * sizeof(INT)) (Znth (n -lo) l 0) ** store_int_array_missing_i_rec x n lo m l.
Proof.
  intros.
  unfold store_int_array_rec, store_int_array_missing_i_rec.
  sep_apply (store_array_rec_split (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
  lia.
Qed.

Lemma store_int_array_rec_merge: forall x lo n m a l,
  lo <= n < m ->
  store_int (x + n * sizeof(INT)) a ** store_int_array_missing_i_rec x n lo m l |-- store_int_array_rec x lo m (replace_Znth (n -lo) a l).
Proof.
  intros.
  unfold store_int_array_rec, store_int_array_missing_i_rec.
  sep_apply (store_array_rec_merge (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
  lia.
Qed.

Lemma store_int_array_rec_divide:
  forall x lo n l m,
    lo <= m <= n -> Zlength l = n -lo ->
    store_int_array_rec x lo n l --||-- 
    store_int_array_rec x lo m (sublist 0 (m - lo) l) ** store_int_array_rec x m n (sublist (m -lo) (n -lo) l).
Proof.
  intros; unfold store_int_array_rec. 
  eapply store_array_rec_divide_aux with (storeA := store_int); eauto.
Qed.

Lemma store_int_array_rec_divide_rev:
  forall x lo n l1 l2 m,
    lo <= m <= n -> 
    store_int_array_rec x lo m l1 ** store_int_array_rec x m n l2 |-- 
    store_int_array_rec x lo n (l1 ++ l2).
Proof.
  intros.
  prop_apply (store_int_array_rec_Zlength x lo).
  prop_apply (store_int_array_rec_Zlength x m).
  Intros.
  rewrite (store_int_array_rec_divide x lo n (l1 ++ l2) m);[ | lia | ].
  rewrite <- H0.
  rewrite sublist_app_exact1 by lia.
  rewrite sublist_split_app_r with (len := Zlength l1) by lia.
  replace (Zlength l1 - Zlength l1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_app. lia.
Qed.

Lemma store_int_array_rec_head:
  forall x lo hi l,
    lo < hi -> 
    store_int_array_rec x lo hi l  |-- 
    (x + lo * sizeof ( INT )) # Int |-> (Znth 0 l 0) ** 
    store_int_array_rec x (lo + 1) hi (sublist 1 (hi - lo) l).
Proof.
  intros.
  destruct l.
  - unfold store_int_array_rec. simpl.
    entailer!.
  - prop_apply (store_int_array_rec_Zlength x lo hi).
  Intros.
  rewrite (store_int_array_rec_divide x lo hi ((z :: nil) ++ l) (lo + 1));[ | lia | easy ].
  replace (lo + 1 - lo) with 1 by lia.
  assert (Zlength (z::nil) = 1). { rewrite Zlength_cons, Zlength_nil. lia. }
  rewrite <- H1 at 2.
  rewrite sublist_app_exact1.
  replace (z::l) with (app (z :: nil) l)  by easy.
  rewrite sublist_split_app_r with (len := 1) by lia.
  replace (1 - 1) with 0 by lia.
  rewrite sublist_self.
  entailer!.
  unfold store_int_array_rec. simpl.
  Intros.
  rewrite Znth0_cons.
  entailer!.
  rewrite Zlength_cons in H0. lia. 
Qed.


Lemma store_int_array_rec_head_merge:
  forall x lo hi z l,
    lo < hi -> 
    (x + lo * sizeof ( INT )) # Int |-> z ** 
    store_int_array_rec x (lo + 1) hi l |-- 
    store_int_array_rec x lo hi (z :: l).
Proof.
  intros.
  prop_apply (store_int_array_rec_Zlength x (lo + 1) hi).
  Intros.
  rewrite (store_int_array_rec_divide x lo hi ((z :: nil) ++ l) (lo + 1));[ | lia |  ].
  replace (lo + 1 - lo) with 1 by lia.
  assert (Zlength (z::nil) = 1). { rewrite Zlength_cons, Zlength_nil. lia. }
  rewrite <- H1 at 3.
  rewrite sublist_app_exact1.
  rewrite sublist_split_app_r with (len := 1) by lia.
  replace (1 - 1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  unfold store_int_array_rec. simpl.
  entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.  lia. 
Qed.

Lemma store_int_array_rec_tail_merge:
  forall x lo hi z l,
    lo <= hi -> 
    (x + hi * sizeof ( INT )) # Int |-> z ** 
    store_int_array_rec x lo hi l |-- 
    store_int_array_rec x lo (hi + 1) (l ++ [z]).
Proof.
  intros.
  prop_apply (store_int_array_rec_Zlength x lo hi).
  Intros.
  rewrite (store_int_array_rec_divide x lo (hi + 1) (l ++ [z]) hi);[ | lia |  ].
  rewrite <- H0 at 1.
  rewrite sublist_app_exact1.
  rewrite sublist_split_app_r with (len := hi - lo) by lia.
  replace (hi - lo - (hi - lo)) with 0 by lia.
  rewrite sublist_self.
  entailer!.
  unfold store_int_array_rec. simpl.
  entailer!.
  rewrite Zlength_cons, Zlength_nil. lia.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.  lia. 
Qed.

Lemma store_int_array_rec_cons:
  forall x lo hi z l,
    lo < hi -> 
    store_int_array_rec x lo hi (z::l)  |-- 
    (x + lo * sizeof ( INT )) # Int |-> z ** 
    store_int_array_rec x (lo + 1) hi l.
Proof.
  intros.
  prop_apply store_int_array_rec_Zlength.
  Intros.
  rewrite Zlength_cons in H0.
  sep_apply store_int_array_rec_head;[ | lia].
  rewrite Znth0_cons.
  replace (z :: l) with ([z] ++ l) by easy.
  rewrite sublist_split_app_r with (len := 1).
  replace (1-1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_cons,Zlength_nil. lia.
  lia.
Qed.

Lemma store_int_array_split: forall x n m l,
  0 <= n < m ->
  store_int_array x m l |-- store_int (x + n * sizeof(INT)) (Znth n l 0) ** store_int_array_missing_i_rec x n 0 m l.
Proof.
  intros.
  unfold store_int_array, store_int_array_missing_i_rec.
  sep_apply (store_array_split (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
  lia.
Qed.

Lemma store_int_array_merge: forall x n m a l,
  0 <= n < m ->
  store_int (x + n * sizeof(INT)) a ** store_int_array_missing_i_rec x n 0 m l |-- store_int_array x m (replace_Znth n a l).
Proof.
  intros.
  unfold store_int_array, store_int_array_missing_i_rec.
  sep_apply (store_array_merge (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
  lia.
Qed.

Lemma store_int_array_divide:
  forall x n l m,
    0 <= m <= n -> Zlength l = n ->
    store_int_array x n l --||-- 
    store_int_array x m (sublist 0 m l) ** store_int_array (x + m*sizeof(INT)) (n-m) (sublist m n l).
Proof.
  intros; unfold store_int_array. 
  eapply store_array_divide with (storeA := store_int); eauto.
  auto.
Qed.

Lemma store_int_array_divide_rec:
  forall x n l m,
    0 <= m <= n -> Zlength l = n ->
    store_int_array x n l --||-- 
    store_int_array_rec x 0 m (sublist 0 m l) ** store_int_array_rec x m n (sublist m n l).
Proof.
  intros; unfold store_int_array, store_array. 
  eapply store_array_rec_divide with (storeA := store_int); eauto.
Qed.

Definition store_uint_array_rec (x: addr) (lo hi: Z) (l: list Z): Assertion :=
  store_array_rec (fun x lo a => (x + lo * sizeof(UINT)) # UInt |-> a) x lo hi l.
  
Definition store_undef_uint_array_rec (x: addr) (lo hi: Z): Assertion :=
  store_undef_array_rec (fun x lo => (x + lo * sizeof(UINT)) # UInt |->_ ) x lo hi (Z.to_nat (hi - lo)).

Lemma store_uint_array_rec_length: forall x lo hi l,
  store_uint_array_rec x lo hi l |-- [| Z.of_nat (length l) = hi - lo |].
Proof.
  intros.
  unfold store_uint_array_rec.
  sep_apply (store_array_rec_length (fun x lo a => (x + lo * sizeof(UINT)) # UInt |-> a)). entailer!.
Qed.

Lemma store_uint_array_rec_Zlength: forall x lo hi l,
  store_uint_array_rec x lo hi l |-- [| Zlength l = hi - lo |].
Proof.
  intros.
  sep_apply store_uint_array_rec_length.
  rewrite Zlength_correct.
  entailer!.
Qed.


Definition store_uint_array_missing_i_rec (x: addr) (i lo hi: Z) (l: list Z): Assertion := 
  store_array_missing_i_rec (fun x lo a => (x + lo * sizeof(UINT)) # UInt |-> a) x i lo hi l.

Definition store_undef_uint_array_missing_i_re (x: addr) (i lo hi: Z) : Assertion :=
  store_undef_array_missing_i_rec (fun x lo => (x + lo * sizeof(UINT)) # UInt |->_ ) x i lo hi (Z.to_nat (hi - lo)).

Definition store_uint_array (x: addr) (n: Z) (l: list Z): Assertion :=
  store_array (fun x lo a => (x + lo * sizeof(UINT)) # UInt |-> a) x n l.

Definition store_undef_uint_array (x: addr) (n: Z): Assertion :=
  store_undef_array (fun x lo => (x + lo * sizeof(UINT)) # UInt |->_ ) x n.

Lemma store_uint_array_length: forall x n l,
  store_uint_array x n l |-- [| Z.of_nat (length l) = n |].
Proof.
  intros.
  unfold store_uint_array.
  sep_apply store_uint_array_rec_length.
  entailer!. 
Qed.

Lemma store_uint_array_Zlength: forall x n l,
  store_uint_array x n l |-- [| Zlength l = n |].
Proof.
  intros.
  unfold store_uint_array.
  apply store_array_Zlength.
Qed.

Lemma store_uint_array_range : forall x n l,
  store_uint_array x n l |-- [| forall a, In a l -> NULL <= a <= Int.max_unsigned |].
Proof.
  intros.
  unfold store_uint_array.
  unfold store_array.
  remember 0 as lo. 
  rename n into hi.
  clear Heqlo. revert lo hi. unfold NULL. 
  induction l ; intros. 
  - entailer!.
  - simpl. prop_apply IHl.
    prop_apply store_uint_range.
    entailer!.
    intros. destruct H1 ; auto.
    subst. auto. 
Qed.

Lemma store_uint_array_rec_split: forall x lo n m l,
  lo <= n < m ->
  store_uint_array_rec x lo m l |-- store_uint (x + n * sizeof(UINT)) (Znth (n -lo) l 0) ** store_uint_array_missing_i_rec x n lo m l.
Proof.
  intros.
  unfold store_uint_array_rec, store_uint_array_missing_i_rec.
  sep_apply (store_array_rec_split (fun x lo a => (x + lo * sizeof(UINT)) # UInt |-> a)). entailer!.
  lia.
Qed.

Lemma store_uint_array_rec_merge: forall x lo n m a l,
  lo <= n < m ->
  store_uint (x + n * sizeof(UINT)) a ** store_uint_array_missing_i_rec x n lo m l |-- store_uint_array_rec x lo m (replace_Znth (n -lo) a l).
Proof.
  intros.
  unfold store_uint_array_rec, store_uint_array_missing_i_rec.
  sep_apply (store_array_rec_merge (fun x lo a => (x + lo * sizeof(UINT)) # UInt |-> a)). entailer!.
  lia.
Qed.

Lemma store_uint_array_rec_divide:
  forall x lo n l m,
    lo <= m <= n -> Zlength l = n -lo ->
    store_uint_array_rec x lo n l --||-- 
    store_uint_array_rec x lo m (sublist 0 (m - lo) l) ** store_uint_array_rec x m n (sublist (m -lo) (n -lo) l).
Proof.
  intros; unfold store_uint_array_rec. 
  eapply store_array_rec_divide_aux with (storeA := store_uint); eauto.
Qed.

Lemma store_uint_array_rec_divide_rev:
  forall x lo n l1 l2 m,
    lo <= m <= n -> 
    store_uint_array_rec x lo m l1 ** store_uint_array_rec x m n l2 |-- 
    store_uint_array_rec x lo n (l1 ++ l2).
Proof.
  intros.
  prop_apply (store_uint_array_rec_Zlength x lo).
  prop_apply (store_uint_array_rec_Zlength x m).
  Intros.
  rewrite (store_uint_array_rec_divide x lo n (l1 ++ l2) m);[ | lia | ].
  rewrite <- H0.
  rewrite sublist_app_exact1 by lia.
  rewrite sublist_split_app_r with (len := Zlength l1) by lia.
  replace (Zlength l1 - Zlength l1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_app. lia.
Qed.

Lemma store_uint_array_rec_head:
  forall x lo hi l,
    lo < hi -> 
    store_uint_array_rec x lo hi l  |-- 
    (x + lo * sizeof ( UINT )) # UInt |-> (Znth 0 l 0) ** 
    store_uint_array_rec x (lo + 1) hi (sublist 1 (hi - lo) l).
Proof.
  intros.
  destruct l.
  - unfold store_uint_array_rec. simpl.
    entailer!.
  - prop_apply (store_uint_array_rec_Zlength x lo hi).
  Intros.
  rewrite (store_uint_array_rec_divide x lo hi ((z :: nil) ++ l) (lo + 1));[ | lia | easy ].
  replace (lo + 1 - lo) with 1 by lia.
  assert (Zlength (z::nil) = 1). { rewrite Zlength_cons, Zlength_nil. lia. }
  rewrite <- H1 at 2.
  rewrite sublist_app_exact1.
  replace (z::l) with (app (z :: nil) l)  by easy.
  rewrite sublist_split_app_r with (len := 1) by lia.
  replace (1 - 1) with 0 by lia.
  rewrite sublist_self.
  entailer!.
  unfold store_uint_array_rec. simpl.
  Intros.
  rewrite Znth0_cons.
  entailer!.
  rewrite Zlength_cons in H0. lia. 
Qed.


Lemma store_uint_array_rec_head_merge:
  forall x lo hi z l,
    lo < hi -> 
    (x + lo * sizeof ( UINT )) # UInt |-> z ** 
    store_uint_array_rec x (lo + 1) hi l |-- 
    store_uint_array_rec x lo hi (z :: l).
Proof.
  intros.
  prop_apply (store_uint_array_rec_Zlength x (lo + 1) hi).
  Intros.
  rewrite (store_uint_array_rec_divide x lo hi ((z :: nil) ++ l) (lo + 1));[ | lia |  ].
  replace (lo + 1 - lo) with 1 by lia.
  assert (Zlength (z::nil) = 1). { rewrite Zlength_cons, Zlength_nil. lia. }
  rewrite <- H1 at 3.
  rewrite sublist_app_exact1.
  rewrite sublist_split_app_r with (len := 1) by lia.
  replace (1 - 1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  unfold store_uint_array_rec. simpl.
  entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.  lia. 
Qed.

Lemma store_uint_array_rec_tail_merge:
  forall x lo hi z l,
    lo <= hi -> 
    (x + hi * sizeof ( UINT )) # UInt |-> z ** 
    store_uint_array_rec x lo hi l |-- 
    store_uint_array_rec x lo (hi + 1) (l ++ [z]).
Proof.
  intros.
  prop_apply (store_uint_array_rec_Zlength x lo hi).
  Intros.
  rewrite (store_uint_array_rec_divide x lo (hi + 1) (l ++ [z]) hi);[ | lia |  ].
  rewrite <- H0 at 1.
  rewrite sublist_app_exact1.
  rewrite sublist_split_app_r with (len := hi - lo) by lia.
  replace (hi - lo - (hi - lo)) with 0 by lia.
  rewrite sublist_self.
  entailer!.
  unfold store_uint_array_rec. simpl.
  entailer!.
  rewrite Zlength_cons, Zlength_nil. lia.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.  lia. 
Qed.

Lemma store_uint_array_rec_cons:
  forall x lo hi z l,
    lo < hi -> 
    store_uint_array_rec x lo hi (z::l)  |-- 
    (x + lo * sizeof ( UINT )) # UInt |-> z ** 
    store_uint_array_rec x (lo + 1) hi l.
Proof.
  intros.
  prop_apply store_uint_array_rec_Zlength.
  Intros.
  rewrite Zlength_cons in H0.
  sep_apply store_uint_array_rec_head;[ | lia].
  rewrite Znth0_cons.
  replace (z :: l) with ([z] ++ l) by easy.
  rewrite sublist_split_app_r with (len := 1).
  replace (1-1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_cons,Zlength_nil. lia.
  lia.
Qed.

Lemma store_uint_array_split: forall x n m l,
  0 <= n < m ->
  store_uint_array x m l |-- store_uint (x + n * sizeof(UINT)) (Znth n l 0) ** store_uint_array_missing_i_rec x n 0 m l.
Proof.
  intros.
  unfold store_uint_array, store_uint_array_missing_i_rec.
  sep_apply (store_array_split (fun x lo a => (x + lo * sizeof(UINT)) # UInt |-> a)). entailer!.
  lia.
Qed.

Lemma store_uint_array_merge: forall x n m a l,
  0 <= n < m ->
  store_uint (x + n * sizeof(UINT)) a ** store_uint_array_missing_i_rec x n 0 m l |-- store_uint_array x m (replace_Znth n a l).
Proof.
  intros.
  unfold store_uint_array, store_uint_array_missing_i_rec.
  sep_apply (store_array_merge (fun x lo a => (x + lo * sizeof(UINT)) # UInt |-> a)). entailer!.
  lia.
Qed.

Lemma store_uint_array_divide:
  forall x n l m,
    0 <= m <= n -> Zlength l = n ->
    store_uint_array x n l --||-- 
    store_uint_array x m (sublist 0 m l) ** store_uint_array (x + m*sizeof(UINT)) (n-m) (sublist m n l).
Proof.
  intros; unfold store_uint_array. 
  eapply store_array_divide with (storeA := store_uint); eauto.
  auto.
Qed.

Lemma store_uint_array_divide_rec:
  forall x n l m,
    0 <= m <= n -> Zlength l = n ->
    store_uint_array x n l --||-- 
    store_uint_array_rec x 0 m (sublist 0 m l) ** store_uint_array_rec x m n (sublist m n l).
Proof.
  intros; unfold store_uint_array, store_array. 
  eapply store_array_rec_divide with (storeA := store_uint); eauto.
Qed.

End IntArrayLib.

Export IntArrayLib.

Module CharArrayLib.

Definition store_char_array_rec (x: addr) (lo hi: Z) (l: list Z): Assertion :=
  store_array_rec (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a) x lo hi l. 

Definition store_undef_char_array_rec (x: addr) (lo hi: Z): Assertion :=
  store_undef_array_rec (fun x lo => (x + lo * sizeof(CHAR)) # Char |->_ ) x lo hi (Z.to_nat (hi - lo)).

Lemma store_char_array_rec_length: forall x lo hi l,
  store_char_array_rec x lo hi l |-- [| Z.of_nat (length l) = hi - lo |].
Proof.
  intros.
  unfold store_char_array_rec.
  sep_apply (store_array_rec_length (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a)). entailer!.
Qed.

Definition store_char_array_missing_i_rec (x: addr) (i lo hi: Z) (l: list Z): Assertion := 
  store_array_missing_i_rec (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a) x i lo hi l.

Definition store_undef_char_array_missing_i_re (x: addr) (i lo hi: Z) : Assertion :=
  store_undef_array_missing_i_rec (fun x lo => (x + lo * sizeof(CHAR)) # Char |->_ ) x i lo hi (Z.to_nat (hi - lo)).

Definition store_char_array (x: addr) (n: Z) (l: list Z): Assertion :=
  store_array (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a) x n l.

Definition store_undef_char_array (x: addr) (n: Z): Assertion :=
  store_undef_array (fun x lo => (x + lo * sizeof(CHAR)) # Char |->_ ) x n.

Lemma store_char_array_length: forall x n l,
  store_char_array x n l |-- [| Z.of_nat (length l) = n |].
Proof.
  intros.
  unfold store_char_array.
  sep_apply store_char_array_rec_length.
  entailer!. 
Qed.

Lemma store_char_array_Zlength: forall x n l,
  store_char_array x n l |-- [| Zlength l = n |].
Proof.
  intros; unfold store_char_array.
  apply store_array_Zlength.
Qed.

Lemma store_char_array_split: forall x n m l,
  0 <= n < m ->
  store_char_array x m l |-- store_char (x + n * sizeof(CHAR)) (Znth n l 0) ** store_char_array_missing_i_rec x n 0 m l.
Proof.
  intros.
  unfold store_char_array, store_char_array_missing_i_rec.
  sep_apply (store_array_split (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a)). entailer!.
  lia.
Qed.

Lemma store_char_array_merge: forall x n m a l,
  0 <= n < m ->
  store_char (x + n * sizeof(CHAR)) a ** store_char_array_missing_i_rec x n 0 m l |-- store_char_array x m (replace_Znth n a l).
Proof.
  intros.
  unfold store_char_array, store_char_array_missing_i_rec.
  sep_apply (store_array_merge (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a)). entailer!.
  lia.
Qed.

End CharArrayLib.

Export CharArrayLib.

End ArrayLibSig.