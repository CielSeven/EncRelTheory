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
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.

Definition zeros (n : Z) := repeat 0 (Z.to_nat n).

Lemma nth_firstn: forall {A} (l: list A) n m d,
  (n < m)%nat ->
  nth n (firstn m l) d = nth n l d.
Proof.
  intros.
  revert n m H; induction l; intros.
  + destruct n, m; reflexivity.
  + destruct n, m; try lia.
    - simpl. reflexivity.
    - simpl. apply IHl. lia.
Qed.

Lemma nth_skipn:
  forall {A} i n l (d:A),
       nth i (skipn n l) d = nth (i+n) l d.
Proof.
  intros.
  revert i l; induction n; simpl; intros.
  + f_equal; lia.
  + destruct l; auto.
    destruct i; simpl; auto.
    rewrite IHn.
    replace (i + S n)%nat with (S (i + n))%nat by lia; auto.
Qed.

Lemma skipn_firstn: forall {A} n m (xs: list A),
  skipn n (firstn m xs) = firstn (m-n) (skipn n xs).
Proof.
  intros.
  revert xs n; induction m; intros.
  + simpl. destruct n; reflexivity.
  + destruct xs; simpl.
    - rewrite skipn_nil.
      destruct match n with
               | O => S m
               | S l => (m - l)%nat
               end; reflexivity.
    - destruct n.
      * simpl. reflexivity.
      * simpl. apply IHm.
Qed.

Lemma firstn_firstn: forall {A} (contents: list A) n m,
  (n <= m)%nat ->
  firstn n (firstn m contents) = firstn n contents.
Proof.
  intros.
  revert n m H;
  induction contents;
  intros.
  + destruct n, m; reflexivity.
  + destruct n, m; try solve [lia].
    - simpl; reflexivity.
    - simpl; reflexivity.
    - simpl.
      rewrite IHcontents by lia.
      reflexivity.
Qed.

Lemma skipn_skipn: forall {A} n m (xs: list A),
  skipn n (skipn m xs) = skipn (m + n) xs.
Proof.
  intros.
  revert xs; induction m; intros.
  + reflexivity.
  + simpl.
    destruct xs.
    - destruct n; reflexivity.
    - apply IHm.
Qed.

Definition Znth {A} (n: Z) (l: list A) (a0: A): A := nth (Z.to_nat n) l a0.

Fixpoint replace_nth {A: Type} (n: nat) (a: A) (l: list A): list A :=
  match l with
  | nil => nil
  | a0 :: l0 =>
      match n with
      | O => a :: l0
      | S n0 => a0 :: replace_nth n0 a l0
      end
  end.

Definition replace_Znth {A} (n: Z) (a: A) (l: list A): list A :=
  replace_nth (Z.to_nat n) a l.

Lemma Znth0_cons: forall {A} (a: A) l a0,
  Znth 0 (a :: l) a0 = a.
Proof.
  intros.
  unfold Znth.
  simpl.
  reflexivity.
Qed.

Lemma Znth_cons: forall {A} n (a: A) l a0,
  n > 0 ->
  Znth n (a :: l) a0 = Znth (n - 1) l a0.
Proof.
  intros.
  unfold Znth.
  assert (Z.to_nat n = S (Z.to_nat (n - 1))) by lia.
  rewrite H0.
  simpl.
  reflexivity.
Qed.

Lemma replace_Znth_cons: forall {A} n (a b: A) l,
  n > 0 ->
  replace_Znth n a (b :: l) =
  b :: replace_Znth (n - 1) a l.
Proof.
  intros.
  unfold replace_Znth.
  assert (Z.to_nat n = S (Z.to_nat (n - 1))) by lia.
  rewrite H0.
  simpl.
  reflexivity.
Qed.

Lemma replace_nth_app_l : forall {A} n (a: A) l1 l2,
  (n < length l1)%nat ->
  replace_nth n a (l1 ++ l2) = replace_nth n a l1 ++ l2.
Proof.
  intros.
  revert dependent l1.
  revert l2.
  induction n.
  + intros.
    destruct l1; simpl in *; try lia.
    simpl.
    reflexivity.
  + intros.
    destruct l1; simpl in *; try lia.
    simpl.
    f_equal.
    apply IHn.
    lia. 
Qed. 

Lemma replace_nth_app_r: forall {A} n (a: A) l1 l2,
  (n >= length l1)%nat ->
  replace_nth n a (l1 ++ l2) = replace_nth n a l1 ++ replace_nth (n - length l1) a l2.
Proof.
  intros.
  revert dependent l1.
  revert l2.
  induction n; intros.
  + destruct l1; simpl in *; try lia.
    simpl.
    reflexivity.
  + destruct l1; simpl in *; [ | rewrite IHn ; auto; try lia].
    reflexivity. 
Qed. 

Lemma replace_Znth_app_l : forall {A} n (a: A) l1 l2,
  (0 <= n) -> 
  (n < Zlength l1) ->
  replace_Znth n a (l1 ++ l2) = replace_Znth n a l1 ++ l2.
Proof.
  intros.
  unfold replace_Znth.
  apply replace_nth_app_l.
  rewrite Zlength_correct in H0.
  lia.
Qed. 

Lemma replace_Znth_app_r : forall {A} n (a: A) l1 l2,
  (n >= Zlength l1) ->
  replace_Znth n a (l1 ++ l2) = replace_Znth n a l1 ++ replace_Znth (n - Zlength l1) a l2.
Proof. 
  intros.
  unfold replace_Znth.
  rewrite Zlength_correct in *.
  replace (Z.to_nat (n - Z.of_nat (length l1))) with (Z.to_nat n - length l1)%nat by lia.
  rewrite replace_nth_app_r ; try lia.
  auto.
Qed.

Lemma replace_Znth_Znth: forall {A} n l (a0: A),
  replace_Znth n (Znth n l a0) l = l.
Proof.
  intros.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat n); clearbody m; clear n.
  revert m; induction l; simpl; intros.
  + destruct m; reflexivity.
  + destruct m.
    - reflexivity.
    - simpl.
      rewrite IHl.
      reflexivity.
Qed.

Lemma replace_Znth_nothing : forall {A} n (l: list A) (a: A),
  n >= Zlength l -> replace_Znth n a l = l.
Proof.
  intros.
  rewrite Zlength_correct in H.
  unfold replace_Znth.
  assert (Z.to_nat n >= length l)%nat by lia.
  clear H. 
  set (m := Z.to_nat n) in *; clearbody m ; clear n.
  revert dependent l.
  induction m; intros. 
  + destruct l; simpl in * ; auto ; lia.
  + destruct l; simpl in * ; auto.
    rewrite IHm ; auto. lia. 
Qed.

Definition sublist {A: Type} (lo hi: Z) (l: list A): list A :=
  skipn (Z.to_nat lo) (firstn (Z.to_nat hi) l).

Lemma sublist_split_app_l : forall {A : Type} lo hi (l1 l2 : list A),
  0 <= lo <= hi -> hi <= Z.of_nat (length l1) -> sublist lo hi (l1 ++ l2) = sublist lo hi l1.
Proof.
  intros.
  unfold sublist.
  rewrite firstn_app.
  simpl. 
  replace (Z.to_nat hi - length l1)%nat with O by lia.
  rewrite app_nil_r. auto. 
Qed. 

Lemma sublist_single : forall {A : Type} n (l : list A) (a : A),
  0 <= n < Z.of_nat (length l) -> sublist n (n + 1) l = [Znth n l a].
Proof.
  intros.
  rewrite (list_split_nth _ (Z.to_nat n) l a) at 1; try lia.
  unfold Znth. 
  unfold sublist.
  rewrite firstn_app.
  assert (length (firstn (Z.to_nat n) l) = Z.to_nat n) by (rewrite firstn_length; lia).
  rewrite firstn_all2; try lia. 
  replace (Z.to_nat (n + 1) - length (firstn (Z.to_nat n) l))%nat with 1%nat by lia.
  rewrite skipn_app.
  replace (Z.to_nat n - length (firstn (Z.to_nat n) l))%nat with 0%nat by lia.
  rewrite skipn_all2; try lia.
  simpl. reflexivity.
Qed. 

Lemma sublist_split: forall {A : Type} lo hi mid (l : list A),
  0 <= lo <= mid -> mid <= hi <= Z.of_nat (length l) ->
  sublist lo hi l = sublist lo mid l ++ sublist mid hi l.
Proof.
  intros.
  rewrite <- (firstn_skipn (Z.to_nat hi) l).
  remember (firstn (Z.to_nat hi) l) as l1.
  remember (skipn (Z.to_nat hi) l) as l2.
  assert (Z.of_nat (length l1) = hi).
  {
    rewrite Heql1.
    rewrite firstn_length.
    lia.
  }
  assert (length l = length l1 + length l2)%nat.
  {
    rewrite Heql1, Heql2.
    rewrite firstn_length, skipn_length.
    lia.
  }
  rewrite H2 in H0.
  clear Heql1 Heql2 H2 l.
  do 3 (rewrite sublist_split_app_l ; try lia).
  unfold sublist.
  replace (Z.to_nat hi)%nat with (length l1) by lia.
  assert (mid <= Z.of_nat (length l1)) by lia.
  clear H0 H1 l2 hi.
  rewrite firstn_all2 ; try lia.
  rename l1 into l. 
  rewrite <- (firstn_skipn (Z.to_nat lo) l).
  remember (firstn (Z.to_nat lo) l) as l1.
  remember (skipn (Z.to_nat lo) l) as l2.
  assert (Z.of_nat (length l1) = lo).
  {
    rewrite Heql1.
    rewrite firstn_length.
    lia.
  }
  rewrite firstn_app.
  do 3 rewrite skipn_app.
  rewrite firstn_all2 ; try lia.
  replace (Z.to_nat lo - length l1)%nat with O by lia.
  simpl.
  do 2 (rewrite skipn_all2 ; try lia).
  rewrite! app_nil_l.
  rewrite firstn_skipn.
  reflexivity.
Qed.

Lemma Zlength_nonneg:
 forall {A} (l: list A), 0 <= Zlength l.
Proof.
  intros. rewrite Zlength_correct. lia.
Qed.

Lemma Zlength_app: forall {A} (l1 l2: list A),
  Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof.
  intros.
  rewrite !Zlength_correct.
  rewrite app_length.
  lia.
Qed.

Lemma app_Znth1:
  forall A (l l': list A) (i:Z) (d: A),
  0 <= i < Zlength l -> Znth i (l++l') d = Znth i l d.
Proof.
  intros.
  unfold Znth.
  assert (Z.to_nat i < length l)%nat by (pose proof Zlength_correct l; lia).
  set (j := Z.to_nat i) in *; clearbody j; clear i H.
  apply app_nth1; auto.
Qed.

Lemma app_Znth2:
  forall A (l l': list A) (i:Z) (d: A),
  i >= Zlength l -> Znth i (l++l') d = Znth (i-Zlength l) l' d.
Proof.
  intros.
  unfold Znth.
  pose proof (Zlength_nonneg l).
  assert (Z.to_nat i >= length l)%nat by
    (pose proof Zlength_correct l; lia).
  replace (Z.to_nat (i - Zlength l)) with (Z.to_nat i - length l)%nat
    by (pose proof Zlength_correct l; lia).
  apply app_nth2; auto.
Qed.

Lemma Znth_sublist:
  forall {A} lo i hi (l: list A) (d: A),
  0 <= lo ->
  0 <= i < hi-lo ->
  Znth i (sublist lo hi l) d = Znth (i+lo) l d.
Proof.
  intros.
  unfold sublist, Znth.
  rewrite nth_skipn.
  rewrite nth_firstn by lia.
  f_equal.
  lia.
Qed.

Lemma Znth_sublist0:
  forall {A} i hi (l: list A) (d: A),
    0 <= i < hi ->
    Znth i (sublist 0 hi l) d = Znth i l d.
Proof.
  intros.
  rewrite Znth_sublist by lia.
  f_equal.
  lia.
Qed.

Lemma Znth_indep:
  forall {A} (l : list A) n (d d' : A),
    0 <= n < Zlength l ->
    Znth n l d = Znth n l d'.
Proof.
  intros.
  unfold Znth.
  apply nth_indep.
  pose proof Zlength_correct l.
  lia.
Qed.

Lemma Zlength_sublist:
  forall {A} lo hi (l: list A),
    0 <= lo <= hi /\ hi <= Zlength l ->
    Zlength (sublist lo hi l) = hi-lo.
Proof.
  intros.
  pose proof Zlength_correct l.
  rewrite Zlength_correct.
  unfold sublist.
  rewrite skipn_length.
  rewrite firstn_length_le by lia.
  lia.
Qed.

Lemma Zlength_sublist0:
  forall {A} hi (l: list A),
    0 <= hi /\ hi <= Zlength l ->
    Zlength (sublist 0 hi l) = hi.
Proof.
  intros.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma sublist_sublist {A} i j k m (l:list A): 0<=m -> 0<=k <=i -> i <= j-m ->
  sublist k i (sublist m j l) = sublist (k+m) (i+m) l.
Proof.
  intros.
  unfold sublist.
  rewrite ! skipn_firstn.
  rewrite firstn_firstn by lia.
  rewrite skipn_skipn.
  f_equal; [lia | ].
  f_equal; lia.
Qed.

Lemma sublist_sublist0 {A} i j k (l:list A): 0<=k -> k<=i<=j ->
  sublist k i (sublist 0 j l) = sublist k i l.
Proof. intros. rewrite sublist_sublist; repeat rewrite Zplus_0_r; trivial; lia. Qed.

Lemma sublist_sublist00 {A} i j (l:list A): 0<=i<=j ->
  sublist 0 i (sublist 0 j l) = sublist 0 i l.
Proof. intros. apply sublist_sublist0; lia. Qed.

Lemma sublist_app_exact1 {A} (l1 l2: list A):
  sublist 0 (Zlength l1) (l1 ++ l2) = l1.
Proof.
  unfold sublist.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  replace (length l1) with (length l1 + O)%nat by lia.
  rewrite (firstn_app_2 O).
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Definition sum (l: list Z): Z :=
  fold_right Z.add 0 l.

Lemma sum_app: forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
Proof.  
  intros.
  revert l2.
  induction l1 ; simpl; intros ; auto.
  rewrite IHl1.
  lia.
Qed.

Lemma sum_bound : forall b l, (forall i, 0 <= i -> 0 <= Znth i l 0 <= b) -> 0 <= sum l <= Z.of_nat (length l) * b.
Proof.
  intros.
  revert H; induction l; intros ; simpl in * ; try lia.
  assert (forall i, 0 <= i -> 0 <= Znth i l 0 <= b). 
  {
    intros.
    specialize (H (i + 1)). unfold Znth in *.
    replace (Z.to_nat (i + 1)) with (length ([a]) + Z.to_nat i)%nat in H by (simpl ; lia).
    replace (a :: l) with ([a] ++ l) in H by auto.
    rewrite app_nth2_plus in H. lia.
  }
  pose proof (IHl H0).
  assert (0 <= a <= b) by (apply (H 0); simpl ; lia).
  destruct b ; lia.
Qed. 
  
Lemma sum_bound_lt : forall b l, l <> [] -> (forall i, 0 <= i < Z.of_nat (length l) -> 0 <= Znth i l 0 < b) -> 0 <= sum l < Z.of_nat (length l) * b.
Proof.
  intros.
  revert H H0; induction l; intros ; simpl in * ; try lia.
  + contradiction.
  + assert (pureH : 0 <= a < b).
    {
      assert (0 <= 0 < Z.pos (Pos.of_succ_nat (length l))) by lia. simpl in *.
      specialize (H0 0 H1). unfold Znth in H0. simpl in H0.
      lia.
    }
    assert (forall i, 0 <= i < Z.of_nat (length l) -> 0 <= Znth i l 0 < b). 
    {
      intros.
      specialize (H0 (i + 1)). unfold Znth in *.
      replace (Z.to_nat (i + 1)) with (length ([a]) + Z.to_nat i)%nat in H0 by (simpl ; lia).
      replace (a :: l) with ([a] ++ l) in H0 by auto.
      rewrite app_nth2_plus in H0. lia.
    }
    destruct l ; simpl in *.
    * destruct b ; lia. 
    * assert (z :: l <> []).
      { intro. inversion H2. }
        pose proof (IHl H2 H1).
      destruct b ; lia.
Qed. 


Lemma sublist_length : forall {A : Type} lo hi (l : list A),
  0 <= lo <= hi -> hi <= Z.of_nat (length l) -> length (sublist lo hi l) = Z.to_nat (hi - lo).
Proof.
  intros.
  unfold sublist.
  rewrite skipn_length, firstn_length.
  lia.
Qed.

Lemma Znth_sublist_lt : forall {A : Type} lo hi (l : list A) i a0,
  0 <= lo <= hi -> hi <= Z.of_nat (length l) -> 0 <= i < hi - lo -> Znth i (sublist lo hi l) a0 = Znth (lo + i) l a0.
Proof. 
  intros. unfold Znth.
  pose proof (firstn_skipn (Z.to_nat lo) l).
  rewrite <- H2 at 2.
  replace (Z.to_nat (lo + i)) with (length (firstn (Z.to_nat lo) l) + Z.to_nat i)%nat by (rewrite firstn_length ; lia).
  rewrite app_nth2_plus.
  replace (skipn (Z.to_nat lo) l) with (sublist lo hi l ++ sublist hi (Z.of_nat (length l)) l) .
  - rewrite app_nth1 ; auto. 
    rewrite sublist_length ; try lia.
  - replace (skipn (Z.to_nat lo) l) with (sublist lo (Z.of_nat (length l)) l).
    + rewrite <- sublist_split ; auto ; lia. 
    + unfold sublist. rewrite firstn_all2 ; auto. lia.
Qed.

Lemma Znth_sublist_ge : forall {A : Type} lo hi (l : list A) i a0,
  0 <= lo <= hi -> hi <= Z.of_nat (length l) -> hi - lo <= i -> Znth i (sublist lo hi l) a0 = a0.
Proof.
  intros. unfold Znth.
  rewrite nth_overflow ; auto.
  rewrite sublist_length ; lia.
Qed.

Lemma list_eq_ext: forall {A: Type} d (l1 l2: list A),
  l1 = l2 <->
  (Zlength l1 = Zlength l2 /\
   forall i, 0 <= i < Zlength l1 -> Znth i l1 d = Znth i l2 d).
Proof.
  intros.
  split; [intros; subst; auto |].
  intros [? ?].
  revert l2 H H0; induction l1; simpl; intros.
  + destruct l2.
    - reflexivity.
    - rewrite Zlength_cons in H.
      rewrite Zlength_nil in H.
      pose proof Zlength_nonneg l2.
      lia.
  + destruct l2.
    - rewrite Zlength_cons in H.
      rewrite Zlength_nil in H.
      pose proof Zlength_nonneg l1.
      lia.
    - rewrite !Zlength_cons in H.
      specialize (IHl1 l2 ltac:(lia)).
      pose proof Zlength_nonneg l1.
      rewrite Zlength_cons in H0.
      pose proof H0 0 ltac:(lia).
      rewrite !Znth0_cons in H2.
      subst a0.
      f_equal.
      apply IHl1.
      intros.
      specialize (H0 (i + 1) ltac:(lia)).
      rewrite !Znth_cons in H0 by lia.
      replace (i + 1 - 1) with i in H0 by lia.
      tauto.
Qed.

Lemma list_snoc_destruct: forall {A: Type} (l: list A),
  l = nil \/
  exists a l', l = l' ++ [a].
Proof.
  intros.
  revert l; apply rev_ind.
  + left; reflexivity.
  + intros.
    right.
    eauto.
Qed.

Lemma sublist_nil {A: Type}:
  forall (l : list A) a b,
    b <= a -> sublist a b l = [].
Proof.
  intros. unfold sublist.
  apply skipn_all2.
  rewrite firstn_length; lia.
Qed.

Lemma sublist_of_nil {A: Type}:
  forall i j,
    sublist i j (@nil A) = [].
Proof.
  intros. unfold sublist.
  rewrite firstn_nil, skipn_nil. auto.
Qed.

Lemma sublist_self {A: Type}:
  forall (l1: list A) x,
    x = Zlength l1 ->
    sublist 0 x l1 = l1.
Proof.
  intros. unfold sublist; subst.
  rewrite skipn_O. rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length l1))) with (length l1) by lia.
  apply firstn_all.
Qed.

Lemma Zlength_sublist' {A: Type}:
  forall (l: list A) i j,
    Zlength (sublist i j l) = 
    Z.of_nat (min (Z.to_nat j) (length l) - Z.to_nat i).
Proof.
  intros.
  rewrite Zlength_correct.
  unfold sublist.
  rewrite skipn_length.
  rewrite firstn_length.
  reflexivity.
Qed.

Lemma sublist_split_app_r {A: Type}:
  forall lo hi len (l1 l2: list A),
    Zlength l1 = len ->
    len <= lo <= hi ->
    sublist lo hi (l1 ++ l2) = sublist (lo - len) (hi - len) l2.
Proof.
  intros.
  unfold sublist.
  repeat rewrite skipn_firstn.
  rewrite skipn_app.
  pose proof (skipn_length (Z.to_nat lo) l1).
  rewrite Zlength_correct in H.
  replace (length l1 - Z.to_nat lo)%nat with O in H1 by lia.
  rewrite length_zero_iff_nil in H1; rewrite H1.
  simpl.
  replace (Z.to_nat (hi - len) - Z.to_nat (lo - len))%nat with (Z.to_nat hi - Z.to_nat lo)%nat by lia.
  replace (Z.to_nat lo - Datatypes.length l1)%nat with (Z.to_nat (lo - len)) by lia.
  auto.
Qed.

Lemma sublist_cons1 {A: Type}:
  forall n a (l: list A),
    1 <= n -> sublist 0 n (a::l) = a :: (sublist 0 (n-1) l).
Proof.
  intros.
  unfold sublist.
  repeat rewrite skipn_firstn.
  repeat rewrite skipn_O.
  replace (Z.to_nat n - Z.to_nat 0)%nat with (S(Z.to_nat (n - 1) - Z.to_nat 0)) by lia.
  apply firstn_cons.
Qed.

Lemma sublist_cons2 {A: Type}:
  forall m n a (l: list A),
    1 <= m <= n -> n  <= Zlength (a::l) ->
    sublist m n (a::l) = sublist (m-1) (n-1) l.
Proof.
  intros.
  unfold sublist.
  repeat rewrite skipn_firstn.
  replace (Z.to_nat m) with (S (Z.to_nat (m - 1))) at 2 by lia.
  rewrite skipn_cons.
  replace (Z.to_nat (n - 1) - Z.to_nat (m - 1))%nat with (Z.to_nat n - Z.to_nat m)%nat by lia.
  reflexivity.
Qed.

Inductive interval_list (pace lo hi : Z): list Z -> Prop :=
  | interval_list_nil: interval_list pace lo hi []
  | interval_list_cons: forall l x,
      interval_list pace lo hi l ->
      lo <= x -> x + pace <= hi -> 
      Forall (fun x' => x + pace < x' \/ x' + pace < x) l ->
      interval_list pace lo hi (x :: l).

Theorem interval_list_valid1:  forall l pace lo hi , interval_list pace lo hi l -> pace > 0 ->
  Forall (fun x => lo <= x < hi) l.
Proof.
  intros.
  induction H; simpl; auto.
  constructor; auto. lia.
Qed.

Theorem interval_list_valid2:  forall l pace lo hi , interval_list pace lo hi l -> pace > 0 -> NoDup l.
Proof.
  intros.
  induction H; simpl; constructor; auto.
  rewrite Forall_forall in H3.
  intro. 
  apply H3 in H4.
  lia. 
Qed.

Theorem interval_list_valid3:  forall l pace lo hi , interval_list pace lo hi l -> Forall (fun x => lo <= x /\ x + pace <= hi) l.
Proof.
  intros.
  induction H; simpl; constructor; auto.
Qed.

Definition Zlist_max (l: list Z) (lo : Z) : Z :=
  fold_right Z.max lo l.

Theorem interval_perm_keep: forall l l1 pace lo hi, interval_list pace lo hi l -> Permutation l l1 -> interval_list pace lo hi l1.
Proof.
  intros.
  induction H0; auto.
  - inversion H; subst.
    constructor; auto.
    rewrite <- H0. auto.
  - pose proof (interval_list_valid3 _ _ _ _ H).
    assert (Permutation (x :: y :: l) (y :: x :: l)).
    { constructor; auto. }
    rewrite <- H1 in H0.
    inversion H0. subst.
    inversion H ; subst.
    inversion H5 ; subst.
    inversion H6 ; subst.
    inversion H9 ; subst.
    constructor ; auto ; try lia.
    + constructor ; auto ; try lia.
    + constructor ; auto ; try lia.
Qed.

Inductive increasing : list Z -> Prop :=
  | increasing_nil: increasing []
  | increasing_cons: forall x l',
      increasing l' ->
      Forall (fun x' => x <= x') l' ->
      increasing (x :: l').

Fixpoint list_insert (i : Z) (l : list Z) :=
  match l with
  | [] => [i]
  | h :: t => if Z_le_gt_dec i h then i :: h :: t else h :: list_insert i t
  end.

Fixpoint sort (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => list_insert h (sort t)
  end.      

Lemma list_insert_In : forall x a l, In x (list_insert a l) <-> In x l \/ x = a.
Proof.
  intros.
  induction l; simpl in * ; split ; intros.
  - destruct H ; auto.
  - destruct H ; auto.
  - destruct (Z_le_gt_dec a a0).
    + destruct H ; auto.
    + destruct H ; auto. rewrite IHl in H.
      destruct H ; auto.
  - destruct (Z_le_gt_dec a a0) ; simpl.
    + destruct H as [ [? | ?] | ?]; auto.
    + rewrite IHl. 
      destruct H as [[? |?] | ?] ; auto.
Qed. 

Theorem sort_list_increasing : forall l, increasing (sort l).
Proof.
  intros.
  induction l ; simpl in *; auto.
  - constructor.
  - remember (sort l) as l1.
    clear Heql1 l. rename l1 into l. 
    induction l; simpl in * ; auto.
    + constructor ; auto.
    + destruct (Z_le_gt_dec a a0).
      * constructor ; auto.
        inversion IHl ; subst.
        constructor ; auto.
        rewrite Forall_forall in *.
        intros.
        specialize (H2 _ H).
        lia.
      * inversion IHl ; subst.
        constructor ; auto.
        rewrite Forall_forall in *.
        intros.
        rewrite list_insert_In in H.
        destruct H ; auto.
        lia.
Qed.

Lemma list_insert_perm : forall x l, Permutation (x :: l) (list_insert x l).
Proof.
  intros.
  induction l; simpl in * ; auto.
  destruct (Z_le_gt_dec x a).
  - constructor ; auto.
  - rewrite perm_swap. constructor ; auto.
Qed.

Theorem sort_list_perm : forall l, Permutation l (sort l).
Proof.
  intros.
  induction l ; simpl in * ; auto.
  apply perm_trans with (l' := a :: sort l) ; auto.
  apply list_insert_perm.
Qed.

Lemma interval_list_compress : forall l pace lo1 hi1 lo2 hi2, interval_list pace lo1 hi1 l -> lo1 <= lo2 -> hi2 <= hi1 -> 
  Forall (fun x => lo2 <= x /\ x + pace <= hi2) l -> interval_list pace lo2 hi2 l.
Proof.
  intros.
  revert dependent lo2. revert dependent hi2.
  induction H; intros ; simpl.
  - constructor.
  - constructor ; auto.
    + apply IHinterval_list ; auto.
      inversion H5 ; auto.
    + inversion H5 ; lia.
    + inversion H5 ; lia.
Qed.   

Theorem increasing_interval_list_range : forall l pace lo hi, pace > 0 ->
lo <= hi -> 
interval_list pace lo hi l -> increasing l ->
lo + (Zlength l) * (pace + 1) <= hi + pace + 1.
Proof.
  intros. revert dependent lo. 
  induction l; simpl ; intros; auto.
  - lia.
  - inversion H2 ; subst.
    inversion H1 ; subst.
    apply Zle_lt_or_eq in H9.
    destruct H9.
    + specialize (IHl H5 (a + pace + 1) (ltac:(lia))).
      rewrite Zlength_cons.
      assert (interval_list pace (a + pace + 1) hi l).
      {  
        apply interval_list_compress with (lo1 := lo) (hi1 := hi) ; auto ; try lia.
        pose proof (interval_list_valid3 _ _ _ _ H7).
        rewrite Forall_forall in *.
        intros. 
        specialize (H10 _ H9).
        specialize (H4 _ H9).
        specialize (H6 _ H9).
        lia. 
      }
      specialize (IHl H4).
      lia.
    + destruct l. 
      * replace (Zlength [a]) with 1 by auto.
        lia.
      * exfalso. 
        inversion H7; subst.
        inversion H10; subst.
        inversion H6 ; subst.
        lia.
Qed.

Theorem interval_list_range : forall l pace lo hi, pace > 0 ->
lo <= hi -> 
interval_list pace lo hi l -> 
lo + (Zlength l) * (pace + 1) <= hi + pace + 1.
Proof.
  intros.
  pose proof (sort_list_perm l).
  assert (Zlength l = Zlength (sort l)).
  {
     rewrite !Zlength_correct.
     rewrite (Permutation_length H2) ; auto.
  }
  rewrite H3.
  apply (increasing_interval_list_range (sort l) pace lo hi) ; auto.
  + apply (interval_perm_keep l) ; auto.
  + apply sort_list_increasing.
Qed. 
    

  
