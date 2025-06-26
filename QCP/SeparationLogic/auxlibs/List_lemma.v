Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.

Inductive Forall2 {A B : Type} (P : A -> B -> Prop) : list A -> list B -> Prop :=
  | Forall2_nil : Forall2 P nil nil
  | Forall2_cons : forall a b la lb,
    P a b -> Forall2 P la lb -> Forall2 P (a :: la) (b :: lb)
.

Lemma Forall2_split : forall (A B : Type)
  (P : A -> B -> Prop) (n : nat) xs ys,
  Forall2 P xs ys ->
  Forall2 P (firstn n xs) (firstn n ys) /\
  Forall2 P (skipn n xs) (skipn n ys).
Proof.
  induction n; intros; simpl.
  - split.
    + constructor.
    + auto.
  - destruct xs; destruct ys; simpl in *; inversion H.
    + split; constructor.
    + destruct (IHn _ _ H5). split.
      * constructor; auto.
      * auto.
Qed.

Lemma Forall2_split_app1 : forall (A B : Type)
  (P : A -> B -> Prop) xs1 xs2 ys,
  Forall2 P (xs1 ++ xs2) ys ->
  exists ys1 ys2,
  ys = ys1 ++ ys2 /\ Forall2 P xs1 ys1 /\ Forall2 P xs2 ys2.
Proof.
  intros. pose proof (Forall2_split _ _ _ (length xs1) _ _ H).
  destruct H0.
  rewrite firstn_app in H0. rewrite firstn_all in H0.
  rewrite skipn_app in H1. rewrite skipn_all in H1.
  replace (length xs1 - length xs1) with 0 in * by lia.
  simpl in *. rewrite app_nil_r in H0.
  exists (firstn (length xs1) ys), (skipn (length xs1) ys).
  intuition.
  rewrite firstn_skipn. auto.
Qed.

Lemma Forall2_split_app2 : forall (A B : Type)
  (P : A -> B -> Prop) xs ys1 ys2,
  Forall2 P xs (ys1 ++ ys2) ->
  exists xs1 xs2,
  xs = xs1 ++ xs2 /\ Forall2 P xs1 ys1 /\ Forall2 P xs2 ys2.
Proof.
  intros. pose proof (Forall2_split _ _ _ (length ys1) _ _ H).
  destruct H0.
  rewrite firstn_app in H0. rewrite firstn_all in H0.
  rewrite skipn_app in H1. rewrite skipn_all in H1.
  replace (length ys1 - length ys1) with 0 in * by lia.
  simpl in *. rewrite app_nil_r in H0.
  exists (firstn (length ys1) xs), (skipn (length ys1) xs).
  intuition.
  rewrite firstn_skipn. auto.
Qed.

Lemma Forall2_merge : forall (A B : Type) (P : A -> B -> Prop) xs1 ys1 xs2 ys2,
  Forall2 P xs1 ys1 ->
  Forall2 P xs2 ys2 ->
  Forall2 P (xs1 ++ xs2) (ys1 ++ ys2).
Proof.
  induction xs1; intros; destruct ys1; simpl.
  - auto.
  - inversion H.
  - inversion H.
  - inversion H. subst. constructor; auto.
Qed.

Lemma list_split_nth : forall (A : Type) (n : nat) (l : list A) (d : A),
  n < length l ->
  l = firstn n l ++ nth n l d :: skipn (S n) l.
Proof.
  induction n; intros.
  - destruct l; simpl in *; try lia. auto.
  - destruct l; simpl in *; try lia.
    f_equal. assert (n < length l) by lia.
    apply IHn. auto.
Qed.

Arguments list_split_nth _ n%nat.

Lemma Forall2_length : forall (A B : Type) (P : A -> B -> Prop) xs ys,
  Forall2 P xs ys ->
  length xs = length ys.
Proof.
  intros. induction H; simpl.
  - auto.
  - lia.
Qed.

Lemma Forall2_nth_iff : forall (A B : Type)
  (P : A -> B -> Prop) xs ys dx dy,
  Forall2 P xs ys <->
  (length xs = length ys /\
   forall n, n < length xs ->
     P (nth n xs dx) (nth n ys dy)).
Proof.
  intros. split; intros.
  - split. apply (Forall2_length _ _ _ _ _ H).
    intros.
    assert (n < length ys).
    { rewrite <- (Forall2_length _ _ _ _ _ H); auto. }
    rewrite (list_split_nth _ n xs dx H0) in H.
    rewrite (list_split_nth _ n ys dy H1) in H.
    apply (Forall2_split _ _ _ n) in H.
    destruct H as [_ ?].
    rewrite ! skipn_app in H.
    assert (n = length (firstn n xs)).
    { rewrite firstn_length. rewrite min_l; auto. lia. }
    assert (skipn n (firstn n xs) = nil).
    { transitivity (skipn (length (firstn n xs)) (firstn n xs)).
      - congruence.
      - apply skipn_all. }
    assert (n = length (firstn n ys)).
    { rewrite firstn_length. rewrite min_l; auto. lia. }
    assert (skipn n (firstn n ys) = nil).
    { transitivity (skipn (length (firstn n ys)) (firstn n ys)).
      - congruence.
      - apply skipn_all. }
    rewrite H3 in H. rewrite H5 in H. simpl in H.
    replace (n - length (firstn n xs)) with O in H by lia.
    replace (n - length (firstn n ys)) with O in H by lia.
    simpl in H. inversion H. auto.
  - destruct H. generalize dependent ys.
    induction xs; intros; destruct ys; simpl in *; try lia.
    + constructor.
    + constructor.
      * specialize (H0 O). apply H0. lia.
      * apply IHxs; auto.
        intros. apply (H0 (S n)). lia.
Qed.

Lemma Forall2_app : forall (A B : Type)
  (P : A -> B -> Prop) xs1 xs2 ys1 ys2,
  Forall2 P xs1 ys1 ->
  Forall2 P xs2 ys2 ->
  Forall2 P (xs1 ++ xs2) (ys1 ++ ys2).
Proof.
  induction xs1; intros; destruct ys1; simpl; auto.
  - inversion H.
  - inversion H.
  - inversion H. subst. constructor; auto.
Qed.

Lemma Forall2_congr : forall (A B : Type) (p p' : A -> B -> Prop) xs ys,
  (forall x y, In x xs -> In y ys -> p x y -> p' x y) ->
  Forall2 p xs ys ->
  Forall2 p' xs ys.
Proof.
  intros. induction H0.
  - constructor.
  - constructor.
    + apply H; auto.
      * left. auto.
      * left. auto.
    + apply IHForall2. intros.
      apply H; auto.
      * right. auto.
      * right. auto.
Qed.

Definition nperm (s : list nat) : Prop := Permutation (seq O (length s)) s.

Definition do_nperm {A : Type} (s : list nat) (l : list A) (d : A) : list A :=
  map (fun n => nth n l d) s.

Definition trivial_nperm (n : nat) := seq O n.

Lemma trivial_nperm_nperm : forall n, nperm (trivial_nperm n).
Proof.
  intros. unfold nperm, trivial_nperm.
  rewrite seq_length.
  apply Permutation_refl.
Qed.

Lemma trivial_nperm_refl : forall (A : Type) (n : nat) (l : list A) (d : A),
  length l = n ->
  do_nperm (trivial_nperm n) l d = l.
Proof.
  unfold do_nperm. induction n; simpl; intros.
  - destruct l; auto. simpl in H. lia.
  - destruct l; simpl in *; try lia.
    inversion H. subst. f_equal.
    rewrite <- seq_shift. rewrite map_map. auto.
Qed.

Fixpoint find_index (l : list nat) (n : nat) : nat :=
  match l with
  | nil => O
  | n' :: l' =>
    if (n' =? n)%nat
    then O
    else S (find_index l' n)
  end.

Lemma find_index_nth : forall l n d,
  NoDup l ->
  n < length l ->
  find_index l (nth n l d) = n.
Proof.
  intros. generalize dependent l.
  induction n; intros; destruct l; simpl in *; auto; try lia.
  - rewrite Nat.eqb_refl. auto.
  - inversion H. subst.
    assert (n < length l) by lia.
    rewrite (IHn _ H4 H1).
    destruct (n0 =? nth n l d) eqn:E; auto.
    rewrite Nat.eqb_eq in E. subst.
    contradict H3.
    apply (nth_In l d H1).
Qed.

Lemma nth_find_index : forall l n d,
  In n l ->
  nth (find_index l n) l d = n.
Proof.
  intros. generalize dependent n.
  induction l; intros; simpl in *.
  - contradiction.
  - destruct (a =? n) eqn:E.
    + rewrite Nat.eqb_eq in E. auto.
    + rewrite Nat.eqb_neq in E. destruct H; try congruence.
      apply IHl. auto.
Qed.

Lemma map_nth_len : forall (A B : Type) (f : A -> B) l n dx dy,
  n < length l ->
  nth n (map f l) dx = f (nth n l dy).
Proof.
  intros. generalize dependent l.
  induction n; intros.
  - destruct l; simpl in *; auto. lia.
  - destruct l; simpl in *; try lia.
    apply IHn. lia.
Qed.

Lemma map_find_index_same : forall l,
  NoDup l ->
  map (find_index l) l = seq O (length l).
Proof.
  intros. apply (nth_ext _ _ O O).
  - rewrite map_length. rewrite seq_length. auto.
  - intros. rewrite map_length in H0.
    rewrite seq_nth; auto. simpl.
    rewrite (map_nth_len _ _ _ _ _ _ O); auto.
    rewrite find_index_nth; auto.
Qed.

Lemma do_nperm_length : forall (A : Type) s (l : list A) d,
  length (do_nperm s l d) = length s.
Proof.
  intros. unfold do_nperm. rewrite map_length. auto.
Qed.

Lemma nperm_range : forall s n0 d,
  nperm s ->
  n0 < (length s) ->
  nth n0 s d < (length s).
Proof.
  intros.
  pose proof (nth_In s d H0).
  unfold nperm in H. symmetry in H.
  apply (Permutation_in _ H) in H1.
  apply in_seq in H1. simpl in *. lia.
Qed.

Lemma nperm_NoDup : forall s,
  nperm s -> NoDup s.
Proof.
  intros.
  apply (Permutation_NoDup H).
  apply seq_NoDup.
Qed.

Lemma nperm_map : forall (A B : Type) s (f : A -> B) (l : list A) dx,
  do_nperm s (map f l) (f dx) = map f (do_nperm s l dx).
Proof.
  intros. unfold do_nperm. rewrite map_map.
  apply map_ext. intros. apply map_nth.
Qed.

Lemma find_index_range : forall l n,
  In n l ->
  find_index l n < length l.
Proof.
  intros. induction l; simpl in *.
  - contradiction.
  - destruct (a =? n) eqn:E.
    + lia.
    + rewrite Nat.eqb_neq in E. destruct H; try congruence.
      specialize (IHl H). lia.
Qed.

Definition inverse_nperm (s : list nat) :=
  map (find_index s) (seq O (length s)).

Lemma inverse_nperm_nperm : forall s,
  nperm s ->
  nperm (inverse_nperm s).
Proof.
  intros. unfold inverse_nperm, nperm.
  pose proof (Permutation_map (find_index s) H).
  rewrite map_find_index_same in H0.
  - symmetry. rewrite map_length. rewrite seq_length. auto.
  - apply nperm_NoDup. auto.
Qed.

Definition inverse_nperm_compose_refl1 : forall (A : Type)
  (s : list nat) (l : list A) d,
  nperm s ->
  length l = length s ->
  do_nperm s (do_nperm (inverse_nperm s) l d) d = l.
Proof.
  intros. unfold do_nperm, inverse_nperm; simpl.
  apply (nth_ext _ _ d d).
  { rewrite map_length. auto. }
  intros. rewrite map_length in H1.
  rewrite <- H0 in H1. rewrite map_map.
  rewrite (map_nth_len _ _ _ _ n _ O) by lia.
  rewrite (map_nth_len _ _ _ _ _ _ O).
  2:{ rewrite seq_length. apply nperm_range; auto. lia. }
  rewrite seq_nth.
  2:{ apply nperm_range; auto. lia. }
  simpl. rewrite find_index_nth; auto.
  { apply nperm_NoDup. auto. }
  { lia. }
Qed.

Definition inverse_nperm_compose_refl2 : forall (A : Type)
  (s : list nat) (l : list A) d,
  nperm s ->
  length l = length s ->
  do_nperm (inverse_nperm s) (do_nperm s l d) d = l.
Proof.
  intros. unfold do_nperm, inverse_nperm; simpl.
  apply (nth_ext _ _ d d).
  { rewrite ! map_length. rewrite seq_length. auto. }
  intros. rewrite map_length in H1. rewrite map_length in H1.
  rewrite seq_length in H1.
  rewrite (map_nth_len _ _ _ _ n _ O).
  2:{ rewrite map_length. rewrite seq_length. lia. }
  rewrite (map_nth_len _ _ _ _ n _ O).
  2:{ rewrite seq_length. lia. }
  rewrite (map_nth_len _ _ _ _  _ _ O).
  2:{ rewrite seq_nth; auto. simpl.
      apply find_index_range.
      apply (Permutation_in _ H). apply in_seq. lia. }
  rewrite seq_nth by lia. simpl.
  rewrite nth_find_index; auto.
  { apply (Permutation_in _ H). apply in_seq. lia. }
Qed.

Lemma do_nperm_permutation :
  forall (A : Type) (s : list nat) (l : list A) (d : A),
  nperm s ->
  length l = length s ->
  Permutation l (do_nperm s l d).
Proof.
  intros. rewrite <- (trivial_nperm_refl _ (length l) l d) at 1; auto.
  unfold do_nperm. apply Permutation_map. rewrite H0. apply H.
Qed.

Lemma Forall2_nperm_congr0 : forall (A B : Type)
  (P : A -> B -> Prop) xs ys (s : list nat) dx dy,
  nperm s ->
  length xs = length s ->
  Forall2 P xs ys ->
  Forall2 P (do_nperm s xs dx) (do_nperm s ys dy).
Proof.
  intros * HPerm **.
  apply (Forall2_nth_iff _ _ _ _ _ dx dy) in H0.
  apply (Forall2_nth_iff _ _ _ _ _ dx dy).
  destruct H0. split.
  - rewrite ! do_nperm_length; auto.
  - intros. unfold do_nperm.
    rewrite do_nperm_length in H2; auto.
    rewrite (map_nth_len _ _ _ _ _ dx O) by lia.
    rewrite (map_nth_len _ _ _ _ _ dy O) by lia.
    apply H1; auto.
    pose proof (nperm_range s _ O HPerm H2). lia.
Qed.

Lemma Forall2_nperm_congr : forall (A B : Type)
  (P : A -> B -> Prop) xs ys (s : list nat) dx dy,
  nperm s ->
  length xs = length s ->
  length ys = length s ->
  Forall2 P xs ys <->
  Forall2 P (do_nperm s xs dx) (do_nperm s ys dy).
Proof.
  intros * HPerm **. split; intros.
  - apply Forall2_nperm_congr0; auto.
  - rewrite <- (inverse_nperm_compose_refl2 _ s xs dx HPerm H).
    rewrite <- (inverse_nperm_compose_refl2 _ s ys dy HPerm H0).
    apply Forall2_nperm_congr0; auto.
    + apply inverse_nperm_nperm. auto.
    + rewrite do_nperm_length. unfold inverse_nperm. rewrite map_length.
      rewrite seq_length. auto.
Qed.

Definition swap_nperm (n1 n2 n3 : nat) :=
  seq 0 n1 ++ 1 + n1 + n2 :: seq (1 + n1) n2 ++ n1 :: seq (2 + n1 + n2) n3.

Definition swap_nperm_nperm : forall (n1 n2 n3 : nat), nperm (swap_nperm n1 n2 n3).
Proof.
  intros. unfold nperm, swap_nperm.
  rewrite ! app_length. rewrite seq_length. simpl.
  replace (2 + n1 + n2 + n3) with (n1 + (1 + n2 + (1 + n3))) by lia.
  rewrite (seq_app n1). apply Permutation_app; [apply Permutation_refl | ].
  simpl. rewrite app_length. simpl. rewrite ! seq_length.
  rewrite (seq_app n2). simpl.
  rewrite ! (Permutation_app_comm (seq (S n1) n2)).
  simpl. apply perm_swap.
Qed.

Lemma swap_nperm_do_nperm : forall (A : Type) l1 i l2 j l3 (d : A),
  do_nperm (swap_nperm (length l1) (length l2) (length l3))
    (l1 ++ i :: l2 ++ j :: l3) d =
    (l1 ++ j :: l2 ++ i :: l3).
Proof.
  intros. unfold do_nperm, swap_nperm; simpl.
  rewrite map_app. simpl. rewrite map_app. simpl.
  f_equal.
  { apply (nth_ext _ _ d d).
    - rewrite map_length. rewrite seq_length. auto.
    - intros.
      rewrite map_length in H. rewrite seq_length in H.
      rewrite (map_nth_len _ _ _ _ _ d O); auto.
      + rewrite seq_nth; auto. simpl. apply app_nth1. auto.
      + rewrite seq_length. auto. }
  f_equal.
  { rewrite app_nth2; try lia.
    replace (S (length l1 + length l2) - length l1) with (S (length l2)) by lia.
    simpl. rewrite app_nth2; try lia.
    replace (length l2 - length l2) with 0 by lia. simpl. auto. }
  f_equal.
  { apply (nth_ext _ _ d d).
    - rewrite map_length. rewrite seq_length. auto.
    - intros.
      rewrite map_length in H. rewrite seq_length in H.
      rewrite (map_nth_len _ _ _ _ _ d O); auto.
      + rewrite seq_nth; auto. simpl. rewrite app_nth2; try lia.
        replace (S (length l1 + n) - length l1) with (S n) by lia.
        simpl. apply app_nth1. auto.
      + rewrite seq_length. auto. }
  f_equal.
  { rewrite app_nth2; try lia.
    replace (length l1 - length l1) with 0 by lia. simpl. auto. }
  { apply (nth_ext _ _ d d).
    - rewrite map_length. rewrite seq_length. auto.
    - intros.
      rewrite map_length in H. rewrite seq_length in H.
      rewrite (map_nth_len _ _ _ _ _ d O); auto.
      + rewrite seq_nth; auto. simpl. rewrite app_nth2; try lia.
        replace (S (S (length l1 + length l2 + n)) - length l1) with (2 + length l2 + n) by lia.
        simpl. rewrite app_nth2; try lia.
        replace (S (length l2 + n) - length l2) with (S n) by lia.
        simpl. auto.
      + rewrite seq_length. auto. }
Qed.

Definition list_swap_nperm (n1 n2 : nat) :=
  seq n1 n2 ++ seq 0 n1.

Definition list_swap_nperm_nperm : forall (n1 n2 : nat),
  nperm (list_swap_nperm n1 n2).
Proof.
  intros. unfold nperm, list_swap_nperm.
  rewrite app_length. rewrite ! seq_length.
  replace (n2 + n1) with (n1 + n2) by lia.
  rewrite seq_app. simpl. apply Permutation_app_comm.
Defined.

Lemma list_swap_nperm_do_nperm : forall (A : Type) l1 l2 (d : A),
  do_nperm (list_swap_nperm (length l1) (length l2))
    (l1 ++ l2) d = (l2 ++ l1).
Proof.
  intros. unfold do_nperm, list_swap_nperm; simpl.
  rewrite map_app. simpl. f_equal.
  - apply (nth_ext _ _ d d).
    { rewrite map_length. rewrite seq_length. auto. }
    intros. rewrite map_length in H. rewrite seq_length in H.
    rewrite (map_nth_len _ _ _ _ _ d 0).
    2:{ rewrite seq_length. lia. }
    rewrite seq_nth; auto. rewrite app_nth2; try lia.
    replace (length l1 + n - length l1) with n by lia.
    auto.
  - apply (nth_ext _ _ d d).
    { rewrite map_length. rewrite seq_length. auto. }
    intros. rewrite map_length in H. rewrite seq_length in H.
    rewrite (map_nth_len _ _ _ _ _ d 0).
    2:{ rewrite seq_length. lia. }
    rewrite seq_nth; auto. simpl. rewrite app_nth1; try lia.
    auto.
Qed.

Lemma Forall2_map1 : forall (A B C : Type) (P : C -> B -> Prop) xs ys (f : A -> C),
  Forall2 (fun x y => P (f x) y) xs ys <->
  Forall2 P (map f xs) ys.
Proof.
  induction xs; intros; destruct ys; simpl; split; intros.
  - constructor.
  - constructor.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
Qed.

Lemma Forall2_map2 : forall (A B C : Type) (P : A -> C -> Prop) xs ys (f : B -> C),
  Forall2 (fun x y => P x (f y)) xs ys <->
  Forall2 P xs (map f ys).
Proof.
  induction xs; intros; destruct ys; simpl; split; intros.
  - constructor.
  - constructor.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
Qed.

Lemma NoDup_map_fst : forall (A B : Type) (l : list (A * B)) x y y',
  NoDup (map fst l) ->
  In (x, y) l ->
  In (x, y') l ->
  y = y'.
Proof.
  intros. induction l; simpl in *.
  - contradiction.
  - inversion H. subst. clear H.
    destruct H0; destruct H1; subst.
    + congruence.
    + apply (in_map fst) in H0. simpl in H0. contradiction.
    + apply (in_map fst) in H. simpl in H. contradiction.
    + auto.
Qed.

Fixpoint Zseq (start : Z) (len : nat) : list Z :=
  match len with
  | 0 => nil
  | S len' => start :: Zseq (Z.succ start) len'
  end.

Lemma Zseq_length : forall s n,
  length (Zseq s n) = n.
Proof.
  intros. revert s. induction n; intros; simpl; auto.
Qed.

Fixpoint list_insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: list_insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => list_insert h (sort t)
  end.

Lemma list_insert_perm: forall x l,
    Permutation (x :: l) (list_insert x l).
Proof.
  intros x l. induction l.
  - auto.
  - simpl. destruct (x <=? a) eqn:?.
    + apply Permutation_refl.
    + apply perm_trans with (a :: x :: l).
      * apply perm_swap.
      * apply perm_skip. assumption.
Qed.

Lemma sort_perm: forall l, Permutation l (sort l).
Proof.
  intros l. induction l.
  - auto.
  - simpl. apply perm_trans with (a :: (sort l)).
    + apply perm_skip. assumption.
    + apply list_insert_perm.
Qed.

Lemma sort_nperm : forall s,
  sort s = seq O (length s) ->
  nperm s.
Proof.
  intros. unfold nperm.
  rewrite <- H. symmetry. apply sort_perm.
Qed.

Definition list_update_nth {A : Type} (l : list A) (n : nat) (v : A) :=
  firstn n l ++ v :: skipn (S n) l.

Lemma list_eq_nth : forall (A : Type) (l1 l2 : list A) (d : A),
  length l1 = length l2 ->
  (forall n, n < length l1 -> nth n l1 d = nth n l2 d) ->
  l1 = l2.
Proof.
  induction l1; intros; destruct l2; simpl in *; auto; try lia.
  f_equal.
  - apply (H0 O). lia.
  - apply (IHl1 _ d).
    + lia.
    + intros. apply (H0 (S n)). lia.
Qed.

Lemma Zseq_nth : forall start len n,
  n < len ->
  (nth n (Zseq start len) 0 = start + (Z.of_nat n))%Z.
Proof.
  intros. generalize dependent len. revert start.
  induction n; intros.
  - simpl. destruct len; [lia | ]. simpl. lia.
  - destruct len; [lia | ]. simpl. rewrite IHn; lia.
Qed.

Lemma combine_skipn : forall (A B : Type) (l : list A) (l' : list B) n,
  skipn n (combine l l') = combine (skipn n l) (skipn n l').
Proof.
  intros *. revert l l'. induction n; intros; simpl.
  - auto.
  - destruct l; destruct l'; simpl in *; auto.
    rewrite combine_nil. auto.
Qed.

Lemma Zseq_firstn : forall start len n,
  (n <= len)%nat ->
  firstn n (Zseq start len) = Zseq start n.
Proof.
  intros. generalize dependent len. revert start.
  induction n; intros; simpl; auto.
  destruct len; [lia | ].
  simpl. rewrite IHn; auto. lia.
Qed.

Lemma Zseq_skipn : forall start len n,
  skipn n (Zseq start len) = Zseq (start + Z.of_nat n) (len - n).
Proof.
  intros. generalize dependent len. revert start.
  induction n; intros; simpl.
  - f_equal; lia.
  - destruct len; simpl; auto.
    rewrite IHn; auto. f_equal; lia.
Qed.


Lemma cons_length : forall (A : Type) (x : A) (l : list A),
  length (x :: l) = S (length l).
Proof.
  intros. simpl. auto.
Qed.

Lemma combine_app : forall {A B : Type} (l1 l2 : list A) (l1' l2' : list B),
  length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1; destruct l1'; simpl; intros; auto; try lia.
  f_equal. auto.
Qed.

Lemma Zseq_app : forall start len1 len2,
  Zseq start (len1 + len2) = Zseq start len1 ++ Zseq (start + (Z.of_nat len1)) len2.
Proof.
  intros start len1. revert start.
  induction len1; intros; simpl in *.
  - f_equal. lia.
  - rewrite IHlen1. f_equal. f_equal. f_equal. lia.
Qed.

Lemma forall_in_cons:
  forall {A: Type} (a: A) (l: list A) (P: A -> Prop),
    (forall a0, In a0 (a :: l) -> P a0) <->
    P a /\ (forall a0, In a0 l -> P a0).
Proof.
  intros; split; intros.
  + split.
    - exact (H _ (or_introl eq_refl)).
    - intros.
      exact (H _ (or_intror H0)).
  + destruct H0.
    - subst; tauto.
    - revert a0 H0; tauto.
Qed.

Lemma forall_in_app:
  forall {A: Type} (l1 l2: list A) (P: A -> Prop),
    (forall a, In a (l1 ++ l2) -> P a) <->
    (forall a, In a l1 -> P a) /\
    (forall a, In a l2 -> P a).
Proof.
  intros.
  induction l1; simpl app.
  + assert (forall a, False -> P a) by tauto.
    tauto.
  + rewrite !forall_in_cons.
    tauto.
Qed.

Definition prod_eq_dec {A B}
  (eq_dec1: forall a1 a2: A, {a1 = a2} + {a1 <> a2})
  (eq_dec2: forall b1 b2: B, {b1 = b2} + {b1 <> b2}):
  forall p1 p2: A * B, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [a1 b1] [a2 b2].
  destruct (eq_dec1 a1 a2), (eq_dec2 b1 b2).
  - left; congruence.
  - right; congruence.
  - right; congruence.
  - right; congruence.
Defined.

Definition list_eq_dec {A: Type} (eq_dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2}):
  forall l1 l2: list A, {l1 = l2} + {l1 <> l2}.
Proof.
  intros l1.
  induction l1; destruct l2; simpl.
  + left; auto.
  + right; congruence.
  + right; congruence.
  + destruct (eq_dec a a0), (IHl1 l2).
    - left; congruence.
    - right; congruence.
    - right; congruence.
    - right; congruence.
Defined.

Definition list_eqb {A B: Type} (eqb: A -> B -> bool) (l1 : list A) (l2 : list B): bool :=
  (fix list_eqb (l1 : list A) (l2 : list B): bool :=
    match l1, l2 with
    | nil, nil => true
    | cons a1 l1', cons a2 l2' => eqb a1 a2 && list_eqb l1' l2'
    | _, _ => false
    end) l1 l2.

Lemma list_eqb_eq_nil: forall {A B} (eqb: A -> B -> bool),
  forall l2: list B, list_eqb eqb nil l2 = true <-> nil = l2.
Proof.
  intros.
  destruct l2; simpl.
  + tauto.
  + split; intros; congruence.
Qed.

Lemma list_eqb_eq_cons: forall {A} eqb,
  forall a1 l1,
    (forall a2: A, eqb a1 a2 = true <-> a1 = a2) ->
    (forall l2: list A, list_eqb eqb l1 l2 = true <-> l1 = l2) ->
    (forall l2, list_eqb eqb (cons a1 l1) l2 = true <-> cons a1 l1 = l2).
Proof.
  intros.
  destruct l2; simpl.
  + split; intros; congruence.
  + rewrite andb_true_iff, H, H0.
    split; [intros [? ?] | intros; split]; congruence.
Qed.


Lemma list_eqb_eq {A} eqb (eqb_eq : forall a1 a2: A, eqb a1 a2 = true <-> a1 = a2):
    (forall l1 l2: list A, list_eqb eqb l1 l2 = true <-> l1 = l2).
Proof.
  intros.
  revert l2.
  induction l1.
  + apply list_eqb_eq_nil.
  + apply list_eqb_eq_cons; auto.
Qed.

Lemma list_eqb_refl {A} eqb (eqb_refl : forall a: A, eqb a a = true):
  forall (l: list A), list_eqb eqb l l = true.
Proof.
  intros.
  induction l; simpl; auto.
  rewrite (eqb_refl a), IHl. auto.
Qed.

Lemma list_eqb_true {A} eqb (eqb_true : forall a1 a2: A, eqb a1 a2 = true -> a1 = a2):
  forall (l1 l2 : list A), list_eqb eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1; destruct l2; intros.
  - reflexivity.
  - simpl in H; discriminate H.
  - simpl in H; discriminate H.
  - simpl in H.
    apply andb_true_iff in H as [? ?].
    apply eqb_true in H; subst.
    f_equal; auto.
Qed.

Definition option_eqb {A: Type} (eqb: A -> A -> bool) (o1 o2: option A): bool :=
  match o1, o2 with
  | Some a1, Some a2 => eqb a1 a2
  | None, None => true
  | _, _ => false
  end.

Lemma option_eqb_eq:
  forall A eqb,
    (forall a1 a2: A, eqb a1 a2 = true <-> a1 = a2) ->
    (forall o1 o2: option A, option_eqb eqb o1 o2 = true <-> o1 = o2).
Proof.
  intros.
  destruct o1, o2; simpl.
  + rewrite H.
    split; intros; congruence.
  + split; intros; congruence.
  + split; intros; congruence.
  + tauto.
Qed.