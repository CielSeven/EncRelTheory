Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Local Open Scope nat.
Local Open Scope list.

Import ListNotations.

(** In this section, we give some lemmas about list and sublist. *)
Section List_lemma.

Lemma length_nonnil: forall {A: Type} (l: list A),
  l <> nil -> length l > 0.
Proof.
  intros.
  destruct l.
  - congruence.
  - simpl; lia.
Qed.

Definition sublist {A: Type} (lo hi: nat) (l: list A): list A :=
  skipn lo (firstn hi l).

Lemma list_eq_ext: forall {A: Type} d (l1 l2: list A),
  l1 = l2 <->
  (length l1 = length l2 /\
   forall i, i < length l1 -> nth i l1 d = nth i l2 d).
Proof.
  intros.
  split; [intros; subst; auto |].
  intros [? ?].
  revert l2 H H0; induction l1; simpl; intros.
  + destruct l2.
    - reflexivity.
    - simpl in H.
      lia.
  + destruct l2.
    - simpl in H.
      lia.
    - simpl in H.
      specialize (IHl1 l2 ltac:(lia)).
      pose proof H0 0 ltac:(lia).
      simpl in H1.
      subst a0.
      f_equal.
      apply IHl1.
      intros.
      specialize (H0 (i + 1) ltac:(lia)).
      rewrite Nat.add_1_r in H0.
      simpl in H0.
      auto.
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

Lemma length_sublist:
  forall {A} lo hi (l: list A),
    lo <= hi /\ hi <= length l ->
    length (sublist lo hi l) = hi-lo.
Proof.
  intros.
  unfold sublist.
  rewrite skipn_length.
  rewrite firstn_length_le by lia.
  lia.
Qed.

Lemma length_sublist' {A: Type}:
  forall (l: list A) i j,
    length (sublist i j l) = 
    (min j (length l) - i).
Proof.
  intros.
  unfold sublist.
  rewrite skipn_length.
  rewrite firstn_length.
  reflexivity.
Qed.

Lemma nth_sublist:
  forall {A} lo i hi (l: list A) (d: A),
  i < hi-lo ->
  nth i (sublist lo hi l) d = nth (i+lo) l d.
Proof.
  intros.
  unfold sublist.
  rewrite nth_skipn.
  rewrite nth_firstn by lia.
  f_equal.
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

Lemma sublist_single : forall {A : Type} n (l : list A) (a : A),
  n < length l -> sublist n (n + 1) l = [nth n l a].
Proof.
  intros.
  rewrite (list_split_nth _ n l a) at 1; try lia.
  unfold sublist.
  rewrite firstn_app.
  assert (length (firstn n l) = n) by (rewrite firstn_length; lia).
  rewrite firstn_all2; try lia. 
  replace ((n + 1) - length (firstn (n) l))%nat with 1%nat by lia.
  rewrite skipn_app.
  replace (n - length (firstn (n) l))%nat with 0%nat by lia.
  rewrite skipn_all2; try lia.
  simpl. reflexivity.
Qed.

Lemma sublist_one_ele {A: Type}: 
  forall i (text: list A) (ch default: A),
    0 <= i < length text ->
    ch = nth i text default -> 
    sublist 0 i text ++ [ch] = sublist 0 (i + 1) text.
Proof.
  intros.
  eapply (list_eq_ext default _ _).
  split.
  + rewrite app_length.
    rewrite ! length_sublist by lia.
    simpl; lia.
  + intros.
    destruct (le_gt_dec i i0).
    - rewrite app_nth2 by (rewrite length_sublist by lia; lia).
      rewrite app_length, length_sublist in H1 by lia.
      simpl in H1.
      rewrite !nth_sublist by lia.
      rewrite length_sublist by lia.
      replace (i0 - (i - 0)) with 0 by lia.
      simpl.
      subst ch.
      f_equal; lia.
    - rewrite app_nth1 by (rewrite length_sublist by lia; lia).
      rewrite !nth_sublist by lia.
      reflexivity.
Qed.

Lemma sublist_one_ele' {A: Type}:
  forall i (text: list A) default,
    0 <= i < length text ->
    sublist 0 (i + 1) text = sublist 0 i text ++ [nth i text default].
Proof.
  intros.
  rewrite (sublist_one_ele i text (nth i text default) default) by easy.
  reflexivity.
Qed.

Lemma sublist_single' {A: Type}:
  forall (n : nat) (l : list A) (a : A),
    0 < n <= length l ->
    sublist (n - 1) n l = [nth (n - 1) l a].
Proof.
  intros.
  remember (n-1) as t.
  assert (n = t + 1) by lia.
  rewrite H0.
  apply sublist_single; lia.
Qed.

Lemma sublist_self {A: Type}:
  forall (l1: list A) x,
    x = length l1 ->
    sublist 0 x l1 = l1.
Proof.
  intros. unfold sublist; subst.
  rewrite skipn_O.
  apply firstn_all.
Qed.

Lemma sublist_split_app_l : forall {A : Type} lo hi (l1 l2 : list A),
  lo <= hi -> hi <= length l1 -> sublist lo hi (l1 ++ l2) = sublist lo hi l1.
Proof.
  intros.
  unfold sublist.
  rewrite firstn_app.
  simpl. 
  replace (hi - length l1)%nat with O by lia.
  rewrite app_nil_r. auto. 
Qed.

Lemma sublist_split_app_r {A: Type}:
  forall lo hi len (l1 l2: list A),
    length l1 = len ->
    len <= lo <= hi ->
    sublist lo hi (l1 ++ l2) = sublist (lo - len) (hi - len) l2.
Proof.
  intros.
  unfold sublist.
  repeat rewrite skipn_firstn.
  rewrite skipn_app.
  pose proof (skipn_length lo l1).
  replace (length l1 - lo) with O in H1 by lia.
  rewrite length_zero_iff_nil in H1; rewrite H1.
  simpl.
  replace (hi - len - (lo - len)) with (hi - lo) by lia.
  replace (lo - length l1) with (lo - len) by lia.
  auto.
Qed.

Lemma sublist_split: forall {A : Type} lo hi mid (l : list A),
  0 <= lo <= mid -> mid <= hi <= length l ->
  sublist lo hi l = sublist lo mid l ++ sublist mid hi l.
Proof.
  intros.
  rewrite <- (firstn_skipn hi l).
  remember (firstn hi l) as l1.
  remember (skipn hi l) as l2.
  assert (length l1 = hi).
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
  replace hi%nat with (length l1) by lia.
  assert (mid <= length l1) by lia.
  clear H0 H1 l2 hi.
  rewrite firstn_all2 ; try lia.
  rename l1 into l. 
  rewrite <- (firstn_skipn ( lo) l).
  remember (firstn ( lo) l) as l1.
  remember (skipn ( lo) l) as l2.
  assert (length l1 = lo).
  {
    rewrite Heql1.
    rewrite firstn_length.
    lia.
  }
  rewrite firstn_app.
  do 3 rewrite skipn_app.
  rewrite firstn_all2 ; try lia.
  replace ( lo - length l1)%nat with O by lia.
  simpl.
  do 2 (rewrite skipn_all2 ; try lia).
  rewrite! app_nil_l.
  rewrite firstn_skipn.
  reflexivity.
Qed.

Lemma sublist_nil {A: Type}:
  forall (l : list A) a b,
    b <= a -> sublist a b l = [].
Proof.
  intros. unfold sublist.
  apply skipn_all2.
  rewrite firstn_length; lia.
Qed.

End List_lemma.

(** In this section, we give some basic definitions and lemmas regarding prefix and suffix. *)
Section presuffix_lemma.
Definition is_prefix {A: Type} (l1 l2: list A): Prop :=
  exists l,
    l2 = l1 ++ l.

Definition is_suffix {A: Type} (l1 l2: list A): Prop :=
  exists l,
    l2 = l ++ l1.

Notation "l1 'is_a_prefix_of' l2" := (is_prefix l1 l2) (at level 10, no associativity).

Notation "l1 'is_a_suffix_of' l2" := (is_suffix l1 l2) (at level 10, no associativity).

Definition presuffix {A: Type} (l1 l2: list A): Prop :=
  l1 is_a_prefix_of l2 /\
  l1 is_a_suffix_of l2.

Definition partial_match_res {A: Type} (patn text res: list A): Prop :=
  res is_a_suffix_of text /\
  res is_a_prefix_of patn.

Definition partial_bound_res {A: Type} (patn text bound: list A): Prop :=
  (forall res, partial_match_res patn text res -> length res <= length bound).

Definition proper_presuffix {A: Type} (l1 l2: list A): Prop :=
  presuffix l1 l2 /\ length l1 < length l2.

Definition presuffix_bound {A: Type} (l1 l2: list A): Prop :=
  (forall l3, proper_presuffix l3 l2 -> presuffix l3 l1).

Definition max_proper_presuffix {A: Type} (l1 l2: list A): Prop :=
  proper_presuffix l1 l2 /\ presuffix_bound l1 l2.

Lemma is_suffix_snoc_snoc_iff: forall {A: Type} (l1 l2: list A) a1 a2,
  (l1 ++ [a1]) is_a_suffix_of (l2 ++ [a2]) <->
  l1 is_a_suffix_of l2 /\ a1 = a2.
Proof.
  intros.
  split; intros.
  + destruct H as [l ?].
    rewrite app_assoc in H.
    apply app_inj_tail in H.
    destruct H.
    split; [eexists; eauto | congruence].
  + destruct H as [ [l ?] ?].
    exists l.
    subst.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma prefix_length: forall {A: Type} (l1 l2: list A),
  l1 is_a_prefix_of l2 ->
  length l1 <= length l2.
Proof.
  intros.
  destruct H as [? ?].
  subst.
  rewrite app_length.
  lia.
Qed.

Lemma suffix_length: forall {A: Type} (l1 l2: list A),
  l1 is_a_suffix_of l2 ->
  length l1 <= length l2.
Proof.
  intros.
  destruct H as [? ?].
  subst.
  rewrite app_length.
  lia.
Qed.

Lemma presuffix_length: forall {A: Type} (l1 l2: list A),
  presuffix l1 l2 ->
  length l1 <= length l2.
Proof.
  unfold presuffix; intros.
  apply prefix_length; tauto.
Qed.

Lemma prefix_iff: forall {A: Type} (default: A) (l1 l2: list A),
  l1 is_a_prefix_of l2 <->
  (length l1 <= length l2 /\
   forall i, 0 <= i < length l1 -> nth i l1 default = nth i l2 default)%nat.
Proof.
  intros.
  split; intros.
  + pose proof prefix_length _ _ H.
    destruct H as [? ?].
    split; [tauto |].
    intros.
    subst.
    rewrite app_nth1 by lia.
    reflexivity.
  + destruct H.
    exists (sublist (length l1) (length l2) l2).
    
    rewrite (list_eq_ext default).
    split.
    - rewrite app_length.
      rewrite length_sublist by lia.
      lia.
    - intros.
      destruct (le_gt_dec (length l1) i).
      * rewrite app_nth2 by lia.
        rewrite nth_sublist by lia.
        f_equal; lia.
      * rewrite app_nth1 by lia.
        symmetry; apply H0; lia.
      
Qed.

Lemma prefix_iff': forall {A: Type} (l1 l2: list A),
  l1 is_a_prefix_of l2 <->
  (length l1 <= length l2 /\
   forall default i, 0 <= i < length l1 ->
                     nth i l1 default = nth i l2 default)%nat.
Proof.
  intros.
  split; intros.
  + pose proof prefix_length _ _ H.
    split; [tauto |].
    intros d.
    rewrite (prefix_iff d) in H.
    tauto.
  + destruct H.
    destruct l1.
    - exists l2.
      reflexivity.
    - specialize (H0 a).
      rewrite (prefix_iff a).
      tauto.
Qed.

Lemma suffix_iff: forall {A: Type} (default: A) (l1 l2: list A),
  l1 is_a_suffix_of l2 <->
  (length l1 <= length l2 /\
   forall i, 0 <= i < length l1 ->
             nth (length l1 - 1 - i) l1 default =
             nth (length l2 - 1 - i) l2 default)%nat.
Proof.
  intros.
  split; intros.
  + pose proof suffix_length _ _ H.
    destruct H as [? ?].
    split; [tauto |].
    intros.
    subst.
    rewrite app_length.
    rewrite app_nth2 by lia.
    f_equal. lia.
  + destruct H.
    exists (sublist 0 (length l2 - length l1) l2).
    rewrite (list_eq_ext default).
    split.
    - rewrite app_length.
      rewrite length_sublist by lia.
      lia.
    - intros.
      destruct (le_gt_dec (length l2 - length l1) i).
      * rewrite app_nth2 by (rewrite length_sublist by lia; lia).
        rewrite length_sublist by lia.
        replace (i - (length l2 - length l1 - 0)) with
                (length l1 - 1 - (length l2 - 1 - i)) by lia.
        rewrite H0 by lia.
        f_equal; lia.
      * rewrite app_nth1 by (rewrite length_sublist by lia; lia).
        rewrite nth_sublist by lia.
        f_equal; lia.
  Qed.

Lemma suffix_iff': forall {A: Type} (l1 l2: list A),
  l1 is_a_suffix_of l2 <->
  (length l1 <= length l2 /\
   forall default i, 0 <= i < length l1 ->
             nth (length l1 - 1 - i) l1 default =
             nth (length l2 - 1 - i) l2 default)%nat.
Proof.
  intros.
  split; intros.
  + pose proof suffix_length _ _ H.
    split; [tauto |].
    intros d.
    rewrite (suffix_iff d) in H.
    tauto.
  + destruct H.
    destruct l1.
    - exists l2.
      rewrite app_nil_r.
      reflexivity.
    - specialize (H0 a).
      rewrite (suffix_iff a).
      tauto.
Qed.

Lemma is_prefix_snoc_iff: forall {A: Type} default (l1 l2: list A) a,
  (l1 ++ [a]) is_a_prefix_of l2 <->
  (length l1 < length l2 /\
   l1 is_a_prefix_of l2 /\
   a = nth (length l1) l2 default).
Proof.
  intros.
  rewrite !(prefix_iff default).
  rewrite app_length; simpl.
  split; intros.
  + destruct H.
    split; [| split; [split |]].
    - lia.
    - lia.
    - intros.
      specialize (H0 i ltac:(lia)).
      rewrite <- H0.
      rewrite app_nth1 by lia.
      reflexivity.
    - specialize (H0 (length l1) ltac:(lia)).
      rewrite <- H0.
      rewrite app_nth2 by lia.
      replace (length l1 - length l1) with 0 by lia.
      simpl.
      reflexivity.
  + destruct H as [? [[_ ?] ?]].
    split; [lia |].
    intros.
    destruct (le_gt_dec (length l1) i).
    - rewrite app_nth2 by lia.
      replace (i - length l1) with 0 by lia.
      simpl.
      rewrite H1; f_equal; lia.
    - rewrite app_nth1 by lia.
      apply H0; lia.
Qed.

Lemma prefix_trans: forall {A: Type} (l1 l2 l3: list A),
  l1 is_a_prefix_of l2 ->
  l2 is_a_prefix_of l3 ->
  l1 is_a_prefix_of l3.
Proof.
  intros.
  destruct H as [? ?], H0 as [? ?].
  exists (x ++ x0).
  subst.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma suffix_trans: forall {A: Type} (l1 l2 l3: list A),
  l1 is_a_suffix_of l2 ->
  l2 is_a_suffix_of l3 ->
  l1 is_a_suffix_of l3.
Proof.
  intros.
  destruct H as [? ?], H0 as [? ?].
  exists (x0 ++ x).
  subst.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma presuffix_trans: forall {A: Type} (l1 l2 l3: list A),
  presuffix l1 l2 ->
  presuffix l2 l3 ->
  presuffix l1 l3.
Proof.
  unfold presuffix; intros; split.
  - apply (prefix_trans _ l2); tauto.
  - apply (suffix_trans _ l2); tauto.
Qed.

Lemma prefix_total_order:
  forall {A: Type} (l1 l2 l: list A),
    l1 is_a_prefix_of l ->
    l2 is_a_prefix_of l ->
    length l1 <= length l2 ->
    l1 is_a_prefix_of l2.
Proof.
  intros ? ? ? ?.
  rewrite !prefix_iff'.
  intros [? ?] [? ?] ?.
  split; [lia |].
  intros.
  rewrite H0, H2 by lia.
  reflexivity.
Qed.

Lemma suffix_total_order:
  forall {A: Type} (l1 l2 l: list A),
    l1 is_a_suffix_of l ->
    l2 is_a_suffix_of l ->
    length l1 <= length l2 ->
    l1 is_a_suffix_of l2.
Proof.
  intros ? ? ? ?.
  rewrite !suffix_iff'.
  intros [? ?] [? ?] ?.
  split; [lia |].
  intros.
  rewrite H0, H2 by lia.
  reflexivity.
Qed.

Lemma partial_match_total_order:
  forall {A: Type} (l1 l2 patn text: list A),
    partial_match_res patn text l1 ->
    partial_match_res patn text l2 ->
    length l1 <= length l2 ->
    presuffix l1 l2.
Proof.
  intros.
  destruct H, H0.
  pose proof prefix_total_order _ _ _ H2 H3 H1.
  pose proof suffix_total_order _ _ _ H H0 H1.
  split; tauto.
Qed.

Lemma partial_match_iff:
  forall {A: Type} (res0 patn text: list A),
    partial_match_res patn text res0 ->
    partial_bound_res patn text res0 ->
    forall res,
      partial_match_res patn text res <->
      presuffix res res0.
Proof.
  intros.
  split; intros.
  + specialize (H0 _ H1).
    pose proof partial_match_total_order _ _ _ _ H1 H H0.
    tauto.
  + clear H0.
    destruct H as [? ?].
    destruct H1.
    pose proof prefix_trans _ _ _ H1 H0.
    pose proof suffix_trans _ _ _ H2 H.
    split; tauto.
Qed.

Lemma partial_match_snoc_iff:
  forall {A: Type} default (res patn text: list A) ch,
    partial_match_res patn (text ++ [ch]) res <->
    res = [] \/
    exists res',
      res = res' ++ [ch] /\
      length res' < length patn /\
      nth (length res') patn default = ch /\
      partial_match_res patn text res'.
Proof.
  intros.
  split; intros.
  + destruct (list_snoc_destruct res) as [? | [ch0 [res' ?] ] ]; subst res.
    - left.
      tauto.
    - right.
      exists res'.
      destruct H.
      apply is_suffix_snoc_snoc_iff in H.
      destruct H; subst ch0.
      split; [auto | ].
      split; [| split].
      * apply prefix_length in H0.
        rewrite app_length in H0; simpl in H0.
        lia.
      * destruct H0.
        subst patn.
        rewrite <- app_assoc.
        rewrite app_nth2 by lia.
        replace (length res' - length res') with 0 by lia.
        simpl app.
        reflexivity.
      * split; auto.
        eapply prefix_trans; [ | apply H0].
        exists [ch]; reflexivity.
  + destruct H as [? | [? [? ?] ] ].
    - subst.
      split.
      * exists (text ++ [ch]).
        rewrite app_nil_r.
        reflexivity.
      * exists patn.
        reflexivity.
    - destruct H0 as [? [? [? ?] ]].
      subst.
      split; auto.
      * apply is_suffix_snoc_snoc_iff.
        tauto.
      * rewrite (is_prefix_snoc_iff default).
        tauto.
Qed.

Lemma prefix_iff_sublist {A: Type}:
  forall (l1 l2: list A),
    l1 is_a_prefix_of l2 <->
    (exists j, j = length l1 /\ l1 = sublist 0 j l2).
Proof.
  split; intros.
  - unfold is_prefix in H.
    destruct H as [l3 H].
    exists (length l1).
    pose proof app_length l1 l3.
    subst; split; try lia.
    rewrite sublist_split_app_l; try lia.
    rewrite sublist_self; easy.
  - destruct H as [j [? ?]].
    pose proof (f_equal (@length A) H0).
    rewrite length_sublist' in H1.
    unfold is_prefix.
    exists (sublist j (length l2) l2).
    rewrite <- sublist_self at 1 by eauto.
    rewrite (sublist_split 0 (length l2) j); try lia.
    rewrite H0; auto.
Qed.

Lemma suffix_iff_sublist {A: Type}:
  forall (l1 l2: list A),
    l1 is_a_suffix_of l2 <->
    (exists i, i = length l2 - length l1 /\ l1 = sublist i (length l2) l2).
Proof.
  split; intros.
  - unfold is_suffix in H.
    destruct H as [l3 H].
    exists (length l3).
    pose proof app_length l3 l1.
    subst; split; try lia.
    rewrite sublist_split_app_r with (len:= length l3); try lia.
    rewrite H0.
    replace (length l3 - length l3) with 0 by lia.
    replace (length l3 + length l1 - length l3) with (length l1) by lia.
    rewrite sublist_self; easy.
  - destruct H as [i [? ?]].
    pose proof (f_equal (@length A) H0).
    rewrite length_sublist in H1 by lia.
    unfold is_suffix.
    exists (sublist 0 i l2).
    rewrite <- sublist_self at 1 by eauto.
    rewrite (sublist_split 0 (length l2) i); try lia.
    rewrite H0; easy.
Qed.

Lemma nil_prefix {A: Type}:
  forall (l: list A), [] is_a_prefix_of l.
Proof.
  intros; unfold is_prefix.
  exists l; easy.
Qed.

Lemma nil_suffix {A: Type}:
  forall (l: list A), [] is_a_suffix_of l.
Proof.
  intros; unfold is_suffix.
  exists l. rewrite app_nil_r; easy.
Qed.

Lemma nil_presuffix {A: Type}:
  forall (l: list A), presuffix [] l.
Proof. 
  intros; unfold presuffix.
  split; [apply nil_prefix | apply nil_suffix].
Qed.

Lemma presuffix_nil_iff {A: Type}:
  forall (l:list A), presuffix l [] <-> l = [].
Proof.
  intros; split; intros.
  - unfold presuffix in H.
    pose proof prefix_length _ _ (proj1 H).
    simpl in H0.
    apply length_zero_iff_nil; lia.
  - subst; apply nil_presuffix.
Qed.

Lemma partial_match_nil {A: Type}:
  forall (patn text: list A),
    partial_match_res patn text [].
Proof.
  intros; unfold partial_match_res.
  split; [apply nil_suffix | apply nil_prefix].
Qed.

Lemma presuffix_partial_match {A: Type} (p t l0 l1: list A):
  partial_match_res p t l0 ->
  presuffix l1 l0 ->
  partial_match_res p t l1.
Proof.
  unfold partial_match_res, presuffix; intros.
  destruct H; destruct H0.
  split.
  - eapply suffix_trans; eauto.
  - eapply prefix_trans; eauto.
Qed.

Lemma prefix_app_iff {A: Type}:
  forall (l1 l2 l3: list A),
    l1 is_a_prefix_of l2 <->
    length l1 <= length l2 /\ l1 is_a_prefix_of (l2 ++ l3).
Proof.
  split; intros.
  - split. apply prefix_length, H.
    unfold is_prefix in *.
    destruct H. exists (x ++ l3).
    rewrite H. rewrite app_assoc; auto.
  - destruct H as [H0 H1].
    rewrite prefix_iff' in *.
    destruct H1 as [_ H1]; split; try easy.
    intros. specialize (H1 default i H).
    rewrite app_nth1 in H1 by lia; auto.
Qed.

Lemma suffix_app_iff {A: Type}:
  forall (l1 l2 l3: list A),
    l1 is_a_suffix_of l2 <->
    length l1 <= length l2 /\ l1 is_a_suffix_of (l3 ++ l2) .
Proof.
  split; intros.
  - split. apply suffix_length, H.
    unfold is_suffix in *.
    destruct H. exists (l3 ++ x).
    rewrite H. rewrite app_assoc; auto.
  - destruct H as [H0 H1].
    rewrite suffix_iff' in *.
    destruct H1 as [_ H1]; split; try easy.
    intros. specialize (H1 default i H).
    rewrite app_length in H1.
    rewrite app_nth2 in H1 by lia.
    replace (length l3 + length l2 - 1 - i - length l3) 
      with (length l2 - 1 - i) in H1 by lia; auto.
Qed.

Lemma prefix_sublist_iff {A: Type}:
  forall (l0 l: list A) i,
    0 <= i <= length l ->
    l0 is_a_prefix_of (sublist 0 i l) <->
    length l0 <= i /\ l0 is_a_prefix_of l.
Proof.
  intros.
  rewrite <- (sublist_self l) at 2; eauto.
  rewrite (sublist_split 0 (length l) i); try lia.
  pose proof length_sublist 0 i l ltac:(lia).
  replace (i - 0) with i in H0 by lia.
  rewrite <- H0 at 2.
  apply prefix_app_iff.
Qed.

Lemma suffix_sublist_cons_iff {A: Type}:
  forall (l0 l: list A) i,
    1 <= i <= length l ->
    l0 is_a_suffix_of (sublist 1 i l) <->
    length l0 <= i - 1 /\ l0 is_a_suffix_of (sublist 0 i l).
Proof.
  intros.
  rewrite (sublist_split 0 i 1); try lia.
  pose proof length_sublist 1 i l ltac:(lia).
  rewrite <- H0.
  apply suffix_app_iff.
Qed.

End presuffix_lemma.