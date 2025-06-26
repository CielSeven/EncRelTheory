Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Inductive merge_step:
  (list Z * list Z * list Z) -> (list Z * list Z * list Z) -> Prop :=
| merge_step_l: forall x1 x2 l1 l2 l3,
    x1 <= x2 ->
    merge_step ((x1 :: l1), (x2 :: l2), l3) (l1, (x2 :: l2), (app l3 (cons x1 nil)))
| merge_step_r: forall x1 x2 l1 l2 l3,
    x2 <= x1 ->
    merge_step ((x1 :: l1), (x2 :: l2), l3) ((x1 :: l1), l2, (app l3 (cons x2 nil))).

Definition merge_steps l1 l2 l3 l1' l2' l3': Prop :=
  clos_refl_trans merge_step (l1, l2, l3) (l1', l2', l3').

Inductive merge_rel l1 l2: list Z -> Prop :=
| merge_l: forall l1' l3',
    merge_steps l1 l2 nil l1' nil l3' ->
    merge_rel l1 l2 (l3' ++ l1')
| merge_r: forall l2' l3',
    merge_steps l1 l2 nil nil l2' l3' ->
    merge_rel l1 l2 (l3' ++ l2').


Fixpoint increasing_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ increasing_aux l0 y
  end.

Definition increasing (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => increasing_aux l0 x
  end.

Inductive split_rec_rel:
  list Z -> list Z -> list Z -> list Z -> list Z -> Prop :=
| split_rec_rel_rec:
    forall a l l1 l2 l1' l2',
      split_rec_rel l l2 (a :: l1) l2' l1' ->
      split_rec_rel (a :: l) l1 l2 l1' l2'
| split_rec_rel_nil:
    forall l1 l2,
      split_rec_rel nil l1 l2 l1 l2.

Definition split_rel l l1 l2: Prop :=
  split_rec_rel l nil nil l1 l2.

Inductive merge_sort_rel: list Z -> list Z -> Prop :=
| merge_sort_rel_base: forall l l1,
    split_rel l l1 [] ->
    merge_sort_rel l l1
| merge_sort_rel_rec: forall l l1 l2 l1' l2' l',
    split_rel l l1 l2 ->
    l2 <> [] ->
    merge_sort_rel l1 l1' ->
    merge_sort_rel l2 l2' ->
    merge_rel l1' l2' l' ->
    merge_sort_rel l l'.

Lemma increasing_app_cons: forall l1 x l2,
  increasing (l1 ++ [x]) ->
  increasing (x :: l2) ->
  increasing (l1 ++ x :: l2).
Proof.
  intros.
  simpl in H0.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma increasing_app_cons_inv1: forall l1 x l2,
  increasing (l1 ++ x :: l2) ->
  increasing (l1 ++ [x]).
Proof.
  intros.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma increasing_app_cons_inv2: forall l1 x l2,
  increasing (l1 ++ x :: l2) ->
  increasing (x :: l2).
Proof.
  intros.
  simpl.
  induction l1; simpl in *.
  + tauto.
  + apply IHl1.
    destruct l1; simpl in *; tauto.
Qed.

Lemma merge_step_increasing1: forall l1 l2 l3 l1' l2' l3',
  merge_step (l1, l2, l3) (l1', l2', l3') ->
  increasing (l3 ++ l1) ->
  increasing (l3 ++ l2) ->
  increasing (l3' ++ l1').
Proof.
  intros.
  inversion H; subst.
  + rewrite <- app_assoc.
    apply H0.
  + rewrite <- app_assoc.
    simpl.
    apply increasing_app_cons.
    - eapply increasing_app_cons_inv1.
      apply H1.
    - apply increasing_app_cons_inv2 in H0.
      simpl in H0.
      simpl.
      tauto.
Qed.

Lemma merge_step_increasing2: forall l1 l2 l3 l1' l2' l3',
  merge_step (l1, l2, l3) (l1', l2', l3') ->
  increasing (l3 ++ l1) ->
  increasing (l3 ++ l2) ->
  increasing (l3' ++ l2').
Proof.
  intros.
  inversion H; subst.
  + rewrite <- app_assoc.
    simpl.
    apply increasing_app_cons.
    - eapply increasing_app_cons_inv1.
      apply H0.
    - apply increasing_app_cons_inv2 in H1.
      simpl in H1.
      simpl.
      tauto.
  + rewrite <- app_assoc.
    apply H1.
Qed.

Lemma merge_step_perm: forall l1 l2 l3 l1' l2' l3',
  merge_step (l1, l2, l3) (l1', l2', l3') ->
  Permutation (l3 ++ l1 ++ l2) (l3' ++ l1' ++ l2').
Proof.
  intros.
  inversion H; subst.
  + rewrite <- !app_assoc.
    reflexivity.
  + rewrite <- !app_assoc.
    apply Permutation_app; [reflexivity |].
    rewrite Permutation_app_comm.
    simpl.
    apply perm_skip.
    rewrite Permutation_app_comm.
    reflexivity.
Qed.

Lemma merge_steps_increasing: forall l1 l2 l3 l1' l2' l3',
  merge_steps l1 l2 l3 l1' l2' l3' ->
  increasing (l3 ++ l1) /\ increasing (l3 ++ l2) ->
  increasing (l3' ++ l1') /\ increasing (l3' ++ l2') .
Proof.
  unfold merge_steps.
  intros.
  induction_1n H.
  + tauto.
  + pose proof merge_step_increasing1 _ _ _ _ _ _ H1.
    pose proof merge_step_increasing2 _ _ _ _ _ _ H1.
    tauto.
Qed.

Lemma merge_steps_perm: forall l1 l2 l3 l1' l2' l3',
  merge_steps l1 l2 l3 l1' l2' l3' ->
  Permutation (l3 ++ l1 ++ l2) (l3' ++ l1' ++ l2').
Proof.
  unfold merge_steps.
  intros.
  induction_1n H.
  + reflexivity.
  + pose proof merge_step_perm _ _ _ _ _ _ H0.
    rewrite H1.
    tauto.
Qed.

Lemma merge_rel_increasing: forall l1 l2 l,
  merge_rel l1 l2 l ->
  increasing l1 ->
  increasing l2 ->
  increasing l.
Proof.
  intros.
  inversion H; subst.
  + pose proof merge_steps_increasing _ _ _ _ _ _ H2.
    simpl in H3.
    tauto.
  + pose proof merge_steps_increasing _ _ _ _ _ _ H2.
    simpl in H3.
    tauto.
Qed.

Lemma merge_rel_perm: forall l1 l2 l,
  merge_rel l1 l2 l ->
  Permutation (l1 ++ l2) l.
Proof.
  intros.
  inversion H; subst.
  + pose proof merge_steps_perm _ _ _ _ _ _ H0.
    simpl in H1.
    rewrite app_nil_r in H1.
    tauto.
  + pose proof merge_steps_perm _ _ _ _ _ _ H0.
    simpl in H1.
    tauto.
Qed.

Lemma split_rec_rel_perm: forall l l1 l2 l1' l2',
  split_rec_rel l l1 l2 l1' l2' ->
  Permutation (l ++ l1 ++ l2) (l1' ++ l2').
Proof.
  intros.
  induction H.
  + rewrite (Permutation_app_comm l1' l2'), <- IHsplit_rec_rel.
    rewrite !app_assoc.
    rewrite (Permutation_app_comm (l ++ l2)).
    simpl.
    apply perm_skip.
    rewrite !app_assoc.
    apply Permutation_app; [| reflexivity].
    apply Permutation_app_comm.
  + reflexivity.
Qed.

Lemma split_rel_perm: forall l l1 l2,
  split_rel l l1 l2 ->
  Permutation l (l1 ++ l2).
Proof.
  intros.
  apply split_rec_rel_perm in H.
  rewrite !app_nil_r in H.
  tauto.
Qed.

Lemma split_rec_rel_length: forall l l1 l2 l1' l2',
  split_rec_rel l l1 l2 l1' l2' ->
  (length l1 = length l2 -> length l1' <= S (length l2'))%nat /\
  (S (length l1) = length l2 -> length l2' <= S (length l1'))%nat.
Proof.
  intros.
  induction H.
  + simpl in *; lia.
  + simpl; lia.
Qed.

Lemma merge_base_fact: forall l l',
  split_rel l l' nil ->
  (exists x, l = [x] /\ l' = [x]) \/
  (l = [] /\ l' = []).
Proof.
  intros.
  pose proof split_rec_rel_length _ _ _ _ _ H.
  destruct H0 as [? _].
  specialize (H0 eq_refl).
  pose proof split_rec_rel_perm _ _ _ _ _ H.
  rewrite !app_nil_r in H1.
  pose proof Permutation_length H1.
  unfold split_rel in H0.
  inversion H; subst; clear H.
  + inversion H3; subst; clear H3.
    - simpl in *; lia.
    - left; exists a; tauto.
  + right; tauto.
Qed.

Lemma merge_sort_rel_increasing: forall l l',
  merge_sort_rel l l' ->
  increasing l'.
Proof.
  intros.
  induction H.
  + apply merge_base_fact in H.
    destruct H as [ [x [? ?] ] | [? ?] ]; subst.
    - simpl; tauto.
    - simpl; tauto.
  + pose proof merge_rel_increasing _ _ _ H3.
    tauto.
Qed.

Lemma merge_sort_rel_perm: forall l l',
  merge_sort_rel l l' ->
  Permutation l l'.
Proof.
  intros.
  induction H.
  + apply merge_base_fact in H.
    destruct H as [ [x [? ?] ] | [? ?] ]; subst.
    - reflexivity.
    - reflexivity.
  + pose proof merge_rel_perm _ _ _ H3.
    pose proof split_rel_perm _ _ _ H.
    rewrite H5, IHmerge_sort_rel1, IHmerge_sort_rel2, H4.
    reflexivity.
Qed.