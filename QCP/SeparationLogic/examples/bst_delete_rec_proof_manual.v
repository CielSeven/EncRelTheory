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
From SimpleC.EE Require Import bst_delete_rec_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Proof.
  pre_process.
  subst; simpl.
  Exists t_left 0 nil l0 t_key.
  Exists t_value.
  sep_apply (store_tree_zero 0 r0).
  entailer!.
  + simpl.
    entailer!.
  + intros. simpl.
    rewrite H2.
    destruct tr_ret_right0; tauto. 
  + tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Proof.
  pre_process.
  Exists retval_left_2 0.
  Exists (pt_2 ++ (RH t_key t_value l0 :: nil)).
  Exists tr_ret_left_2 retval_key_2.
  Exists retval_value_2.
  entailer!.
  + rewrite H1.
    sep_apply (store_pt_RH t_right t_pre t_left t_key t_value l0); try tauto.
    sep_apply (store_pt_app retval t_right t_pre pt_2 (RH t_key t_value l0 :: nil)).
    entailer!. 
  + intros tr0.
    pose proof H0 tr0.
    pose proof combine_tree_pt_assoc (RH t_key t_value l0 :: nil) pt_2 (make_tree tr_ret_left_2 retval_key_2
    retval_value_2 tr0).
    rewrite <- H10.
    subst tr. 
    transitivity (make_tree l0 t_key t_value (tree_pre_merge r0 tr0)); simpl.
    - destruct r0; simpl; reflexivity.
    - f_equal. apply H9.
Qed.


Lemma proof_of_get_pre_which_implies_wit_1 : get_pre_which_implies_wit_1.
Proof. 
  pre_process.
  sep_apply store_tree_not_zero; [ | tauto].
  Intros x k v r0.
  Intros pl pr.
  Exists pr pl x v.
  Exists r0 k.
  entailer!.
Qed.


Lemma proof_of_delete_return_wit_1 : delete_return_wit_1.
Proof. 
  pre_process.
  Exists b_pre_v_2.
  entailer!.
  sep_apply (store_tree_zero); [ | tauto].
  entailer!.
  rewrite H3.
  simpl. 
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_2_1 : delete_return_wit_2_1.
Proof.
  pre_process.
  Exists p_left.
  entailer!.
  rewrite H9.
  simpl.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?]; try Key.order.
  sep_apply store_tree_make_tree; try tauto.
  pose proof H0 r0.
  rewrite H15.
  sep_apply store_combine.
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_2_2 : delete_return_wit_2_2.
Proof. 
  pre_process.
  Exists p_right.
  entailer!.
  sep_apply (store_tree_zero); [ | tauto].
  entailer!.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?];
    try Key.order.
  assert (r0 = tree_delete x_pre tr). {
    rewrite e.
    rewrite H4.
    simpl.
    destruct (Key.dec p_key p_key).
    - destruct s ; lia.
    - rewrite H9. simpl. tauto.
  }
  rewrite H10.
  entailer!.
Qed.

Lemma proof_of_delete_return_wit_2_3 : delete_return_wit_2_3.
Proof. 
  pre_process.
  Exists b_pre_v_3.
  entailer!.
  subst.
  simpl.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?]; try Key.order.
  sep_apply store_tree_make_tree; try tauto.
  reflexivity.
Qed.

Lemma proof_of_delete_return_wit_2_4 : delete_return_wit_2_4.
Proof. 
  pre_process.
  Exists b_pre_v_3.
  entailer!.
  subst.
  simpl.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?]; try Key.order.
  sep_apply store_tree_make_tree; try tauto.
  reflexivity.
Qed.

Lemma proof_of_delete_which_implies_wit_1 : delete_which_implies_wit_1.
Proof. 
  pre_process.
  sep_apply store_tree_not_zero; [ | tauto].
  Intros x k v r0. 
  Intros pl pr.
  Exists pr pl x v.
  Exists r0 k.
  entailer!.
Qed.

Lemma proof_of_delete_derive_high_level_spec_by_low_level_spec : delete_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Intros b_pre_v.
  unfold store_map. Intros tr.
  Exists tr. 
  entailer!.
  Exists b_pre_v.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros b_pre_v_4.
  Exists b_pre_v_4.
  entailer!.
  Exists (tree_delete x_pre tr).
  entailer!.
  - apply delete_Abs ; auto.
  - apply delete_SearchTree ; auto. 
Qed.