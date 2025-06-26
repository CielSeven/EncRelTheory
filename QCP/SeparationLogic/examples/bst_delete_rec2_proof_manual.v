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
From SimpleC.EE Require Import bst_delete_rec2_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Proof.
  pre_process.
  Exists t_pre_v_left t_pre_v_right t_left nil.
  Exists t_value t_key t_pre_v.
  sep_apply (store_tree_zero t_pre_v_right t_right); simpl.
  entailer!; rewrite H4; simpl; auto.
  tauto.
Qed.

Lemma proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Proof.
  pre_process.
  Exists retval_v_left_2 retval_v_right_2 ret_left_2.
  Exists (t_pt_2 ++ (RH t_key t_value t_left :: nil)).
  Exists retval_v_value_2 retval_v_key_2 retval_v_2.
  entailer!.
  + sep_apply (store_ptb_RH).
    sep_apply (store_ptb_app retval &( t_pre_v # "tree" ->ₛ "right") t_pre t_pt_2 (RH t_key t_value t_left :: nil)).
    entailer!.
    - tauto.
    - tauto.
  + rewrite H9. simpl. tauto.
  + rewrite H9. simpl. rewrite H4. tauto.
  + rewrite H9. simpl. tauto.
  + rewrite H9. simpl. tauto.
Qed.

Lemma proof_of_get_pre_which_implies_wit_1 : get_pre_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; try tauto.
  Intros l0 k0 v0 r0.
  Intros pl pr.
  Exists pr pl l0 r0.
  Exists v0 k0.
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
  Exists b_pre_v_2.
  rewrite H15.
  simpl.
  entailer!.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?]; try Key.order.
  destruct l0.
  + discriminate.
  + inversion H9.
    rewrite H2. rewrite H3. rewrite H4. rewrite H5.
    sep_apply store_ptb_store_tree.
    Intros p_root.
    sep_apply store_tree_make_tree.
    entailer!.
    tauto.
    tauto.
Qed.

Lemma proof_of_delete_return_wit_2_2 : delete_return_wit_2_2.
Proof. 
  pre_process.
  Exists p_right.
  entailer!.
  sep_apply (store_tree_zero); [ | tauto].
  entailer!.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?]; try Key.order.
  assert (r0 = tree_delete' x_pre tr). {
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

Lemma proof_of_delete_which_implies_wit_2 : delete_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; try tauto.
  Intros l1 k0 v0 r1.
  Intros pl pr.
  Exists pr pl l1 r1.
  Exists v0 k0.
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
  Exists (tree_delete' x_pre tr).
  entailer!.
  - apply delete'_Abs. tauto. tauto.
  - apply delete'_SearchTree. tauto.
Qed.
