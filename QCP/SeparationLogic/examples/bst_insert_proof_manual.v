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
From SimpleC.EE Require Import bst_insert_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_insert_entail_wit_1 : insert_entail_wit_1.
Proof.
  pre_process.
  Exists b_pre_v nil tr.
  simpl.
  entailer!.
Qed.

Lemma proof_of_insert_entail_wit_2_1 : insert_entail_wit_2_1.
Proof.
  pre_process.
  sep_apply (store_ptb_LH b b_v_2); [ | try tauto .. ].
  sep_apply store_ptb_app.
  Exists
    p_left
    (LH p_key p_value r0 ::  pt0_2)
    l0.
  entailer!.
  subst.
  rewrite <- H4.
  simpl.
  f_equal.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Lemma proof_of_insert_entail_wit_2_2 : insert_entail_wit_2_2.
Proof.
  pre_process.
  sep_apply (store_ptb_RH b b_v_2); [ | try tauto .. ].
  sep_apply store_ptb_app.
  Exists
    p_right
    (RH p_key p_value l0 ::  pt0_2)
    r0.
  entailer!.
  subst.
  rewrite <- H5.
  simpl.
  f_equal.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?];
    first [reflexivity | Key.order].
Qed.

Lemma proof_of_insert_return_wit_1 : insert_return_wit_1.
Proof.
  pre_process.
  sep_apply store_tree_zero; [ | tauto].
  Intros.
  subst.
  rewrite <- H1.
  simpl.
  sep_apply store_tree_size_1; [ | tauto ..].
  sep_apply store_ptb_store_tree.
  Intros p_root.
  Exists p_root.
  entailer!.
Qed.

Lemma proof_of_insert_return_wit_2 : insert_return_wit_2.
Proof.
  pre_process.
  sep_apply store_tree_make_tree; [ | tauto ..].
  sep_apply store_ptb_store_tree.
  rewrite <- H5.
  subst.
  simpl.
  destruct (Key.dec x_pre p_key) as [[? | ?] | ?];
    try Key.order.
  Intros p_root.
  Exists p_root.
  subst.
  entailer!.
Qed.

Lemma proof_of_insert_which_implies_wit_1 : insert_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_tree_not_zero; [ | tauto].
  Intros x.
  Intros k.
  Intros v.
  Intros r0. 
  Intros pl pr.
  Exists pr pl x v.
  Exists r0 k.
  entailer!.
Qed.

Lemma proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Intros b_pre_v.
  unfold store_map.
  Intros tr.
  Exists tr.
  Exists b_pre_v.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros b_post_v.
  Exists b_post_v.
  Exists (tree_insert x_pre value_pre tr).
  entailer!.
  + apply insert_Abs; tauto.
  + apply insert_SearchTree; tauto.
Qed.
