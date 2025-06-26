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
From SimpleC.EE Require Import bst_insert_rec_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_insert_return_wit_1 : insert_return_wit_1.
Proof.
  pre_process.
  sep_apply (store_tree_zero); [ | tauto].
  Intros.
  subst.
  simpl.
  Exists 0 0.
  entailer!.
Qed.

Lemma proof_of_insert_return_wit_2 : insert_return_wit_2.
Proof.
  pre_process.
  subst.
  simpl.
  destruct (Key.dec x_pre b_key) as [[? | ?] | ?];
    try Key.order.
  simpl.
  Exists retval b_right.
  entailer!.
Qed.

Lemma proof_of_insert_return_wit_3 : insert_return_wit_3.
Proof.
  pre_process.
  subst.
  simpl.
  destruct (Key.dec x_pre b_key) as [[? | ?] | ?];
    try Key.order.
  simpl.
  Exists b_left retval.
  entailer!.
Qed.

Lemma proof_of_insert_return_wit_4 : insert_return_wit_4.
Proof.
  pre_process.
  subst.
  simpl.
  destruct (Key.dec x_pre b_key) as [[? | ?] | ?];
    try Key.order.
  simpl.
  subst.
  Exists b_left b_right.
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
  unfold store_map.
  Intros tr.
  Exists tr.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros retval.
  Exists retval.
  Exists (tree_insert x_pre value_pre tr).
  entailer!.
  + apply insert_Abs; tauto.
  + apply insert_SearchTree; tauto.
Qed.
