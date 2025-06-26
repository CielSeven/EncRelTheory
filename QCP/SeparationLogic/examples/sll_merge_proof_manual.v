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
From SimpleC.EE Require Import sll_merge_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Require Import sll_merge_lib.
Local Open Scope sac.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof.
  pre_process.
  Exists s1 s2 nil.
  simpl sllbseg.
  entailer!.
  unfold merge_steps. reflexivity.
Qed.

Lemma proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Proof.
  pre_process.
  Exists l1_new (y_data :: l2_new) (l3_2 ++ (x_data :: nil))%list.
  simpl sll. Exists y_next.
  entailer!.
  + sep_apply (sllbseg_len1 t). all: try tauto.
    sep_apply (sllbseg_sllbseg (&( "ret" ))).
    entailer!.
    sep_apply store_ptr_undef_store_ptr. entailer!.
  + unfold merge_steps.
    transitivity_n1 (x_data :: l1_new, y_data :: l2_new, l3_2).
    - subst. tauto.
    - apply merge_step_l. lia.
Qed.

Lemma proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Proof.
  pre_process.
  Exists (x_data :: l1_new) l2_new (l3_2 ++ (y_data :: nil))%list.
  simpl sll. Exists x_next.
  entailer!.
  + sep_apply (sllbseg_len1 t). all: try tauto.
    sep_apply (sllbseg_sllbseg (&( "ret" ))).
    entailer!.
    sep_apply store_ptr_undef_store_ptr. entailer!.
  + unfold merge_steps.
    transitivity_n1 (x_data :: l1_new, y_data :: l2_new, l3_2).
    - subst. tauto.
    - apply merge_step_r. lia.
Qed.

Lemma proof_of_merge_return_wit_1_1 : merge_return_wit_1_1.
Proof.
  pre_process.
  sep_apply (sll_zero y). all: try tauto.
  sep_apply sllseg_sll.
  Exists (l3 ++ l1)%list.
  entailer!.
  subst l2.
  apply merge_l. tauto.
Qed.

Lemma proof_of_merge_return_wit_1_2 : merge_return_wit_1_2.
Proof.
  pre_process.
  sep_apply (sll_zero x). all: try tauto.
  sep_apply sllseg_sll.
  Exists (l3 ++ l2)%list.
  entailer!.
  subst l1.
  apply merge_r. tauto.
Qed.

Lemma proof_of_merge_which_implies_wit_3 : merge_which_implies_wit_3.
Proof.
  pre_process.
  sep_apply sllbseg_2_sllseg.
  Intros ret'.
  Exists ret'.
  entailer!.
Qed.

Lemma proof_of_split_rec_return_wit_1 : split_rec_return_wit_1.
Proof.
  pre_process.
  Exists q_pre_v_2 p_pre_v_2.
  Exists l1 l2.
  sep_apply (sll_zero x_pre); [ | tauto].
  entailer!.
  subst l.
  constructor.
Qed.

Lemma proof_of_split_rec_return_wit_2 : split_rec_return_wit_2.
Proof.
  pre_process.
  Exists p_pre_v_2 q_pre_v_2.
  Exists s2_2 s1_2.
  entailer!.
  subst l.
  constructor.
  auto.
Qed.

Lemma proof_of_merge_sort_return_wit_1 : merge_sort_return_wit_1.
Proof.
  pre_process.
  Exists s1.
  sep_apply (sll_zero q_pre_v); [ | tauto].
  simpl sll.
  Intros.
  entailer!.
  constructor.
  subst s2.
  unfold split_rel.
  tauto.
Qed.

Lemma proof_of_merge_sort_return_wit_2 : merge_sort_return_wit_2.
Proof.
  pre_process.
  Exists s3.
  simpl sll.
  entailer!.
  eapply merge_sort_rel_rec; eauto.
Qed.

(* Lemma proof_of_merge_sort_which_implies_wit_1 : merge_sort_which_implies_wit_1.
Proof.
  pre_process.
  subst.
  simpl sll.
  entailer!.
Qed. *)

(* Lemma proof_of_merge_sort_which_implies_wit_2 : merge_sort_which_implies_wit_2.
Proof.
  pre_process.
  subst.
  simpl sll.
  entailer!.
Qed. *)

Lemma proof_of_merge_sort_which_implies_wit_3 : merge_sort_which_implies_wit_3.
Proof.
  pre_process.
  destruct l1.
  + simpl sll.
    entailer!.
  + entailer!.
    congruence.
Qed.

Lemma proof_of_merge_malloc_entail_wit_1 : merge_malloc_entail_wit_1.
Proof.
  pre_process.
  Exists p.
  Exists s1 s2 nil.
  simpl sllbseg. entailer!.
  unfold merge_steps. reflexivity.
Qed.

Lemma proof_of_merge_malloc_entail_wit_2_1 : merge_malloc_entail_wit_2_1.
Proof.
  pre_process.
  Exists x_next.
  Exists l1_new (y_data :: l2_new) (l3_2 ++ (x_data :: nil))%list.
  simpl sll. Exists y_next.
  entailer!.
  + sep_apply sllbseg_len1.
    sep_apply (sllbseg_sllbseg pret).
    entailer!. tauto.
  + unfold merge_steps.
    transitivity_n1 (x_data :: l1_new, y_data :: l2_new, l3_2).
    - subst. tauto.
    - apply merge_step_l. lia.
Qed.

Lemma proof_of_merge_malloc_entail_wit_2_2 : merge_malloc_entail_wit_2_2.
Proof.
  pre_process.
  Exists y_next.
  Exists (x_data :: l1_new) l2_new (l3_2 ++ (y_data :: nil))%list.
  simpl sll. Exists x_next.
  entailer!.
  + sep_apply sllbseg_len1. all: try tauto.
    sep_apply (sllbseg_sllbseg pret).
    entailer!.
  + unfold merge_steps.
    transitivity_n1 (x_data :: l1_new, y_data :: l2_new, l3_2).
    - subst. tauto.
    - apply merge_step_r. lia.
Qed.

Lemma proof_of_merge_malloc_return_wit_1_1 : merge_malloc_return_wit_1_1.
Proof.
  pre_process.
  sep_apply (sll_zero y). all: try tauto.
  sep_apply sllseg_sll.
  Exists (l3 ++ l1)%list.
  entailer!.
  subst l2.
  apply merge_l. tauto.
Qed.

Lemma proof_of_merge_malloc_return_wit_1_2 : merge_malloc_return_wit_1_2.
Proof.
  pre_process.
  sep_apply (sll_zero x). all: try tauto.
  sep_apply sllseg_sll.
  Exists (l3 ++ l2)%list.
  entailer!.
  subst l1.
  apply merge_r. tauto.
Qed.

Lemma proof_of_merge_malloc_which_implies_wit_2 : merge_malloc_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply sllbseg_2_sllseg.
  Intros ret'.
  Exists ret'.
  entailer!.
Qed.

Lemma proof_of_merge_sort_derive_high_level_spec_by_low_level_spec : merge_sort_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists l.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros l0 ret.
  Exists l0 ret.
  pose proof merge_sort_rel_perm _ _ H.
  pose proof merge_sort_rel_increasing _ _ H.
  entailer!.
Qed.

