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
From Examples.QCPexample Require Import sll_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
Local Open Scope sac.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof.
  pre_process.
  Exists s1 s2 nil.
  unfold sllbseg.
  entailer!.
Qed.

Lemma proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Proof.
  pre_process.
  Exists l1_new (y_data :: l2_new) (l3_2 ++ (x_data :: nil))%list.
  simpl sll. Exists y_next.
  entailer!.
  + sep_apply (sllbseg_len1 t); [ | tauto].
    sep_apply (sllbseg_sllbseg (&( "ret" ))).
    entailer!.
    sep_apply store_ptr_undef_store_ptr.
    entailer!.
  + subst.
    clear - H4 H.
    unfold merge_from_mid_rel in *.
    rewrite (repeat_break_unfold _ _) in H4.
    prove_by_one_abs_step (by_continue (l1_new, y_data :: l2_new, l3_2 ++ x_data :: nil)).
    unfold merge_body.
    abs_choice_left.
    abs_test_step; [ lia | ].
    abs_ret_step.
Qed.

Lemma proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Proof.
  pre_process.
  Exists (x_data :: l1_new) l2_new (l3_2 ++ (y_data :: nil))%list.
  simpl sll. Exists x_next.
  entailer!.
  + sep_apply (sllbseg_len1 t); [ | tauto].
    sep_apply (sllbseg_sllbseg (&( "ret" ))).
    entailer!.
    sep_apply store_ptr_undef_store_ptr.
    entailer!.
  + subst.
    clear - H4 H.
    unfold merge_from_mid_rel in *.
    rewrite (repeat_break_unfold _ _) in H4.
    prove_by_one_abs_step (by_continue (x_data :: l1_new, l2_new, l3_2 ++ y_data :: nil)).
    unfold merge_body.
    abs_choice_right.
    abs_test_step; [ lia | ].
    abs_ret_step.
Qed.

Lemma proof_of_merge_return_wit_1_1 : merge_return_wit_1_1.
Proof.
  pre_process.
  sep_apply (sll_zero y); [ | tauto].
  sep_apply sllseg_sll.
  Exists (l3 ++ l1).
  entailer!.
  subst; clear - H1.
  unfold merge_from_mid_rel in H1.
  rewrite (repeat_break_unfold _ _) in H1.
  prove_by_one_abs_step (by_break (l3 ++ l1)).
  unfold merge_body.
  destruct l1; abs_ret_step.
Qed.

Lemma proof_of_merge_return_wit_1_2 : merge_return_wit_1_2.
Proof.
  pre_process.
  sep_apply (sll_zero x); [ | tauto].
  sep_apply sllseg_sll.
  Exists (l3 ++ l2).
  entailer!.
  subst; clear - H0.
  unfold merge_from_mid_rel in H0.
  rewrite (repeat_break_unfold _ _) in H0.
  prove_by_one_abs_step (by_break (l3 ++ l2)).
  unfold merge_body.
  abs_ret_step.
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
  sep_apply sll_zero;auto.
  Intros.
  unfold maketuple in *.
  subst l.
  Exists q_pre_v_2 p_pre_v_2 l1 l2.
  entailer!.
  unfold split_rec_rel in H0.
  rewrite (split_rec_rel_unfold (nil, l1, l2)) in H0.
  simpl in H0.
  auto.
Qed. 

Lemma proof_of_split_rec_return_wit_2 : split_rec_return_wit_2.
Proof. 
  pre_process.
  clear H0.
  unfold maketuple, applyf, reversepair in *.
  Exists p_pre_v_2 q_pre_v_2 s2_2 s1_2.
  entailer!. 
Qed. 

Lemma proof_of_split_rec_which_implies_wit_2 : split_rec_which_implies_wit_2.
Proof.
  pre_process.
  subst l.
  entailer!.
  cbn [sll].
  entailer!.
  Exists p_v_next.
  entailer!.
  unfold split_rec_rel in H.
  rewrite (split_rec_rel_unfold (x_data :: l_new, l1, l2)) in H.
  simpl in H.
  tauto.
Qed. 

Lemma proof_of_merge_sort_entail_wit_1 : merge_sort_entail_wit_1.
Proof.
  pre_process.
  simpl sll.
  entailer!.
  unfold mergesortrec_loc0.
  rewrite (mergesortrec_unfold l) in H.
  unfold mergesortrec_f in H.
  tauto.
Qed.

Lemma proof_of_merge_sort_entail_wit_2 : merge_sort_entail_wit_2.
Proof.
  pre_process.
  Exists s1 s2.
  prop_apply (sll_not_zero' q_pre_v); [ | tauto].
  entailer!.
  + unfold applyf, mergesortrec_loc0, maketuple in H0.
    unfold mergesortrec_loc1.
    destruct s2; [ congruence | ].
    tauto.
Qed.

Lemma proof_of_merge_sort_entail_wit_3 : merge_sort_entail_wit_3.
Proof.
  pre_process.
  Exists l2_2 l0.
  entailer!.
Qed.

Lemma proof_of_merge_sort_entail_wit_4 : merge_sort_entail_wit_4.
Proof.
  pre_process.
  Exists l1_2 l0.
  entailer!.
Qed.

Lemma proof_of_merge_sort_return_wit_1 : merge_sort_return_wit_1.
Proof.
  pre_process.
  sep_apply (sll_zero q_pre_v); [ | tauto].
  Exists s1.
  entailer!.
  unfold applyf, mergesortrec_loc0, maketuple in H0.
  subst s2.
  tauto.
Qed.

Lemma proof_of_merge_sort_partial_solve_wit_3_pure : merge_sort_partial_solve_wit_3_pure.
Proof.
  pre_process.
Qed.


Lemma proof_of_merge_sort3_entail_wit_1 : merge_sort3_entail_wit_1.
Proof.
  pre_process.
  simpl.
  entailer!.
  unfold gmergesortrec_loc0.
  rewrite (gmergesortrec_unfold l) in H2.
  unfold gmergesortrec_f in H2.
  apply safeExec_choice_r in H2.
  unfold seq in H2.
  rewrite (split_rel_refine_ext_split l).
  prove_by_one_abs_step tt.
  abs_test_step.
  lia.
Qed.

Lemma proof_of_merge_sort3_entail_wit_2 : merge_sort3_entail_wit_2.
Proof.
  pre_process.
  Exists s1 s2.
  entailer!.
Qed.

Lemma proof_of_merge_sort3_entail_wit_3 : merge_sort3_entail_wit_3.
Proof.
  pre_process.
  Exists l2_2 l0.
  entailer!.
Qed.

Lemma proof_of_merge_sort3_entail_wit_4 : merge_sort3_entail_wit_4.
Proof.
  pre_process.
  Exists l1_2 l0.
  entailer!.
Qed.

Lemma proof_of_merge_sort3_return_wit_1 : merge_sort3_return_wit_1.
Proof.
  pre_process.
  rewrite (gmergesortrec_unfold l) in H4.
  unfold gmergesortrec_f in H4.
  apply safeExec_choice_l in H4.
  Exists l0_2.
  entailer!.
  revert H4; apply (highstependret_derive _ _ _ (fun _ => ATrue)).
  hnf.
  intros ? _; exists tt.
  split; [ | exact I].
  hnf.
  tauto.
Qed.

Lemma proof_of_merge_sort3_partial_solve_wit_5_pure : merge_sort3_partial_solve_wit_5_pure.
Proof.
  pre_process. 
Qed. 

Lemma proof_of_merge_sort3_partial_solve_wit_6_pure : merge_sort3_partial_solve_wit_6_pure.
Proof. 
  pre_process.
Qed. 

Lemma proof_of_merge_sort3_derive_low_level_spec_aux_by_low_level_spec : merge_sort3_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  Exists l.
  eapply safeExec_bind in H0 as (X' & ? & ?).
  Exists X'.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros l' ret.
  Exists l' ret.
  unfold applyf.
  entailer!.
Qed.

Lemma proof_of_merge_sort3_derive_high_level_spec_by_low_level_spec : merge_sort3_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists l.
  eExists.
  entailer!.
  2: apply safeExec_monad_Atrue_finnal.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  Intros retl retaddr.
  Exists retl retaddr.
  pose proof functional_correctness_gmergesort.
  unfold safeExec, safe in H0.
  unfold Hoare in H1.
  my_destruct H0.
  assert (ATrue tt).
  { hnf. auto. }
  specialize (H1 l tt retl x H3).
  assert ((return retl) x retl x).
  {
    hnf. split; auto.  
  }
  specialize (H2 _ _ H4).
  specialize (H1 H2).
  entailer!.
Qed.

Lemma proof_of_merge_sort2_derive_low_level_spec_aux_by_low_level_spec : merge_sort2_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  Exists l.
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists X'.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros l' ret.
  Exists l' ret.
  unfold applyf.
  entailer!.
Qed.

Lemma proof_of_merge_sort2_derive_high_level_spec_by_low_level_spec : merge_sort2_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists l.
  Exists (gmergesortrec l tt).
  rewrite logic_equiv_coq_prop_andp_sepcon.
  entailer!.
  2: apply safeExec_monad_Atrue_finnal.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  Intros retl retaddr.
  Exists retl retaddr.
  eapply safeExec_ret_Atrue_finnal in H as [? ? ].
  pose proof functional_correctness_gmergesort.
  unfold Hoare in H0.
  assert (ATrue tt).
  { hnf. auto. }
  specialize (H0 l tt retl x H1 H).
  entailer!.
Qed.

Lemma proof_of_merge_sort_derive_low_level_spec_aux_by_low_level_spec : merge_sort_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  Exists l.
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists X'.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros l' ret.
  Exists l' ret.
  unfold applyf.
  entailer!.
Qed.

Lemma proof_of_merge_sort_derive_high_level_spec_by_low_level_spec : merge_sort_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists l.
  Exists (mergesortrec l tt).
  rewrite logic_equiv_coq_prop_andp_sepcon.
  entailer!.
  2: apply safeExec_monad_Atrue_finnal.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  Intros retl retaddr.
  Exists retl retaddr.
  eapply safeExec_ret_Atrue_finnal in H as [? ? ].
  pose proof functional_correctness_mergesort.
  unfold Hoare in H0.
  assert (ATrue tt).
  { hnf. auto. }
  specialize (H0 l tt retl x H1 H).
  entailer!.
Qed.

Lemma proof_of_split_rec_derive_low_level_spec_aux_by_low_level_spec : split_rec_derive_low_level_spec_aux_by_low_level_spec.
Proof. 
  pre_process.
  Intros qptr pptr.
  Exists l l1 l2.
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists X'.
  entailer!.
  Exists qptr.
  entailer!.
  Exists pptr.
  entailer!.
  clear - H0.
  apply derivable1_wand_sepcon_adjoint.
  Intros qptr pptr pl ql.
  Exists qptr pptr pl ql.
  entailer!.
Qed. 

Lemma proof_of_split_rec_derive_high_level_spec_by_low_level_spec : split_rec_derive_high_level_spec_by_low_level_spec.
Proof. 
  pre_process.
  Intros qptr pptr.
  Exists l nil nil X.
  entailer!.
  Exists qptr.
  entailer!.
  Exists pptr.
  entailer!.
  clear.
  apply derivable1_wand_sepcon_adjoint.
  Intros qptr pptr pl ql.
  Exists qptr pptr pl ql.
  entailer!.
Qed. 

