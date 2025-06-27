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
From Examples.QCPexample Require Import kmp_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import kmp_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.

Lemma proof_of_inner_entail_wit_2 : inner_entail_wit_2.
Proof.
  pre_process.
  prop_apply store_char_array_Zlength.
  prop_apply store_int_array_Zlength.
  rewrite Zlength_app.
  replace (Zlength (0::nil)) with 1 by easy.
  pose proof H as H'.
  unfold inner_loop in H.
  unfold_loop H.
  unfold inner_body at 1 in H.
  safe_step H.
  entailer!.
Qed. 

Lemma proof_of_inner_entail_wit_3 : inner_entail_wit_3.
Proof. 
  pre_process.
  entailer!.
  unfold inner_loop in *.
  unfold_loop H4.
  unfold inner_body at 1 in H4.
  safe_step H4.
  rewrite app_Znth1 in H0 by auto.
  safe_choice_r H4.
  safe_choice_r H4; auto.
  unfold continue in H4.
  prog_nf in H4. auto.
Qed. 

Lemma proof_of_inner_return_wit_1 : inner_return_wit_1.
Proof. 
  pre_process.
  entailer!.
  unfold inner_loop in H3.
  unfold_loop H3.
  unfold inner_body at 1 in H3.
  repeat (prog_nf in H3 ; safe_step H3).
  rewrite app_Znth1 in H by lia.
  safe_choice_l H3; auto.
  unfold break in H3.
  prog_nf in H3. auto.
Qed. 

Lemma proof_of_inner_return_wit_2 : inner_return_wit_2.
Proof. 
  pre_process.
  entailer!.
  unfold inner_loop in H4.
  unfold_loop H4.
  unfold inner_body at 1 in H4.
  safe_step H4.
  rewrite app_Znth1 in H0 by lia.
  safe_choice_r H4.
  safe_choice_l H4.
  unfold break in H4.
  prog_nf in H4.
  auto.
Qed. 

Lemma proof_of_constr_entail_wit_1 : constr_entail_wit_1.
Proof. 
  pre_process; subst.
  Exists (sublist 1 n l) (0::nil).
  entailer!.
  prop_apply store_int_array_Zlength; Intros.
  destruct l.
  rewrite Zlength_nil in H0; lia.
  replace (z::l) with ((z::nil) ++ l) by easy.
  rewrite (replace_Znth_app_l 0 0); try lia.
  2:{ lazy; auto. }
  replace (replace_Znth 0 0 (z::nil)) with (0::nil) by easy.
  rewrite (store_int_array_divide retval n _ 1); [ | lia | auto].
  rewrite sublist_split_app_l; [ | lia | easy].
  assert (Zlength (0::nil) = 1). 
  { lazy; auto. }
  rewrite sublist_self; eauto.
  entailer!.
  replace ((0::nil) ++ l) with (0::l) by easy.
  replace ((z::nil) ++ l) with (z::l) by easy.
  rewrite replace_Znth_length in H0.
  rewrite (sublist_cons2 1 n); try lia.
  2:{
    rewrite Zlength_cons.
    rewrite Zlength_cons in H0. lia. 
  }
  rewrite (sublist_cons2 1 n); try lia.
  entailer!.
Qed. 

Lemma proof_of_constr_entail_wit_2 : constr_entail_wit_2.
Proof. 
  pre_process.
  Exists l1 (vnext0_2 ++ (retval::nil)).
  prop_apply (store_int_array_Zlength vnext).
  entailer!.
  rewrite (store_int_array_divide _ (i+1) _ i); try lia.
  2:{ 
    rewrite Zlength_app.
    rewrite H7.
    lazy; auto. 
  }
  rewrite (sublist_split_app_l 0 i); try lia.
  2:{ rewrite <- Zlength_correct; lia. }
  rewrite sublist_self by eauto; entailer!.
  replace (i + 1 - i) with 1 by lia.
  rewrite sublist_split_app_r with (len:=i); [ | auto | lia].
  replace (i-i) with 0 by lia; replace (i+1-i) with 1 by lia.
  rewrite sublist_self by eauto.
  unfold store_int_array, store_array; simpl.
  rewrite Z.add_0_r; entailer!.
Qed. 

Lemma proof_of_constr_return_wit_1 : constr_return_wit_1.
Proof. 
  pre_process.
  prop_apply (store_int_array_length (vnext_2 + i * sizeof ( INT ))); Intros.
  assert (i = n) by lia; subst i; clear H3.
  prop_apply store_char_array_Zlength.  
  Exists vnext0; entailer!.
  - replace (n-n) with 0 by lia.
    prop_apply (store_int_array_Zlength (vnext_2 + n * sizeof ( INT ))).
    Intros; apply Zlength_nil_inv in H4; subst l0.
    unfold store_int_array, store_array; simpl; entailer!.
  - unfold constr_loop_from in H0.
    unfold_loop H0.
    apply string_Zlength in H3.
    safe_choice_r H0.
    auto. lia.
Qed. 

Lemma proof_of_constr_partial_solve_wit_5_pure : constr_partial_solve_wit_5_pure.
Proof. 
  pre_process.
  prop_apply (store_int_array_length vnext).
  prop_apply store_char_array_Zlength.
  entailer! ; apply string_Zlength in H4; 
  rewrite app_Znth1 by lia ; unfold constr_loop_from_after;
  unfold constr_loop_from in *.
  - rewrite range_iter_unfold.
    prog_nf. rewrite choice_l_equiv.
    2:{ prog_nf. apply assume_false_equiv; lia. }
    rewrite assume_equiv by lia.
    unfold constr_body at 1.
    prog_nf.
    rewrite assert_equiv by lia.
    prog_nf.
    easy.
  - 
    unfold_loop H0.
    prog_nf in H0.
    safe_choice_l H0; try lia.
    unfold constr_body at 1 in H0.
    prog_nf in H0.
    safe_step H0. prog_nf in H0.
    auto.
Qed.

Lemma proof_of_constr_which_implies_wit_1 : constr_which_implies_wit_1.
Proof. 
  pre_process.
  prop_apply store_int_array_length; Intros.
  destruct l0.
  simpl in H0; lia.
  Exists z l0; entailer!.
  rewrite <- Zlength_correct in H0.
  rewrite (store_int_array_divide _ (n-i) _ 1) by lia.
  rewrite (sublist_cons1 1) by lia.
  rewrite (sublist_nil l0 0) by lia.
  rewrite sublist_cons2 by lia.
  replace (1-1) with 0 by lia.
  rewrite Zlength_cons in H0.
  rewrite sublist_self by lia.
  replace (vnext + i * sizeof ( INT ) + 1 * sizeof ( INT )) with (vnext + (i + 1) * sizeof ( INT )) by lia.
  replace (n-i-1) with (n-(i+1)) by lia.
  entailer!.
  unfold store_int_array, store_array; simpl; entailer!.
  rewrite Z.add_0_r; easy.
Qed. 

Lemma proof_of_match_entail_wit_1 : match_entail_wit_1.
Proof.
  pre_process.
  subst; entailer!.
Qed. 

Lemma proof_of_match_entail_wit_2 : match_entail_wit_2.
Proof. 
  pre_process.
  prop_apply store_char_array_Zlength; entailer!.
  apply string_Zlength in H14. 
  unfold match_loop_from_after, applyf in H0.
  safe_choice_r H0; [auto | lia].
Qed. 

Lemma proof_of_match_return_wit_1 : match_return_wit_1.
Proof.
  pre_process; subst.
  unfold match_loop_from_after, applyf in H0.
  prop_apply store_char_array_Zlength; Intros.
  apply string_Zlength in H.
  rewrite H in *; clear H.
  Exists (Some(i-n+1)); entailer!.
  safe_choice_l H0; auto.
Qed. 

Lemma proof_of_match_return_wit_2 : match_return_wit_2.
Proof. 
  pre_process.
  prop_apply (store_char_array_Zlength text_pre).
  Exists None; entailer!.
  apply string_Zlength in H11.
  unfold match_loop_from in H0.
  unfold_loop H0.
  prog_nf in H0.
  safe_choice_r H0; [unfold continue in H0 ; prog_nf in H0 ; auto | lia].
Qed. 

Lemma proof_of_match_partial_solve_wit_4_pure : match_partial_solve_wit_4_pure.
Proof. 
  pre_process.
  prop_apply store_char_array_Zlength.
  subst; Intros.
  apply string_Zlength in H4.
  eassert (Heq: _).
  2:{
    entailer!.
    rewrite <- Heq.
    auto.
  }
  unfold match_loop_from_after.
  unfold match_loop_from.
  rewrite (range_iter_break_unfold _ _ i).
  prog_nf.
  rewrite choice_l_equiv.
  2:{ prog_nf. apply assume_false_equiv; lia. }
  rewrite assume_equiv by lia.
  unfold match_body at 1.
  prog_nf.
  rewrite assert_equiv by lia. prog_nf.
  rewrite app_Znth1.
  apply common_step_equiv; intros.
  unfold break , continue.
  prog_nf.
  easy. lia.
Qed. 

Lemma proof_of_match_derive_high_level_spec_by_low_level_spec : match_derive_high_level_spec_by_low_level_spec.
Proof. 
  pre_process.
  Exists patn0 text0 vnext0 n.
  remember (match_loop 0 patn0 text0 vnext0) as prog.
  Exists m (fun (r: option Z) x => prog.(MonadErr.nrm) tt r x).
  do 2 prop_apply store_char_array_Zlength; Intros.
  prop_apply store_int_array_length; Intros.
  apply string_Zlength in H3.
  apply string_Zlength in H4.
  rewrite <- Zlength_correct in H5.
  assert (Zlength patn0 > 0) by lia.
  rewrite <- Zlength_nonnil in H6.
  pose proof match_loop_sound 0 patn0 text0 vnext0 H6 ltac:(lia) H.
  do 2 apply derivable1_wand_sepcon_adjoint.
  entailer!.
  2:{
    destruct H7 as [_ H7].
    specialize (H7 tt).
    subst prog; apply safeExec_monad_Atrue_finnal; tauto.
  }
  apply derivable1_wand_sepcon_adjoint.
  entailer!. Intros ret retval.
  destruct H7 as [H7 _].
  apply safeExec_ret_Atrue_finnal in H8.
  destruct H8 as [σ H8]; subst prog.
  specialize (H7 ret tt σ I H8).
  destruct ret; simpl in H9.
  - Left; Exists z.
    subst retval; entailer!.
    apply first_occur_nonneg in H7; auto.
  - Right; Exists (-1); entailer!.
Qed.

Lemma proof_of_constr_derive_high_level_spec_by_low_level_spec : constr_derive_high_level_spec_by_low_level_spec.
Proof. 
  pre_process.
  prop_apply store_char_array_Zlength; Intros.
  apply string_Zlength in H1.
  Exists str n.
  assert (Zlength str > 0) by lia.
  apply Zlength_nonnil in H2.
  pose proof constr_loop_sound 0 str H2.
  Exists (fun r x => (constr_loop 0 str).(MonadErr.nrm) tt r x).
  entailer!.
  2:{
    destruct H3 as [_ H3].
    specialize (H3 tt I).
    apply safeExec_monad_Atrue_finnal; tauto.
  }
  apply derivable1_wand_sepcon_adjoint.
  entailer!; Intros vnext retval.
  Exists vnext retval; entailer!.
  destruct H3 as [H3 _].
  apply safeExec_ret_Atrue_finnal in H4.
  destruct H4 as [σ H4].
  specialize (H3 vnext tt σ I H4); tauto.
Qed. 

Lemma proof_of_inner_derive_bind_spec_by_low_level_spec : inner_derive_bind_spec_by_low_level_spec.
Proof.
  pre_process.
  prop_apply store_char_array_Zlength; Intros.
  prop_apply store_int_array_Zlength; Intros.
  apply string_Zlength in H2.
  apply safeExec_bind in H as (X' & H7 & H8).
  Exists str0 vnext0.
  Exists n m X'; entailer!.
  apply derivable1_wand_sepcon_adjoint; entailer!.
  Intros ret; Exists ret; entailer!.
Qed. 