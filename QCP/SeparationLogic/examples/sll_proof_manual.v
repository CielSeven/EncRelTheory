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
From SimpleC.EE Require Import sll_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Local Open Scope sac.

Lemma proof_of_length_entail_wit_1 : length_entail_wit_1.
Proof.
  pre_process.
  Exists nil l.
  entailer!.
  simpl. entailer!.
Qed.

Lemma proof_of_length_entail_wit_2 : length_entail_wit_2.
Proof.
  pre_process.
  Exists (l1_2 ++ (p_data::nil)) l3.
  entailer!; simpl.
  - sep_apply sllseg_len1; try easy.
    rewrite logic_equiv_sepcon_comm.
    sep_apply sllseg_sllseg.
    easy.
  - rewrite Zlength_app.
    rewrite <- H2.
    rewrite Zlength_cons. rewrite Zlength_nil. lia.
  - rewrite H1, H; clear H H1. 
    rename l1_2 into l1.
    revert l1 H2.
    induction l3; intros; simpl.
    + rewrite app_nil_r. auto.
    + rewrite <- app_assoc. simpl. f_equal. 
Qed. 

Lemma proof_of_length_return_wit_1 : length_return_wit_1.
Proof. 
  pre_process.
  rewrite H. sep_apply sll_zero; auto.
  Intros. 
  rewrite H4 in H0. 
  rewrite app_nil_r in H0. subst. 
  entailer!. clear H2.
  revert p_pre; induction l1; simpl; try easy.
  intros; Intros.
  Intros z; Exists z. entailer!.
Qed.

Lemma proof_of_length_safety_wit_2 : length_safety_wit_2.
Proof.
  pre_process.
  entailer!.
  - pose proof Zlength_nonneg l1. lia.
  - pose proof Zlength_app l1 l2.
    rewrite <- H1 in H4.
    pose proof Zlength_cons p_data l3.
    rewrite <- H in H5.
    pose proof Zlength_nonneg l3. lia.
Qed.

Lemma proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Proof.
  pre_process.
  Exists nil l.
  simpl sll.
  entailer!.
Qed.

Lemma proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Proof.
  pre_process.
  Exists (v_data :: l1_2) l2_new.
  entailer!.
  + simpl sll.
    Exists w.
    entailer!.
  + subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    apply H1.
Qed.

Lemma proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Proof.
  pre_process.
  sep_apply (sll_zero v l2); [ | tauto].
  entailer!.
  subst l2.
  rewrite app_nil_r in H0.
  subst l.
  rewrite rev_involutive.
  entailer!.
Qed.

Lemma proof_of_reverse_alter_style1_entail_wit_1 : reverse_alter_style1_entail_wit_1.
Proof.
  pre_process.
  Exists nil l.
  simpl sll.
  entailer!.
Qed.

Lemma proof_of_reverse_alter_style1_entail_wit_2 : reverse_alter_style1_entail_wit_2.
Proof.
  pre_process.
  Exists (x :: l1_2) xs.
  entailer!.
  + simpl sll.
    Exists w.
    entailer!.
  + subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    apply H1.
Qed.

Lemma proof_of_reverse_alter_style1_return_wit_1 : reverse_alter_style1_return_wit_1.
Proof.
  pre_process.
  sep_apply (sll_zero v l2); [ | tauto].
  entailer!.
  subst l2.
  rewrite app_nil_r in H0.
  subst l.
  rewrite rev_involutive.
  entailer!.
Qed.

Lemma proof_of_reverse_alter_style2_entail_wit_1 : reverse_alter_style2_entail_wit_1.
Proof.
  pre_process.
  Exists nil l.
  simpl sll.
  entailer!.
Qed.

Lemma proof_of_reverse_alter_style2_entail_wit_2 : reverse_alter_style2_entail_wit_2.
Proof.
  pre_process.
  Exists (x :: l1_2) xs.
  entailer!.
  + simpl sll.
    Exists w_inv.
    entailer!.
  + subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    apply H1.
Qed.

Lemma proof_of_reverse_alter_style3_entail_wit_3 : reverse_alter_style3_entail_wit_3.
Proof.
  pre_process.
  Exists nil l.
  entailer!.
Qed.

Lemma proof_of_reverse_alter_style3_entail_wit_4 : reverse_alter_style3_entail_wit_4.
Proof.
  pre_process.
  Exists (v_data :: l1_2) l2_new.
  entailer!.
  + simpl sll.
    Exists w.
    entailer!.
  + subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    apply H1.
Qed.

Lemma proof_of_reverse_alter_style3_return_wit_1 : reverse_alter_style3_return_wit_1.
Proof.
  pre_process.
  sep_apply (sll_zero v l2); [ | tauto].
  entailer!.
  subst l2.
  rewrite app_nil_r in H0.
  subst l.
  rewrite rev_involutive.
  entailer!.
Qed.

Lemma proof_of_reverse_alter_style2_return_wit_1 : reverse_alter_style2_return_wit_1.
Proof.
  pre_process.
  sep_apply (sll_zero v_inv l2); [ | tauto].
  entailer!.
  subst l2.
  rewrite app_nil_r in H0.
  subst l.
  rewrite rev_involutive.
  entailer!.
Qed.

Lemma proof_of_append_entail_wit_1 : append_entail_wit_1.
Proof.
  pre_process.
  Exists x_next nil x_data l1n.
  entailer!.
  simpl sllseg.
  entailer!.
Qed.

Lemma proof_of_append_entail_wit_2 : append_entail_wit_2.
Proof.
  pre_process.
  subst t_next_2 l1b_2.
  Exists u_next (l1a_2 ++ (t_data_2 :: nil))%list u_data l1b_new.
  entailer!.
  + sep_apply (sllseg_len1 t t_data_2 u); [ | tauto ].
    sep_apply (sllseg_sllseg x).
    entailer!.
  + rewrite <- app_assoc.
    simpl.
    apply H1.
Qed.

Lemma proof_of_append_return_wit_1 : append_return_wit_1.
Proof.
  pre_process.
  sep_apply (sll_zero x_pre); [ | tauto ].
  Intros.
  subst l1.
  entailer!.
Qed.

Lemma proof_of_append_return_wit_2 : append_return_wit_2.
Proof.
  pre_process.
  subst t_next l1.
  rewrite <- app_assoc.
  sep_apply (sll_zero u); [ | tauto].
  sep_apply (sllseg_len1 t t_data y); [ | tauto ].
  Intros.
  subst l1b.
  sep_apply (sllseg_sll t).
  sep_apply sllseg_sll.
  entailer!.
Qed.

Lemma proof_of_append_long_entail_wit_1 : append_long_entail_wit_1.
Proof.
  pre_process.
  Exists xn nil a l1b.
  entailer!.
  simpl sllseg.
  entailer!.
Qed.

Lemma proof_of_append_long_entail_wit_2 : append_long_entail_wit_2.
Proof.
  pre_process.
  subst t_next_2 l1c_2.
  Exists un (l1a_2 ++ (b_2 :: nil))%list c l1d.
  entailer!.
  + sep_apply (sllseg_len1 t b_2 u); [ | tauto ].
    sep_apply (sllseg_sllseg x).
    entailer!.
  + rewrite <- app_assoc.
    simpl.
    apply H1.
Qed.

Lemma proof_of_append_long_return_wit_1 : append_long_return_wit_1.
Proof.
  pre_process.
  sep_apply (sll_zero x_pre); [ | tauto ].
  Intros.
  subst l1.
  entailer!.
Qed.

Lemma proof_of_append_long_return_wit_2 : append_long_return_wit_2.
Proof.
  pre_process.
  subst xn.
  sep_apply (sllseg_len1 x_pre a y_pre); [ | tauto ].
  sep_apply (sllseg_sll x_pre y_pre (a :: nil)%list l2).
  sep_apply (sll_zero 0); [ | tauto ].
  Intros.
  subst l1b.
  rewrite <- H0.
  entailer!.
Qed.

Lemma proof_of_append_long_return_wit_3 : append_long_return_wit_3.
Proof.
  pre_process.
  subst t_next l1.
  rewrite <- app_assoc.
  sep_apply (sll_zero u); [ | tauto].
  sep_apply (sllseg_len1 t b y); [ | tauto ].
  Intros.
  subst l1c.
  sep_apply (sllseg_sll t).
  sep_apply sllseg_sll.
  entailer!.
Qed.

Lemma proof_of_append_2p_entail_wit_1 : append_2p_entail_wit_1.
Proof.
  pre_process.
  Exists nil l1.
  simpl sllbseg.
  entailer!.
Qed.

Lemma proof_of_append_2p_entail_wit_2 : append_2p_entail_wit_2.
Proof.
  pre_process.
  sep_apply (sll_not_zero pt_v_2); [ | tauto ].
  Intros ptn a l0.
  Exists ptn (l1a_2 ++ a :: nil)%list l0.
  entailer!.
  + sep_apply sllbseg_len1; [ | tauto ].
    sep_apply (sllbseg_sllbseg (&( "x" ))).
    entailer!.
  + subst l1b_2.
    rewrite <- app_assoc.
    simpl.
    apply H0.
Qed.

Lemma proof_of_append_2p_return_wit_1 : append_2p_return_wit_1.
Proof.
  pre_process.
  sep_apply (sll_zero pt_v); [ | tauto ].
  Intros.
  sep_apply sllseg_sll.
  subst l1b.
  rewrite app_nil_r in H0.
  subst l1a.
  entailer!.
Qed.

Lemma proof_of_append_2p_which_implies_wit_1 : append_2p_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply sllbseg_2_sllseg.
  Intros y'.
  Exists y'.
  subst pt_v.
  entailer!.
Qed.
