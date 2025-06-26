Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
Require Import int_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Require Import Coq.micromega.Lia.

Lemma int_array_strategy1_correctness : int_array_strategy1.
  pre_process_default.
  prop_apply (store_int_array_length). Intros.
  sep_apply (store_int_array_split p i); [ | tauto].
  entailer!.
  Intros_r v.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma int_array_strategy4_correctness : int_array_strategy4.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma int_array_strategy5_correctness : int_array_strategy5.
Proof.  
  pre_process_default.
Qed.

Lemma int_array_strategy6_correctness : int_array_strategy6.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma int_array_strategy7_correctness : int_array_strategy7.
  pre_process_default.
  sep_apply (store_int_array_rec_split p x i y); [ | tauto].
  entailer!.
  Intros_r_any.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  Intros; subst; entailer!.
Qed.

Lemma int_array_strategy8_correctness : int_array_strategy8.
  pre_process_default.
  Intros; subst.
  prop_apply (store_int_array_rec_Zlength p x y).
  prop_apply (store_int_array_rec_Zlength p y z).
  Intros.
  rewrite (store_int_array_rec_divide p x z (l1 ++ l2) y);[ | lia | ].
  rewrite <- H1.
  rewrite sublist_app_exact1 by lia.
  rewrite sublist_split_app_r with (len := Zlength l1) by lia.
  replace (Zlength l1 - Zlength l1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_app. lia.
Qed.

Lemma int_array_strategy9_correctness : int_array_strategy9.
  pre_process_default.
  Intros. subst.
  prop_apply (store_int_array_rec_Zlength p x z).
  Intros.
  rewrite (store_int_array_rec_divide p x z (l1 ++ l2) y);[ | lia | auto].
  rewrite <- H2.
  rewrite sublist_app_exact1 by lia.
  rewrite sublist_split_app_r with (len := Zlength l1) by lia.
  rewrite Zlength_app in H1.
  replace (Zlength l1 - Zlength l1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
Qed.

Lemma int_array_strategy10_correctness : int_array_strategy10.
  pre_process_default.
  unfold store_int_array_rec.
  Intros;subst.
  cbn.
  entailer!.
Qed.

Lemma int_array_strategy2_correctness : int_array_strategy2.
  pre_process_default.
  simpl.
  sep_apply (store_int_array_merge); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma int_array_strategy11_correctness : int_array_strategy11.
  pre_process_default.
  simpl.
  sep_apply (store_int_array_rec_merge); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma int_array_strategy3_correctness : int_array_strategy3.
  pre_process_default.
  simpl.
  sep_apply (store_int_array_merge); [ | tauto].
  entailer!.
Qed.

Lemma int_array_strategy12_correctness : int_array_strategy12.
  pre_process_default.
  simpl.
  sep_apply (store_int_array_rec_merge); [ | tauto].
  entailer!.
Qed.
