Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
Require Import char_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma char_array_strategy1_correctness : char_array_strategy1.
  pre_process_default.
  prop_apply (store_char_array_length). Intros.
  sep_apply (store_char_array_split p i); [ | tauto].
  entailer!.
  Intros_r v.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma char_array_strategy4_correctness : char_array_strategy4.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma char_array_strategy5_correctness : char_array_strategy5.
  pre_process_default.
Qed.

Lemma char_array_strategy6_correctness : char_array_strategy6.
  pre_process_default.
  prop_apply store_char_array_length.
  rewrite <- Zlength_correct.
  entailer!.
  pose proof Zlength_nonneg l1; subst; auto.
Qed.

Lemma char_array_strategy2_correctness : char_array_strategy2.
  pre_process_default.
  simpl.
  sep_apply (store_char_array_merge); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma char_array_strategy3_correctness : char_array_strategy3.
  pre_process_default.
  simpl.
  sep_apply (store_char_array_merge); [ | tauto].
  entailer!.
Qed.
