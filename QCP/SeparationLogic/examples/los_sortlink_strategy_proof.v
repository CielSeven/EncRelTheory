Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import los_sortlink_strategy_goal.
Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Require Import LOS_Verify.lib.glob_vars_and_defs.
Require Import LOS_Verify.lib.dll.
Require Import lib.sortlink.
Require Import LOS_Verify.lib.tick.
Import DLL.
Import SDLL.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma los_sortlink_strategy7_correctness : los_sortlink_strategy7.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_strategy14_correctness : los_sortlink_strategy14.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_strategy15_correctness : los_sortlink_strategy15.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_strategy18_correctness : los_sortlink_strategy18.
  pre_process_default.
Qed.

Lemma los_sortlink_strategy19_correctness : los_sortlink_strategy19.
  pre_process_default.
  entailer!.
  rewrite H.
  rewrite H0.
  congruence.
Qed.


Lemma los_sortlink_strategy6_correctness : los_sortlink_strategy6.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.


Lemma los_sortlink_strategy20_correctness : los_sortlink_strategy20.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  rewrite H0.
  rewrite H1.
  simpl.
  csimpl.
  destruct a1.
  simpl.
  destruct data0.
  simpl.
  congruence.
Qed.

Lemma los_sortlink_strategy21_correctness : los_sortlink_strategy21.
  pre_process_default.
  intros.
  entailer!.
  simpl.
  rewrite H.
  rewrite H0.
  entailer!.
Qed.

Lemma los_sortlink_strategy22_correctness : los_sortlink_strategy22.
  pre_process_default.
  intros.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_strategy17_correctness : los_sortlink_strategy17.
  pre_process_default.
  intros.
  entailer!.
  Exists x.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_strategy3_correctness : los_sortlink_strategy3.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_strategy8_correctness : los_sortlink_strategy8.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_strategy11_correctness : los_sortlink_strategy11.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.


Lemma los_sortlink_strategy16_correctness : los_sortlink_strategy16.
  pre_process_default.
  intros.
  entailer!.
  Intros x0.
  rewrite H.
  entailer!.
Qed.
