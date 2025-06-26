Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE Require Import sll_queue_strategy_goal.
Require Import sll_lib.
Require Import sll_queue_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_queue_strategy0_correctness : sll_queue_strategy0.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma sll_queue_strategy1_correctness : sll_queue_strategy1.
  pre_process_default.
  Intros; subst; entailer!.
Qed.
