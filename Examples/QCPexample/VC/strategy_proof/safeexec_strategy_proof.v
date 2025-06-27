Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import safeexec_strategy_goal.
Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma safeexec_strategy3_correctness : safeexec_strategy3.
  pre_process_default.
Admitted.

Lemma safeexec_strategy4_correctness : safeexec_strategy4.
  pre_process_default.
Admitted.

Lemma safeexec_strategy5_correctness : safeexec_strategy5.
  pre_process_default.
Admitted.

Lemma safeexec_strategy8_correctness : safeexec_strategy8.
  pre_process_default.
Admitted.

Lemma safeexec_strategy9_correctness : safeexec_strategy9.
  pre_process_default.
Admitted.

Lemma safeexec_strategy1_correctness : safeexec_strategy1.
  pre_process_default.
Admitted.

Lemma safeexec_strategy6_correctness : safeexec_strategy6.
  pre_process_default.
Admitted.

Lemma safeexec_strategy7_correctness : safeexec_strategy7.
  pre_process_default.
Admitted.

Lemma safeexec_strategy2_correctness : safeexec_strategy2.
  pre_process_default.
Admitted.
