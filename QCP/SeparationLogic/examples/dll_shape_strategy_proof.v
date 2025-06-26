Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE Require Import dll_shape_strategy_goal.
Require Import dll_shape_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma dll_shape_strategy1_correctness : dll_shape_strategy1.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy2_correctness : dll_shape_strategy2.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy3_correctness : dll_shape_strategy3.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy4_correctness : dll_shape_strategy4.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy7_correctness : dll_shape_strategy7.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy9_correctness : dll_shape_strategy9.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy8_correctness : dll_shape_strategy8.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy10_correctness : dll_shape_strategy10.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy11_correctness : dll_shape_strategy11.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy5_correctness : dll_shape_strategy5.
  pre_process_default.
Admitted.

Lemma dll_shape_strategy6_correctness : dll_shape_strategy6.
  pre_process_default.
Admitted.
