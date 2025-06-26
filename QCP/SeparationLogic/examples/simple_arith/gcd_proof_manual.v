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
From SimpleC.EE.simple_arith Require Import gcd_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_gcd_return_wit_1 : gcd_return_wit_1.
Proof.
  unfold gcd_return_wit_1.
  intros.
  entailer!.
  subst.
  rewrite Z.gcd_0_r.
  reflexivity.
Qed.

Lemma proof_of_gcd_return_wit_2 : gcd_return_wit_2.
Proof.
  unfold gcd_return_wit_2.
  intros.
  entailer!.
  subst.
  pose proof Z.gcd_rem x_pre y_pre ltac:(lia).
  rewrite Z.gcd_comm, H, Z.gcd_comm.
  reflexivity.
Qed.

Lemma proof_of_gcd_partial_solve_wit_2_pure : gcd_partial_solve_wit_2_pure.
Proof.
  pre_process.
  prop_apply (store_int_range  (&("y")) y_pre).
  Intros. 
  change (Int.min_signed) with (-2147483648) in H3.
  change (Int.max_signed) with (2147483647) in H3.
  pose proof Z.rem_bound_pos_pos x_pre y_pre.
  pose proof Z.rem_bound_neg_pos x_pre y_pre.
  pose proof Z.rem_bound_pos_neg x_pre y_pre.
  pose proof Z.rem_bound_neg_neg x_pre y_pre.
  entailer!.
Qed.
