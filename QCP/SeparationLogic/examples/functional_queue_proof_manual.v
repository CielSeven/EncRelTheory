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
From SimpleC.EE Require Import functional_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Require Import functional_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  subst.
  Exists q_l1 p_pre_v l1 (x_pre :: l2).
  entailer!.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Intros p1 p2 l1 l2.
  Exists p2 p1 l1 l2.
  entailer!.
Qed.

Lemma proof_of_dequeue_return_wit_1_1 : dequeue_return_wit_1_1.
Proof.
  pre_process.
  subst.
  unfold store_queue.
  simpl in H2.
  injection H2 as ? ?.
  subst.
  Exists p_pre_v q_l2 l1_tail l2.
  entailer!.
Qed.

Lemma proof_of_dequeue_return_wit_1_2 : dequeue_return_wit_1_2.
Proof.
  pre_process.
  subst.
  unfold store_queue.
  Exists p_pre_v 0 l nil.
  sep_apply (sll_zero 0); [ | tauto ].
  Intros.
  subst.
  entailer!.
  + simpl.
    entailer!.
  + simpl.
    rewrite app_nil_r.
    reflexivity.
Qed.

Lemma proof_of_dequeue_partial_solve_wit_3_pure : dequeue_partial_solve_wit_3_pure.
Proof.
  pre_process.
  subst.
  sep_apply (sll_zero 0); auto.
  clear H; entailer!.
  subst; rewrite app_nil_l in H0.
  auto.
Qed.

Lemma proof_of_dequeue_which_implies_wit_1 : dequeue_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Intros p1 p2 l1 l2.
  Exists p2 p1 l1 l2.
  entailer!.
Qed.

Lemma proof_of_dequeue_which_implies_wit_3 : dequeue_which_implies_wit_3.
Proof.
  pre_process.
  sep_apply sll_not_zero; [ | tauto].
  Intros y a l0.
  Exists a l0.
  simpl.
  Exists y.
  entailer!.
Qed.
