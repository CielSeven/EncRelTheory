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
From SimpleC.EE Require Import sll_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Require Import sll_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  sep_apply (sllseg_len1 q_tail); [ | tauto].
  sep_apply (sllseg_sllseg q_head).
  Exists q_head retval.
  Exists retval_data retval_next.
  entailer!.
Qed.

Lemma proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Intros h t u v.
  Exists h v u t.
  entailer!.
Qed.

Lemma proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Exists q_head_next q_tail u v.
  entailer!.
Qed.

Lemma proof_of_dequeue_which_implies_wit_1 : dequeue_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Intros h t u v.
  simpl.
  Intros h_next.
  Exists h_next h v u t.
  entailer!.
Qed.

Lemma proof_of_init_empty_queue_return_wit_1 : init_empty_queue_return_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Exists retval_2 retval_2 retval_data retval_next.
  simpl sllseg.
  entailer!.
Qed.
