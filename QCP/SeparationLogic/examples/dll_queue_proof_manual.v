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
From SimpleC.EE Require Import dll_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import dll_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_return_wit_1_1 : enqueue_return_wit_1_1.
Proof.
  pre_process.
  subst.
  unfold store_queue.
  Exists q_head retval.
  sep_apply dllseg_len1; [ | tauto ].
  sep_apply dllseg_len1; [ | tauto ].
  sep_apply (dllseg_dllseg q_head).
  sep_apply (dllseg_dllseg q_head).
  entailer!.
Qed.

Lemma proof_of_enqueue_return_wit_1_2 : enqueue_return_wit_1_2.
Proof.
  pre_process.
  subst.
  unfold store_queue.
  Exists retval retval.
  sep_apply dllseg_head_zero; [ | tauto ].
  sep_apply dllseg_len1; [ | tauto ].
  entailer!.
  subst l.
  entailer!.
Qed.

Lemma proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Proof.
  pre_process.
  intros.
  unfold store_queue.
  Intros h t; Exists h t.
  entailer!.
Qed.

Lemma proof_of_enqueue_which_implies_wit_2 : enqueue_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply dllseg_head_neq_destruct_tail; [ | tauto ].
  Intros z l0 a.
  Exists z 0 l0 a.
  entailer!.
Qed.

Lemma proof_of_dequeue_return_wit_1_1 : dequeue_return_wit_1_1.
Proof.
  pre_process.
  subst.
  unfold store_queue.
  Exists q_head_next_2 q_tail.
  simpl.
  Exists q_head_next.
  entailer!.
Qed.

Lemma proof_of_dequeue_return_wit_1_2 : dequeue_return_wit_1_2.
Proof.
  pre_process.
  subst.
  unfold store_queue.
  sep_apply dllseg_head_zero; [ | tauto ].
  Intros.
  subst.
  Exists 0 0.
  simpl.
  entailer!.
Qed.

Lemma proof_of_dequeue_which_implies_wit_1 : dequeue_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_queue.
  Intros h t.
  simpl.
  Intros h_next.
  Exists h_next t 0 h.
  entailer!.
Qed.

Lemma proof_of_dequeue_which_implies_wit_2 : dequeue_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply dllseg_head_neq; [ | tauto ].
  Intros z a l0.
  Exists z a l0.
  entailer!.
Qed.
