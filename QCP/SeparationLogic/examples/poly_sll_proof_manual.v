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
From SimpleC.EE Require Import poly_sll_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import poly_sll_lib.
Local Open Scope sac.

Lemma proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Proof.
  pre_process.
  Exists nil l.
  simpl.
  entailer!.
Qed.

Lemma proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Proof.
  pre_process.
  Exists (x :: l1_2) xs.
  entailer!.
  + simpl sll.
    Exists v_data w.
    entailer!.
  + subst l2_2.
    simpl.
    rewrite <- app_assoc.
    simpl.
    apply H1.
Qed.

Lemma proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Proof.
  pre_process.
  sep_apply (sll_zero _ storeA v l2); [ | tauto].
  entailer!.
  subst l2.
  rewrite app_nil_r in H0.
  subst l.
  rewrite rev_involutive.
  entailer!.
Qed.
