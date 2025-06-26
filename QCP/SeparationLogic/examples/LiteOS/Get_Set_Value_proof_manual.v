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
From LOS_Verify.VC.code.link Require Import Get_Set_Value_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Require Import LOS_Verify.lib.sortlink.
Require Import LOS_Verify.lib.dll.
Require Import LOS_Verify.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_GET_SORTLIST_VALUE_return_wit_1 : GET_SORTLIST_VALUE_return_wit_1.
Proof. 
    unfold GET_SORTLIST_VALUE_return_wit_1.
    pre_process.
    intros.
    unfold storesortedLinkNode.
    entailer!.
    Exists sortList_pre.
    entailer!.
Qed. 

Lemma proof_of_GET_SORTLIST_VALUE_which_implies_wit_1 : GET_SORTLIST_VALUE_which_implies_wit_1.
Proof. 
    unfold GET_SORTLIST_VALUE_which_implies_wit_1.
    pre_process.
    intros.
    unfold storesortedLinkNode.
    Intros y.
    entailer!.
    apply addr_of_arrow_field_inv in H.
    rewrite H.
    entailer!.
Qed. 

Lemma proof_of_SET_SORTLIST_VALUE_return_wit_1 : SET_SORTLIST_VALUE_return_wit_1.
Proof. 
    unfold SET_SORTLIST_VALUE_return_wit_1. 
    pre_process.
    intros.
    unfold storesortedLinkNode.
    entailer!.
    Exists sortList_pre.
    entailer!.
Qed.

Lemma proof_of_SET_SORTLIST_VALUE_which_implies_wit_1 : SET_SORTLIST_VALUE_which_implies_wit_1.
Proof. 
    unfold SET_SORTLIST_VALUE_which_implies_wit_1.
    pre_process.
    intros.
    unfold storesortedLinkNode.
    Intros y.
    entailer!.
    apply addr_of_arrow_field_inv in H.
    rewrite H.
    entailer!.
Qed. 

