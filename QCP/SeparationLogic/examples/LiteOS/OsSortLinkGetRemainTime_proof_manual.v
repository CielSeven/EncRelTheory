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
From LOS_Verify.VC.code.link Require Import OsSortLinkGetRemainTime_goal.
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

Lemma proof_of_OsSortLinkGetRemainTime_return_wit_1 : OsSortLinkGetRemainTime_return_wit_1.
Proof. 
    unfold OsSortLinkGetRemainTime_return_wit_1.  
    pre_process.
    intros.
    Right.
    entailer!.
    unfold storesortedLinkNode.
    simpl.
    entailer!.
    Exists targetSortList_pre.
    entailer!.
Qed. 

Lemma proof_of_OsSortLinkGetRemainTime_return_wit_2 : OsSortLinkGetRemainTime_return_wit_2.
Proof. 
    unfold OsSortLinkGetRemainTime_return_wit_2.
    pre_process.
    intros.
    Left.
    prop_apply (store_uint64_range (&(targetSortList_pre # "SortLinkList" ->ₛ "responseTime")) t).
    unfold storesortedLinkNode.
    simpl.
    entailer!.
    simpl.
    
    Exists targetSortList_pre.
    entailer!.
    pose proof (unsigned_last_nbits_eq (t - currTime_pre) 64).
    assert (0 <= t - currTime_pre).
    apply Z.lt_le_incl.
    lia. 
    assert ( t - currTime_pre < 2 ^ 64).
    assert (Hmax: t <= 2^64 - 1) by apply H1.
    assert (Ht_range : t < 2 ^ 64).
    apply Z.le_lt_trans with (2 ^ 64 - 1).
    apply Hmax.
    compute. 
    reflexivity.
    assert (Hdiff_leq_t : t - currTime_pre <= t).
    apply Z.le_sub_nonneg.
    lia.
    lia.
    lia.
Qed. 



Lemma proof_of_OsSortLinkGetRemainTime_which_implies_wit_1 : OsSortLinkGetRemainTime_which_implies_wit_1.
Proof. 
  unfold OsSortLinkGetRemainTime_which_implies_wit_1. 
  unfold storesortedLinkNode.
  pre_process.
  simpl.
  entailer!.
  Intros y.
  apply addr_of_arrow_field_inv in H.
  entailer!.
  rewrite H.
  entailer!.
Qed.


