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
From LOS_Verify.VC.strategy Require Import common_strategy_goal.
From LOS_Verify.VC.strategy Require Import common_strategy_proof.
From LOS_Verify.VC.strategy Require Import los_sortlink_strategy_goal.
From LOS_Verify.VC.strategy Require Import los_sortlink_strategy_proof.

(*----- Function OsSortLinkGetRemainTime -----*)

Definition OsSortLinkGetRemainTime_return_wit_1 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  [| (currTime_pre >= t) |] 
  &&  [| (currTime_pre >= 0) |]
  &&  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  ([| (currTime_pre < t) |] 
  &&  [| (0 = (t - currTime_pre )) |]
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) ))
  ||
  ([| (currTime_pre >= t) |] 
  &&  [| (0 = 0) |]
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) ))
.

Definition OsSortLinkGetRemainTime_return_wit_2 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  [| (currTime_pre < t) |] 
  &&  [| (currTime_pre >= 0) |]
  &&  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  ([| (currTime_pre < t) |] 
  &&  [| ((unsigned_last_nbits ((t - currTime_pre )) (64)) = (t - currTime_pre )) |]
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) ))
  ||
  ([| (currTime_pre >= t) |] 
  &&  [| ((unsigned_last_nbits ((t - currTime_pre )) (64)) = 0) |]
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) ))
.

Definition OsSortLinkGetRemainTime_partial_solve_wit_1 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  [| (currTime_pre >= 0) |]
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  [| (currTime_pre >= 0) |]
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition OsSortLinkGetRemainTime_which_implies_wit_1 := 
forall (A: Type) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (targetSortList: Z) ,
  (storesortedLinkNode storeA &((targetSortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((targetSortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsSortLinkGetRemainTime_return_wit_1 : OsSortLinkGetRemainTime_return_wit_1.
Axiom proof_of_OsSortLinkGetRemainTime_return_wit_2 : OsSortLinkGetRemainTime_return_wit_2.
Axiom proof_of_OsSortLinkGetRemainTime_partial_solve_wit_1 : OsSortLinkGetRemainTime_partial_solve_wit_1.
Axiom proof_of_OsSortLinkGetRemainTime_which_implies_wit_1 : OsSortLinkGetRemainTime_which_implies_wit_1.

End VC_Correct.
