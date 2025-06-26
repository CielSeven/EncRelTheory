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

(*----- Function GET_SORTLIST_VALUE -----*)

Definition GET_SORTLIST_VALUE_return_wit_1 := 
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  [| (t = t) |]
  &&  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition GET_SORTLIST_VALUE_partial_solve_wit_1 := 
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) ,
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition GET_SORTLIST_VALUE_which_implies_wit_1 := 
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

(*----- Function SET_SORTLIST_VALUE -----*)

Definition SET_SORTLIST_VALUE_return_wit_1 := 
forall (A: Type) (value_pre: Z) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (a: A) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> value_pre)
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (value_pre)) )
.

Definition SET_SORTLIST_VALUE_partial_solve_wit_1 := 
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) ,
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition SET_SORTLIST_VALUE_which_implies_wit_1 := 
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_GET_SORTLIST_VALUE_return_wit_1 : GET_SORTLIST_VALUE_return_wit_1.
Axiom proof_of_GET_SORTLIST_VALUE_partial_solve_wit_1 : GET_SORTLIST_VALUE_partial_solve_wit_1.
Axiom proof_of_GET_SORTLIST_VALUE_which_implies_wit_1 : GET_SORTLIST_VALUE_which_implies_wit_1.
Axiom proof_of_SET_SORTLIST_VALUE_return_wit_1 : SET_SORTLIST_VALUE_return_wit_1.
Axiom proof_of_SET_SORTLIST_VALUE_partial_solve_wit_1 : SET_SORTLIST_VALUE_partial_solve_wit_1.
Axiom proof_of_SET_SORTLIST_VALUE_which_implies_wit_1 : SET_SORTLIST_VALUE_which_implies_wit_1.

End VC_Correct.
