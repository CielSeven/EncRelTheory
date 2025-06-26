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

(*----- Function OsDeleteNodeSortLink -----*)

Definition OsDeleteNodeSortLink_safety_wit_1 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_pre_pstNext: Z) (node_pre_pstPrev: Z) ,
  [| (node_pre_pstPrev = 0) |] 
  &&  [| (node_pre_pstNext = 0) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) ) |]
  &&  ((( &( "sortList" ) )) # Ptr  |-> sortList_pre)
  **  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_pre_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_pre_pstNext)
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition OsDeleteNodeSortLink_safety_wit_2 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_pre_pstNext: Z) (node_pre_pstPrev: Z) ,
  [| (node_pre_pstPrev = 0) |] 
  &&  [| (node_pre_pstNext = 0) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) ) |]
  &&  ((( &( "sortList" ) )) # Ptr  |-> sortList_pre)
  **  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_pre_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_pre_pstNext)
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition OsDeleteNodeSortLink_return_wit_1 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_pre_pstNext: Z) (node_pre_pstPrev: Z) ,
  [| (node_pre_pstPrev = 0) |] 
  &&  [| (node_pre_pstNext = 0) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) ) |]
  &&  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (unsigned_last_nbits ((-1)) (64)))
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_pre_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_pre_pstNext)
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  EX v v_2,
  [| (v_2 = 0) |] 
  &&  [| (v = 0) |]
  &&  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
.

Definition OsDeleteNodeSortLink_partial_solve_wit_1 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )
.

Definition OsDeleteNodeSortLink_partial_solve_wit_2 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) ,
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) ) |]
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
|--
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) ) |]
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
.

Definition OsDeleteNodeSortLink_partial_solve_wit_3 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_pre_pstNext: Z) (node_pre_pstPrev: Z) ,
  [| (node_pre_pstPrev = 0) |] 
  &&  [| (node_pre_pstNext = 0) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) ) |]
  &&  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_pre_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_pre_pstNext)
  **  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  [| (node_pre_pstPrev = 0) |] 
  &&  [| (node_pre_pstNext = 0) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) ) |]
  &&  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_pre_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_pre_pstNext)
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
.

Definition OsDeleteNodeSortLink_which_implies_wit_1 := 
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (sortList: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList))) (l2)))) )
|--
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList))) (l2)))) ) |]
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((sortList)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
.

Definition OsDeleteNodeSortLink_which_implies_wit_2 := 
forall (A: Type) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsDeleteNodeSortLink_safety_wit_1 : OsDeleteNodeSortLink_safety_wit_1.
Axiom proof_of_OsDeleteNodeSortLink_safety_wit_2 : OsDeleteNodeSortLink_safety_wit_2.
Axiom proof_of_OsDeleteNodeSortLink_return_wit_1 : OsDeleteNodeSortLink_return_wit_1.
Axiom proof_of_OsDeleteNodeSortLink_partial_solve_wit_1 : OsDeleteNodeSortLink_partial_solve_wit_1.
Axiom proof_of_OsDeleteNodeSortLink_partial_solve_wit_2 : OsDeleteNodeSortLink_partial_solve_wit_2.
Axiom proof_of_OsDeleteNodeSortLink_partial_solve_wit_3 : OsDeleteNodeSortLink_partial_solve_wit_3.
Axiom proof_of_OsDeleteNodeSortLink_which_implies_wit_1 : OsDeleteNodeSortLink_which_implies_wit_1.
Axiom proof_of_OsDeleteNodeSortLink_which_implies_wit_2 : OsDeleteNodeSortLink_which_implies_wit_2.

End VC_Correct.
