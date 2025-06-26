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

(*----- Function OsSortLinkResponseTimeConvertFreq -----*)

Definition OsSortLinkResponseTimeConvertFreq_return_wit_1 := 
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) ,
  [| (oldFreq_pre <> 0) |]
  &&  (store_swtmr_sorted_dll sg (updateNodeTime (l2) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
|--
  [| (oldFreq_pre <> 0) |]
  &&  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
  **  (store_swtmr_sorted_dll sg (updateNodeTime (l2) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_pure := 
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) ,
  [| (oldFreq_pre <> 0) |]
  &&  ((( &( "taskHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "oldFreq" ) )) # UInt64  |-> oldFreq_pre)
  **  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
|--
  [| (oldFreq_pre <> 0) |] 
  &&  [| (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) |]
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_aux := 
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) ,
  [| (oldFreq_pre <> 0) |]
  &&  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
|--
  [| (oldFreq_pre <> 0) |] 
  &&  [| (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) |] 
  &&  [| (oldFreq_pre <> 0) |]
  &&  (store_task_sorted_dll sg l1 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  (store_swtmr_sorted_dll sg l2 )
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1 := OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_pure -> OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_aux.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_pure := 
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) ,
  [| (oldFreq_pre <> 0) |]
  &&  ((( &( "swtmrHead" ) )) # Ptr  |-> ( &( "g_swtmrSortLink" ) ))
  **  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  ((( &( "taskHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "oldFreq" ) )) # UInt64  |-> oldFreq_pre)
  **  (store_swtmr_sorted_dll sg l2 )
|--
  [| (oldFreq_pre <> 0) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) |]
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_aux := 
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) ,
  [| (oldFreq_pre <> 0) |]
  &&  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  (store_swtmr_sorted_dll sg l2 )
|--
  [| (oldFreq_pre <> 0) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) |] 
  &&  [| (oldFreq_pre <> 0) |]
  &&  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2 := OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_pure -> OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_aux.

Definition SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec := 
forall (oldFreq_pre: Z) (sortLinkHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) ,
  [| (oldFreq_pre <> 0) |] 
  &&  [| (sortLinkHead_pre = ( &( "g_swtmrSortLink" ) )) |]
  &&  (store_swtmr_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
|--
EX (A: Type) ,
EX (n_2: Z) (storeA: (Z -> (A -> Assertion))) (l_2: (@list (@DL_Node (@sortedLinkNode A)))) ,
  ([| (oldFreq_pre <> 0) |]
  &&  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_2 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_2))
  **
  (((store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (updateNodeTime (l_2) (oldFreq_pre) (n_2)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_2))
  -*
  ((store_swtmr_sorted_dll sg (updateNodeTime (l) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)))
.

Definition SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec := 
forall (oldFreq_pre: Z) (sortLinkHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) ,
  [| (oldFreq_pre <> 0) |] 
  &&  [| (sortLinkHead_pre = ( &( "g_taskSortLink" ) )) |]
  &&  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
|--
EX (A: Type) ,
EX (n_2: Z) (storeA: (Z -> (A -> Assertion))) (l_2: (@list (@DL_Node (@sortedLinkNode A)))) ,
  ([| (oldFreq_pre <> 0) |]
  &&  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_2 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_2))
  **
  (((store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (updateNodeTime (l_2) (oldFreq_pre) (n_2)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_2))
  -*
  ((store_task_sorted_dll sg (updateNodeTime (l) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsSortLinkResponseTimeConvertFreq_return_wit_1 : OsSortLinkResponseTimeConvertFreq_return_wit_1.
Axiom proof_of_OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_pure : OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_pure.
Axiom proof_of_OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1 : OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1.
Axiom proof_of_OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_pure : OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_pure.
Axiom proof_of_OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2 : OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2.
Axiom proof_of_SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec.
Axiom proof_of_SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec.

End VC_Correct.
