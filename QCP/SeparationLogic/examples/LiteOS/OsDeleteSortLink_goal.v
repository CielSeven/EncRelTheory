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

(*----- Function OsDeleteSortLink -----*)

Definition OsDeleteSortLink_safety_wit_1 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) ,
  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (1 <> (INT_MIN)) |]
.

Definition OsDeleteSortLink_safety_wit_2 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) ,
  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition OsDeleteSortLink_return_wit_1_1 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_5: Z) (v_pstNext: Z) (v_6: Z) ,
  [| (t = (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((v_6)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  ((&((v_5)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v_5 x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_6 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  (EX v v_2,
  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (t > g) |] 
  &&  [| (v_2 = 0) |] 
  &&  [| (v = 0) |]
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o))
  ||
  (EX v_3 v_4,
  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (t <= g) |] 
  &&  [| (v_4 = 0) |] 
  &&  [| (v_3 = 0) |]
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_4)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_3)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o))
  ||
  ([| (t = (unsigned_last_nbits ((-1)) (64))) |]
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o))
.

Definition OsDeleteSortLink_return_wit_1_2 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_pstNext: Z) (v_5: Z) (v_6: Z) ,
  [| (v_6 = 0) |] 
  &&  [| (v_5 = 0) |] 
  &&  [| (t <= g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  (EX v v_2,
  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (t > g) |] 
  &&  [| (v_2 = 0) |] 
  &&  [| (v = 0) |]
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o))
  ||
  (EX v_3 v_4,
  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (t <= g) |] 
  &&  [| (v_4 = 0) |] 
  &&  [| (v_3 = 0) |]
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_4)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_3)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o))
  ||
  ([| (t = (unsigned_last_nbits ((-1)) (64))) |]
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o))
.

Definition OsDeleteSortLink_return_wit_1_3 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_pstNext: Z) (v_5: Z) (v_6: Z) ,
  [| (v_6 = 0) |] 
  &&  [| (v_5 = 0) |] 
  &&  [| (t > g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  (EX v v_2,
  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (t > g) |] 
  &&  [| (v_2 = 0) |] 
  &&  [| (v = 0) |]
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o))
  ||
  (EX v_3 v_4,
  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (t <= g) |] 
  &&  [| (v_4 = 0) |] 
  &&  [| (v_3 = 0) |]
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_4)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_3)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o))
  ||
  ([| (t = (unsigned_last_nbits ((-1)) (64))) |]
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o))
.

Definition OsDeleteSortLink_partial_solve_wit_1 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) ,
  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
  **  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_2 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) ,
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_3 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) ,
  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_4_pure := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) ,
  [| (t > g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |] 
  &&  [| (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |]
.

Definition OsDeleteSortLink_partial_solve_wit_4_aux := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) ,
  [| (t > g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |] 
  &&  [| (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (t > g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_4 := OsDeleteSortLink_partial_solve_wit_4_pure -> OsDeleteSortLink_partial_solve_wit_4_aux.

Definition OsDeleteSortLink_partial_solve_wit_5_pure := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) ,
  [| (t <= g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |] 
  &&  [| (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |]
.

Definition OsDeleteSortLink_partial_solve_wit_5_aux := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) ,
  [| (t <= g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |] 
  &&  [| (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (t <= g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_5 := OsDeleteSortLink_partial_solve_wit_5_pure -> OsDeleteSortLink_partial_solve_wit_5_aux.

Definition OsDeleteSortLink_partial_solve_wit_6 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_pstNext: Z) ,
  [| (t <= g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (t <= g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_7 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_pstNext: Z) ,
  [| (t > g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  [| (t > g) |] 
  &&  [| (t <> (unsigned_last_nbits ((-1)) (64))) |] 
  &&  [| (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) |]
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_which_implies_wit_1 := 
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )
|--
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) ) |]
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
.

Definition OsDeleteSortLink_which_implies_wit_2 := 
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) ,
  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
|--
  EX v_pstPrev v v_pstNext v_2,
  [| (v_pstNext = &((node)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node)  # "SortLinkList" ->ₛ "sortLinkNode")) |]
  &&  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  (storesortedLinkNode storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition OsDeleteSortLink_which_implies_wit_3 := 
forall (A: Type) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (node: Z) ,
  (storesortedLinkNode storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Definition OsDeleteSortLink_which_implies_wit_4 := 
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) (v_2: Z) (v_pstNext: Z) (v: Z) (v_pstPrev: Z) ,
  [| (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) ) |] 
  &&  [| (v_pstNext = &((node)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (v_pstPrev = &((node)  # "SortLinkList" ->ₛ "sortLinkNode")) |]
  &&  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  (storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsDeleteSortLink_safety_wit_1 : OsDeleteSortLink_safety_wit_1.
Axiom proof_of_OsDeleteSortLink_safety_wit_2 : OsDeleteSortLink_safety_wit_2.
Axiom proof_of_OsDeleteSortLink_return_wit_1_1 : OsDeleteSortLink_return_wit_1_1.
Axiom proof_of_OsDeleteSortLink_return_wit_1_2 : OsDeleteSortLink_return_wit_1_2.
Axiom proof_of_OsDeleteSortLink_return_wit_1_3 : OsDeleteSortLink_return_wit_1_3.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_1 : OsDeleteSortLink_partial_solve_wit_1.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_2 : OsDeleteSortLink_partial_solve_wit_2.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_3 : OsDeleteSortLink_partial_solve_wit_3.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_4_pure : OsDeleteSortLink_partial_solve_wit_4_pure.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_4 : OsDeleteSortLink_partial_solve_wit_4.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_5_pure : OsDeleteSortLink_partial_solve_wit_5_pure.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_5 : OsDeleteSortLink_partial_solve_wit_5.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_6 : OsDeleteSortLink_partial_solve_wit_6.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_7 : OsDeleteSortLink_partial_solve_wit_7.
Axiom proof_of_OsDeleteSortLink_which_implies_wit_1 : OsDeleteSortLink_which_implies_wit_1.
Axiom proof_of_OsDeleteSortLink_which_implies_wit_2 : OsDeleteSortLink_which_implies_wit_2.
Axiom proof_of_OsDeleteSortLink_which_implies_wit_3 : OsDeleteSortLink_which_implies_wit_3.
Axiom proof_of_OsDeleteSortLink_which_implies_wit_4 : OsDeleteSortLink_which_implies_wit_4.

End VC_Correct.
