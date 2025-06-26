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

(*----- Function GetSortLinkNextExpireTime -----*)

Definition GetSortLinkNextExpireTime_safety_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| False |]
.

Definition GetSortLinkNextExpireTime_safety_wit_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| False |]
.

Definition GetSortLinkNextExpireTime_entail_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) ,
  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((( &( "list" ) )) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| ((obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_2_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  EX retval,
  [| (retval <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_2_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  EX retval,
  [| (retval <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_3_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  EX a l1 retval,
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_3_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a_2: (@DL_Node (@sortedLinkNode A))) (l1_2: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a_2) (l1_2))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a_2) (l1_2)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  EX a l1 retval,
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_return_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| ((unsigned_last_nbits ((((2 ^ 64 ) - 1 ) - tickPrecision_pre )) (64)) = (getFirstNodeExpireTime (l) (startTime_pre) (tickPrecision_pre))) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_return_wit_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (pl: Z) ,
  [| ((responseTime ((data (a)))) <= (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (storeA &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") (sl_data ((data (a)))) )
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| ((unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64)) = (getFirstNodeExpireTime (l) (startTime_pre) (tickPrecision_pre))) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_return_wit_3 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (pl: Z) ,
  [| ((responseTime ((data (a)))) > (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (storeA &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") (sl_data ((data (a)))) )
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| ((responseTime ((data (a)))) = (getFirstNodeExpireTime (l) (startTime_pre) (tickPrecision_pre))) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) ,
  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) ,
  [| ((obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_3 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) ,
  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_4 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_5_pure := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) ,
  [| (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((( &( "listSorted" ) )) # Ptr  |-> retval)
  **  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a))) |]
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_5_aux := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) ,
  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons ((Build_DL_Node ((mksortedLinkNode ((sl_data ((data (a))))) ((responseTime ((data (a))))))) (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode")))) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_5 := GetSortLinkNextExpireTime_partial_solve_wit_5_pure -> GetSortLinkNextExpireTime_partial_solve_wit_5_aux.

Definition GetSortLinkNextExpireTime_partial_solve_wit_6 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (pl: Z) ,
  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  (storesortedLinkNode storeA &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode ((sl_data ((data (a))))) ((responseTime ((data (a)))))) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
|--
  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (storesortedLinkNode storeA &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode ((sl_data ((data (a))))) ((responseTime ((data (a)))))) )
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2 ^ 64 ) - 1 ))
.

Definition GetSortLinkNextExpireTime_which_implies_wit_1 := 
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortHead: Z) ,
  (store_sorted_dll storeA &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") l )
|--
  EX pt h,
  [| (increasingSortedNode l ) |]
  &&  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
.

Definition GetSortLinkNextExpireTime_which_implies_wit_2 := 
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) (sortHead: Z) ,
  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
|--
  (store_dll (storesortedLinkNode (storeA)) &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition GetSortLinkNextExpireTime_which_implies_wit_3 := 
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (t: Z) (al: A) (listSorted: Z) (sortHead: Z) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") (cons ((Build_DL_Node ((mksortedLinkNode (al) (t))) (&((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode")))) (l1)) )
|--
  EX pt pl,
  ((&((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  (storesortedLinkNode storeA &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (al) (t)) )
.

Definition GetSortLinkNextExpireTime_which_implies_wit_4 := 
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (al: A) (listSorted: Z) ,
  (storesortedLinkNode storeA &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (al) (t)) )
|--
  (storeA &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode") al )
  **  ((&((listSorted)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Definition LOS_ListEmpty_derive_getfirstSpec_by_highSpec := 
forall (A: Type) ,
forall (node_pre: Z) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) ,
  (store_dll storeA node_pre l )
|--
EX (A: Type) ,
EX (storeA_2: (Z -> (A -> Assertion))) (l_2: (@list (@DL_Node A))) ,
  ((store_dll storeA_2 node_pre l_2 ))
  **
  (((EX retval_2,
  [| (l_2 = nil) |] 
  &&  [| (retval_2 = 1) |]
  &&  (store_dll storeA_2 node_pre l_2 ))
  ||
  (EX retval_2,
  [| (l_2 <> nil) |] 
  &&  [| (retval_2 = 0) |]
  &&  (store_dll storeA_2 node_pre l_2 )))
  -*
  ((EX a l1 retval,
  [| (l <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| (l = (cons (a) (l1))) |]
  &&  (store_dll storeA node_pre (cons (a) (l1)) ))
  ||
  (EX retval,
  [| (l = nil) |] 
  &&  [| (retval = 1) |]
  &&  (store_dll storeA node_pre l ))))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_GetSortLinkNextExpireTime_safety_wit_1 : GetSortLinkNextExpireTime_safety_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_safety_wit_2 : GetSortLinkNextExpireTime_safety_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_1 : GetSortLinkNextExpireTime_entail_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_2_1 : GetSortLinkNextExpireTime_entail_wit_2_1.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_2_2 : GetSortLinkNextExpireTime_entail_wit_2_2.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_3_1 : GetSortLinkNextExpireTime_entail_wit_3_1.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_3_2 : GetSortLinkNextExpireTime_entail_wit_3_2.
Axiom proof_of_GetSortLinkNextExpireTime_return_wit_1 : GetSortLinkNextExpireTime_return_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_return_wit_2 : GetSortLinkNextExpireTime_return_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_return_wit_3 : GetSortLinkNextExpireTime_return_wit_3.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_1 : GetSortLinkNextExpireTime_partial_solve_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_2 : GetSortLinkNextExpireTime_partial_solve_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_3 : GetSortLinkNextExpireTime_partial_solve_wit_3.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_4 : GetSortLinkNextExpireTime_partial_solve_wit_4.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_5_pure : GetSortLinkNextExpireTime_partial_solve_wit_5_pure.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_5 : GetSortLinkNextExpireTime_partial_solve_wit_5.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_6 : GetSortLinkNextExpireTime_partial_solve_wit_6.
Axiom proof_of_GetSortLinkNextExpireTime_which_implies_wit_1 : GetSortLinkNextExpireTime_which_implies_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_which_implies_wit_2 : GetSortLinkNextExpireTime_which_implies_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_which_implies_wit_3 : GetSortLinkNextExpireTime_which_implies_wit_3.
Axiom proof_of_GetSortLinkNextExpireTime_which_implies_wit_4 : GetSortLinkNextExpireTime_which_implies_wit_4.
Axiom proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.

End VC_Correct.
