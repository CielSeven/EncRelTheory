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

(*----- Function OsSortLinkGetNextExpireTime -----*)

Definition OsSortLinkGetNextExpireTime_safety_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| False |]
.

Definition OsSortLinkGetNextExpireTime_safety_wit_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| False |]
.

Definition OsSortLinkGetNextExpireTime_entail_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (pt: Z) (h: Z) ,
  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  ((( &( "list" ) )) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| ((obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_2_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  EX retval,
  [| (retval <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_2_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  EX retval,
  [| (retval <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_3_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  EX a l1 retval,
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_3_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a_2: (@DL_Node (@sortedLinkNode A))) (l1_2: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a_2) (l1_2))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a_2) (l1_2)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  EX a l1 retval,
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_return_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick_4 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_4)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_4 ts att )
|--
  (EX SysTick,
  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (l <> nil) |] 
  &&  [| ((getFirstNodeResponseTime (l)) > (tick_getcycle_ret (ts))) |] 
  &&  [| (0 = ((getFirstNodeResponseTime (l)) - (tick_getcycle_ret (ts)) )) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att ))
  ||
  (EX SysTick_2,
  [| (SysTick_2 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (l <> nil) |] 
  &&  [| ((getFirstNodeResponseTime (l)) <= (tick_getcycle_ret (ts))) |] 
  &&  [| (0 = 0) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att ))
  ||
  (EX SysTick_3,
  [| (SysTick_3 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (l = nil) |] 
  &&  [| (0 = 0) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_3)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 ts att ))
.

Definition OsSortLinkGetNextExpireTime_return_wit_2_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_5: Z) (retval_4: Z) (x_pstNext: Z) (retval: Z) ,
  [| ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) > retval_4) |] 
  &&  [| (retval = ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) - retval_4 )) |] 
  &&  [| (x_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (SysTick_5 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (retval_4 = (tick_getcycle_ret (ts))) |] 
  &&  [| (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick_4 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_pstNext)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_5)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (EX SysTick,
  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (l <> nil) |] 
  &&  [| ((getFirstNodeResponseTime (l)) > (tick_getcycle_ret (ts))) |] 
  &&  [| (retval = ((getFirstNodeResponseTime (l)) - (tick_getcycle_ret (ts)) )) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att ))
  ||
  (EX SysTick_2,
  [| (SysTick_2 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (l <> nil) |] 
  &&  [| ((getFirstNodeResponseTime (l)) <= (tick_getcycle_ret (ts))) |] 
  &&  [| (retval = 0) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att ))
  ||
  (EX SysTick_3,
  [| (SysTick_3 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (l = nil) |] 
  &&  [| (retval = 0) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_3)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 ts att ))
.

Definition OsSortLinkGetNextExpireTime_return_wit_2_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_5: Z) (retval_4: Z) (x_pstNext: Z) (retval: Z) ,
  [| ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) <= retval_4) |] 
  &&  [| (retval = 0) |] 
  &&  [| (x_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (SysTick_5 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (retval_4 = (tick_getcycle_ret (ts))) |] 
  &&  [| (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick_4 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_pstNext)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_5)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (EX SysTick,
  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (l <> nil) |] 
  &&  [| ((getFirstNodeResponseTime (l)) > (tick_getcycle_ret (ts))) |] 
  &&  [| (retval = ((getFirstNodeResponseTime (l)) - (tick_getcycle_ret (ts)) )) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att ))
  ||
  (EX SysTick_2,
  [| (SysTick_2 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (l <> nil) |] 
  &&  [| ((getFirstNodeResponseTime (l)) <= (tick_getcycle_ret (ts))) |] 
  &&  [| (retval = 0) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att ))
  ||
  (EX SysTick_3,
  [| (SysTick_3 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (l = nil) |] 
  &&  [| (retval = 0) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_3)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 ts att ))
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) ,
  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (pt: Z) (h: Z) ,
  [| ((obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_3 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) ,
  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_4 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_5 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) ,
  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (h: Z) ,
  [| (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "listSorted" ) )) # Ptr  |-> retval_2)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_6_aux := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (h: Z) ,
  [| (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_6 := OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure -> OsSortLinkGetNextExpireTime_partial_solve_wit_6_aux.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_2: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_3: Z) (retval: Z) (h: Z) (SysTick: Z) (retval_2: Z) ,
  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (retval_2 = (tick_getcycle_ret (ts))) |] 
  &&  [| (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick_2 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "listSorted" ) )) # Ptr  |-> retval)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  [| (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |]
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_7_aux := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (h: Z) (SysTick_2: Z) (retval_3: Z) ,
  [| (SysTick_2 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (retval_3 = (tick_getcycle_ret (ts))) |] 
  &&  [| (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (SysTick_2 <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |] 
  &&  [| (retval_3 = (tick_getcycle_ret (ts))) |] 
  &&  [| (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| (SysTick <> 0) |] 
  &&  [| (( &( "g_archTickTimer" ) ) <> 0) |]
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_7 := OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure -> OsSortLinkGetNextExpireTime_partial_solve_wit_7_aux.

Definition OsSortLinkGetNextExpireTime_which_implies_wit_1 := 
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z) ,
  (store_sorted_dll storeA &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") l )
|--
  EX pt h,
  [| (increasingSortedNode l ) |]
  &&  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
.

Definition OsSortLinkGetNextExpireTime_which_implies_wit_2 := 
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) (sortLinkHead: Z) ,
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
|--
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition OsSortLinkGetNextExpireTime_which_implies_wit_3 := 
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  EX h,
  [| (h = (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |]
  &&  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec := 
forall (A: Type) ,
forall (targetSortList_pre: Z) (currTime_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (x: Z) (storeA: (Z -> (A -> Assertion))) ,
  EX x_pstNext,
  [| (x_pstNext = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |] 
  &&  [| (l <> nil) |]
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x l )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_pstNext)
|--
EX (A: Type) ,
EX (storeA_2: (Z -> (A -> Assertion))) (a: A) (t: Z) ,
  ((storesortedLinkNode storeA_2 &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) ))
  **
  (((EX retval_2,
  [| (currTime_pre >= t) |] 
  &&  [| (retval_2 = 0) |]
  &&  (storesortedLinkNode storeA_2 &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) ))
  ||
  (EX retval_2,
  [| (currTime_pre < t) |] 
  &&  [| (retval_2 = (t - currTime_pre )) |]
  &&  (storesortedLinkNode storeA_2 &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )))
  -*
  ((EX x_pstNext_2 retval,
  [| ((getFirstNodeResponseTime (l)) > currTime_pre) |] 
  &&  [| (retval = ((getFirstNodeResponseTime (l)) - currTime_pre )) |] 
  &&  [| (x_pstNext_2 = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |]
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x l )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_pstNext_2))
  ||
  (EX x_pstNext_3 retval,
  [| ((getFirstNodeResponseTime (l)) <= currTime_pre) |] 
  &&  [| (retval = 0) |] 
  &&  [| (x_pstNext_3 = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) |]
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x l )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_pstNext_3))))
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

Axiom proof_of_OsSortLinkGetNextExpireTime_safety_wit_1 : OsSortLinkGetNextExpireTime_safety_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_safety_wit_2 : OsSortLinkGetNextExpireTime_safety_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_1 : OsSortLinkGetNextExpireTime_entail_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_2_1 : OsSortLinkGetNextExpireTime_entail_wit_2_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_2_2 : OsSortLinkGetNextExpireTime_entail_wit_2_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_3_1 : OsSortLinkGetNextExpireTime_entail_wit_3_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_3_2 : OsSortLinkGetNextExpireTime_entail_wit_3_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_return_wit_1 : OsSortLinkGetNextExpireTime_return_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_return_wit_2_1 : OsSortLinkGetNextExpireTime_return_wit_2_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_return_wit_2_2 : OsSortLinkGetNextExpireTime_return_wit_2_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_1 : OsSortLinkGetNextExpireTime_partial_solve_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_2 : OsSortLinkGetNextExpireTime_partial_solve_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_3 : OsSortLinkGetNextExpireTime_partial_solve_wit_3.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_4 : OsSortLinkGetNextExpireTime_partial_solve_wit_4.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_5 : OsSortLinkGetNextExpireTime_partial_solve_wit_5.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure : OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_6 : OsSortLinkGetNextExpireTime_partial_solve_wit_6.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure : OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_7 : OsSortLinkGetNextExpireTime_partial_solve_wit_7.
Axiom proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_1 : OsSortLinkGetNextExpireTime_which_implies_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_2 : OsSortLinkGetNextExpireTime_which_implies_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_3 : OsSortLinkGetNextExpireTime_which_implies_wit_3.
Axiom proof_of_OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec : OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec.
Axiom proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.

End VC_Correct.
