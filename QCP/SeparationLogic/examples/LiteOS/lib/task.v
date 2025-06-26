Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Require Import SL.ConAssertion SL.CriticalSTS SL.NestedCriticalSTS.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Local Open Scope stmonad.
Require Import LOS_Verify.lib.Los_Rules_lib.
Import TaskStateDef.
Local Open Scope sac.
Require Import LOS_Verify.lib.dll.


Definition task_InsideCritical (p : StableGlobVars ) (l : Los_Verify_State ) (st : TcbGlobalState) :=
  InsideCritical p (replace_tskS st l).

Definition task_OutsideCritical (p : StableGlobVars ) (l : Los_Verify_State ) (st : TcbGlobalState) :=
  OutsideCritical p (replace_tskS st l).

Definition task_RTrans_C p1 l1 st1 p2 l2 st2: Prop :=
  RTrans_C  p1 (replace_tskS st1 l1) p2 (replace_tskS st2 l2).

Definition task_GTrans_C p1 l1 st1 p2 l2 st2 : Prop :=
  GTrans_C  p1 (replace_tskS st1 l1) p2 (replace_tskS st2 l2).

Definition task_RTrans_Abs l1 st1 l2 st2 : Prop :=
  RTrans_Abs (replace_tskS st1 l1) (replace_tskS st2 l2).

Definition task_GTrans_Abs l1 st1 l2 st2 : Prop :=
  GTrans_Abs (replace_tskS st1 l1) (replace_tskS st2 l2).


Definition g_taskMaxNum := 6.   (* including  idle, swtmr task *)

Definition OS_TASK_STATUS_UNUSED := 1.         Definition STATUS_UNUSED := 0. 
Definition OS_TASK_STATUS_SUSPEND := 2.        Definition STATUS_SUSPEND := 1.
Definition OS_TASK_STATUS_READY := 4.          Definition STATUS_READY := 2.
Definition OS_TASK_STATUS_PEND := 8.           Definition STATUS_PEND := 3.
Definition OS_TASK_STATUS_RUNNING := 16.       Definition STATUS_RUNNING := 4.
Definition OS_TASK_STATUS_DELAY := 32.         Definition STATUS_DELAY := 5.
Definition OS_TASK_STATUS_TIMEOUT := 64.       Definition STATUS_TIMEOUT := 6.
Definition OS_TASK_STATUS_PEND_TIME := 128.    Definition STATUS_PEND_TIME := 7.
Definition OS_TASK_STATUS_EXIT := 256.         Definition STATUS_EXIT := 8.

Definition OS_TASK_FLAG_USER_TASK := 512.      Definition FLAG_USER_TASK := 9.
Definition OS_TASK_FLAG_STACK_FREE := 2048.    Definition FLAG_STACK_FREE := 11.
Definition OS_TASK_FLAG_SYSTEM_TASK := 4096.   Definition FLAG_SYSTEM_TASK := 12.
Definition OS_TASK_FLAG_SIGNAL := 8192.        Definition FLAG_SIGNAL := 13.
Definition OS_TASK_FLAG_FREEZE := 16384.       Definition FLAG_FREEZE := 14.
Definition OS_TASK_FLAG_JOINABLE := 32768.     Definition FLAG_JOINABLE := 15.



Definition ghostTaskId := g_taskMaxNum.  (* system will malloc (g_taskMaxNum + 1) tcb space, the last tcb, termed ghost task, is used when there is actually no real running task *)

(** show how low level abstract state stores in memory  **)

(* demonstrate where pendList is stored *)
Definition set_pendList (sg : StableGlobVars)(ctrl_start: addr) (status : Z) (tID : TaskID): Assertion :=
    if Z.testbit status STATUS_READY then 
        (if Z.eq_dec tID sg.(idleTaskID) then occupy_dll_node &(ctrl_start # "LosTaskCB" ->ₛ "pendList") else emp)        (* status 为 ready 且不是 idle, 权限在g_priQueueList里  *)
    else if Z.testbit status STATUS_PEND then emp   (* status 为 pend, 权限在对应哨兵节点里  *)
    else if Z.testbit status STATUS_UNUSED then emp   (* status 为 unused, 权限在对应哨兵节点里  *)
    else occupy_dll_node &(ctrl_start # "LosTaskCB" ->ₛ "pendList").


(* demonstrate where sortList is stored *)

Definition occupy_sdll_node :  addr -> Assertion. 
Admitted.

Definition store_event: addr -> Z * list TaskID -> Assertion.
Admitted.

Axiom store_event_def_implies_undef: forall p, store_event p (0, []) |-- store_event p (-1, []).

Definition set_sortLisk (ctrl_start: addr) (status : Z): Assertion :=
    if Z.testbit status STATUS_DELAY then emp        (* status 为 delay, 权限在 g_taskSortLink 里  *)
    else if Z.testbit status STATUS_PEND_TIME then emp   (* status 为 pendtime, 权限在 g_taskSortLink 里  *)
    else occupy_sdll_node &(ctrl_start # "LosTaskCB" ->ₛ "sortList").

(* tJoinList is stored in a dll with ctrl_start->joinList as the head node *)  
Definition set_joinList (sg : StableGlobVars)(ctrl_start: addr) (tJoinList : list TaskID) :=
  occupy_dll_node (&(ctrl_start # "LosTaskCB" ->ₛ "joinList")).
    (* match tJoinList with
    | nil => occupy_dll_node (&(ctrl_start # "LosTaskCB" ->ₛ "joinList"))
    | _ =>store_pend_list_dll sg (&(ctrl_start # "LosTaskCB" ->ₛ "joinList")) tJoinList
    end. *)


(* complete tasks in usedTask, i.e. a normal complete task  satisfying usedTask(task) != None *)
Definition used_complete_task (sg: StableGlobVars) (ctrl_start: addr) (tID : TaskID) (tskabs: TaskAbstractState): Assertion :=
    &(ctrl_start # "LosTaskCB" ->ₛ "taskID") # UInt |-> tID **
    &(ctrl_start # "LosTaskCB" ->ₛ "taskStatus") # UShort |-> tskabs.(status) ** 
    &(ctrl_start # "LosTaskCB" ->ₛ "priority") # UShort |-> tskabs.(tPrio) **
    &(ctrl_start # "LosTaskCB" ->ₛ "stackPointer") # Ptr |-> tskabs.(tStackPointer) **
    &(ctrl_start # "LosTaskCB" ->ₛ "timeSlice") # Int |-> tskabs.(tTimeSlice) **
    &(ctrl_start # "LosTaskCB" ->ₛ "waitTimes") # UInt |-> tskabs.(tWaitTimes) **
    &(ctrl_start # "LosTaskCB" ->ₛ "startTime") # UInt64 |-> tskabs.(tStartTime) **
    &(ctrl_start # "LosTaskCB" ->ₛ "stackSize") # UInt |-> tskabs.(tStackSize) **
    &(ctrl_start # "LosTaskCB" ->ₛ "topOfStack") # UInt |-> tskabs.(tTopOfStack) **
    &(ctrl_start # "LosTaskCB" ->ₛ "taskEntry") # Ptr |-> tskabs.(tTaskEntry) **
    &(ctrl_start # "LosTaskCB" ->ₛ "taskSem") # Ptr |-> tskabs.(tTaskSem) **
    &(ctrl_start # "LosTaskCB" ->ₛ "taskMux") # Ptr |-> tskabs.(tTaskMux) **
    &(ctrl_start # "LosTaskCB" ->ₛ "arg") # UInt |-> tskabs.(tArg) **
    &(ctrl_start # "LosTaskCB" ->ₛ "taskName") # Ptr |-> tskabs.(tTaskName) **
    &(ctrl_start # "LosTaskCB" ->ₛ "joinRetval") # UInt |-> tskabs.(tJoinRetval) **
    &(ctrl_start # "LosTaskCB" ->ₛ "msg") # Ptr |-> tskabs.(tMsg) **
    &(ctrl_start # "LosTaskCB" ->ₛ "eventMask") # UInt |-> tskabs.(tEventMask) **
    &(ctrl_start # "LosTaskCB" ->ₛ "eventMode") # UInt |-> tskabs.(tEventMode) **
    store_event ctrl_start tskabs.(tEvent) **
    set_sortLisk ctrl_start tskabs.(status) **   (* 设置sortList 在内存中的存储 *)
    set_pendList sg ctrl_start tskabs.(status) tID **   (* 设置pendList 在内存中的存储 *)
    set_joinList sg ctrl_start tskabs.(tJoinList).     (* 设置joinList 在内存中的存储 *)


(* how usedTask map stores *)
Definition store_used_task_map (sg: StableGlobVars) 
                               (m: TaskID -> option TaskAbstractState): Assertion :=
  store_map 
    (fun taskID t =>
      used_complete_task sg (sg.(g_taskCBArray) + sizeof("LosTaskCB") * taskID) taskID t)
    m.

(* auxillary predicate stating how usedTask map stores after extracting a tsk *)
Definition store_used_task_map_exclude
            (sg: StableGlobVars)
            (m: TaskID -> option TaskAbstractState)
            (missingID: TaskID): Assertion :=
  store_map_missing_i
    (fun taskID t => 
      used_complete_task sg (sg.(g_taskCBArray) + sizeof("LosTaskCB") * taskID) taskID t)
    m missingID.

(* tasks in g_losFreeTask, where pendlist is pended on g_losFreeTask*)
Definition unused_task (ctrl_start: addr) (tID : TaskID) : Assertion :=
  &(ctrl_start # "LosTaskCB" ->ₛ "taskID") # UInt |-> tID **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskStatus") # UShort |-> 1 ** 
  &(ctrl_start # "LosTaskCB" ->ₛ "priority") # UShort |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "stackPointer") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "timeSlice") # Int |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "waitTimes") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "startTime") # UInt64 |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "stackSize") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "topOfStack") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskEntry") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskSem") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskMux") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskName") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "arg") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "joinRetval") # UInt |->_ ** 
  &(ctrl_start # "LosTaskCB" ->ₛ "msg") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "eventMask") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "eventMode") # UInt |->_ **
  (store_event ctrl_start (-1, nil)) **
  occupy_sdll_node &(ctrl_start # "LosTaskCB" ->ₛ "sortList") **
  occupy_dll_node (&(ctrl_start # "LosTaskCB" ->ₛ "joinList")).

(* how g_losFreeTask stores *)
Definition store_free_task_list (sg: StableGlobVars) (l: list TaskID): Assertion :=
    EX l0: list (DL_Node TaskID),
      [| map DLL.data l0 = l |] &&
      store_dll
        (fun p taskID =>
           EX ctrl_start: addr,
           [| ctrl_start = sg.(g_taskCBArray) + sizeof("LosTaskCB") * taskID |] &&
           [| p = &(ctrl_start # "LosTaskCB" ->ₛ "pendList") |] &&
             unused_task ctrl_start taskID)
        (&("g_losFreeTask")) l0.


(* tasks in g_taskRecycleList *)
Definition recycle_task (ctrl_start: addr) ( recycle_tskabs : RecycleTaskAbstractState) : Assertion :=
  &(ctrl_start # "LosTaskCB" ->ₛ "taskID") # UInt |-> recycle_tskabs.(recycle_tID) **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskStatus") # UShort |-> recycle_tskabs.(recycle_status) ** 
  &(ctrl_start # "LosTaskCB" ->ₛ "priority") # UShort |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "stackPointer") # Ptr |-> recycle_tskabs.(recycle_tStackPointer) **
  &(ctrl_start # "LosTaskCB" ->ₛ "timeSlice") # Int |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "waitTimes") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "startTime") # UInt64 |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "stackSize") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "topOfStack") # UInt |->  recycle_tskabs.(recycle_tTopOfStack) **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskEntry") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskSem") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskMux") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskName") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "arg") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "joinRetval") # UInt |->_ ** 
  &(ctrl_start # "LosTaskCB" ->ₛ "msg") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "eventMask") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "eventMode") # UInt |->_ **
  (store_event ctrl_start (-1,nil)) **
  occupy_sdll_node &(ctrl_start # "LosTaskCB" ->ₛ "sortList") **
  occupy_dll_node (&(ctrl_start # "LosTaskCB" ->ₛ "joinList")).


(* how g_taskRecycleList stores *)
Definition store_recycle_task_list (sg: StableGlobVars) (l : list ( RecycleTaskAbstractState) ): Assertion :=
    EX l0: list (DL_Node (RecycleTaskAbstractState)),
      [| map DLL.data l0 = l |] &&
      store_dll 
      (fun p recycle_tskabs =>
           EX ctrl_start: addr,
           [| ctrl_start = sg.(g_taskCBArray) + sizeof("LosTaskCB") * recycle_tskabs.(recycle_tID) |] &&
           [| p = &(ctrl_start # "LosTaskCB" ->ₛ "pendList") |] &&
           recycle_task ctrl_start recycle_tskabs
           )
        (&("g_taskRecycleList")) l0.


(* how ghost task stores *)  
Definition store_ghost_task (sg: StableGlobVars) (ghostTaskInfo : TaskID * Z * Z * addr): Assertion :=
  let ctrl_start := sg.(g_taskCBArray) + ghostTaskId * sizeof("LosTaskCB") in
  match ghostTaskInfo with
  | (tID , status, tTopOfStack, tTaskName) =>
  &(ctrl_start # "LosTaskCB" ->ₛ "taskID") # UInt |-> tID **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskStatus") # UShort |-> status ** 
  &(ctrl_start # "LosTaskCB" ->ₛ "priority") # UShort |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "stackPointer") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "timeSlice") # Int |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "waitTimes") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "startTime") # UInt64 |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "stackSize") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "topOfStack") # UInt |-> tTopOfStack **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskEntry") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskSem") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskMux") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskName") # Ptr |-> tTaskName **
  &(ctrl_start # "LosTaskCB" ->ₛ "arg") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "joinRetval") # UInt |->_ ** 
  &(ctrl_start # "LosTaskCB" ->ₛ "msg") # Ptr |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "eventMask") # UInt |->_ **
  &(ctrl_start # "LosTaskCB" ->ₛ "eventMode") # UInt |->_ **
  (store_event ctrl_start (-1,nil)) **
  occupy_sdll_node &(ctrl_start # "LosTaskCB" ->ₛ "sortList") **
  occupy_dll_node &(ctrl_start # "LosTaskCB" ->ₛ "pendList") **
  occupy_dll_node (&(ctrl_start # "LosTaskCB" ->ₛ "joinList"))
  end.


(* how runTask and newTask stores *)
Definition store_runTask (sg: StableGlobVars) (runTask : Z ) :=
  [| 0 <= runTask < g_taskMaxNum |] &&
  &( &("g_losTask") ->ₛ "runTask") # Ptr |->  (sg.(g_taskCBArray) + runTask * sizeof("LosTaskCB")) .

Definition store_newTask (sg: StableGlobVars) (newTask : Z ) :=
  [| 0 <= newTask < g_taskMaxNum |] &&
  &( &("g_losTask") ->ₛ "newTask") # Ptr |->  (sg.(g_taskCBArray) + newTask * sizeof("LosTaskCB")) .

(* how g_idleTaskID and  g_swtmrTaskID stores *)
Definition store_idleTaskID (idleTaskID : Z) :=
  [| 0 <= idleTaskID < g_taskMaxNum |] &&
   &("g_idleTaskID") # UInt |-> idleTaskID.

Definition store_swtmrTaskID (swtmrTaskID : Z) :=
  [| 0 <= swtmrTaskID < g_taskMaxNum |] &&
   &("g_swtmrTaskID") # UInt |-> swtmrTaskID.
  
(* how g_losTaskLock stores*)
Definition store_losTaskLock (losTaskLock : Z) :=
   &("g_losTaskLock") # UShort |-> losTaskLock.


(* 临界区内的临时中间谓词,拥有pendlist, sortedlist 等权限  *)
Definition store_task_with_all_permission (ctrl_start: addr) (tID : TaskID) ( tskabs: TaskAbstractState) : Assertion :=
  &(ctrl_start # "LosTaskCB" ->ₛ "taskID") # UInt |-> tID **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskStatus") # UShort |-> tskabs.(status) ** 
  &(ctrl_start # "LosTaskCB" ->ₛ "priority") # UShort |-> tskabs.(tPrio) **
  &(ctrl_start # "LosTaskCB" ->ₛ "stackPointer") # Ptr |-> tskabs.(tStackPointer) **
  &(ctrl_start # "LosTaskCB" ->ₛ "timeSlice") # Int |-> tskabs.(tTimeSlice) **
  &(ctrl_start # "LosTaskCB" ->ₛ "waitTimes") # UInt |-> tskabs.(tWaitTimes) **
  &(ctrl_start # "LosTaskCB" ->ₛ "startTime") # UInt64 |-> tskabs.(tStartTime) **
  &(ctrl_start # "LosTaskCB" ->ₛ "stackSize") # UInt |-> tskabs.(tStackSize) **
  &(ctrl_start # "LosTaskCB" ->ₛ "topOfStack") # UInt |-> tskabs.(tTopOfStack) **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskEntry") # Ptr |-> tskabs.(tTaskEntry) **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskSem") # Ptr |-> tskabs.(tTaskSem) **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskMux") # Ptr |-> tskabs.(tTaskMux) **
  &(ctrl_start # "LosTaskCB" ->ₛ "arg") # UInt |-> tskabs.(tArg) **
  &(ctrl_start # "LosTaskCB" ->ₛ "taskName") # Ptr |-> tskabs.(tTaskName) **
  &(ctrl_start # "LosTaskCB" ->ₛ "joinRetval") # UInt |-> tskabs.(tJoinRetval) **
  &(ctrl_start # "LosTaskCB" ->ₛ "msg") # Ptr |-> tskabs.(tMsg) **
  &(ctrl_start # "LosTaskCB" ->ₛ "eventMask") # UInt |-> tskabs.(tEventMask) **
  &(ctrl_start # "LosTaskCB" ->ₛ "eventMode") # UInt |-> tskabs.(tEventMode) **
  (store_event ctrl_start tskabs.(tEvent)) **
  occupy_sdll_node &(ctrl_start # "LosTaskCB" ->ₛ "sortList") **
  occupy_dll_node &(ctrl_start # "LosTaskCB" ->ₛ "pendList") **
  occupy_dll_node (&(ctrl_start # "LosTaskCB" ->ₛ "joinList")).

(* every task has a stack, how stack stores *)

Definition store_stack_memory (tTopOfStack: Z) :  Assertion. (* store continuous memory space *)
Admitted.

Definition store_one_stack (tTopOfStack: Z) :=
  store_stack_memory tTopOfStack.

Definition store_used_task_stack (usedTask : TaskID -> option TaskAbstractState) : Assertion :=
  store_map 
  (fun taskID t => store_stack_memory t.(tTopOfStack))
  usedTask.

Fixpoint store_list {A: Type} (storeA: A -> Assertion )(l: list A) :=
  match l with 
  | nil => emp 
  | a :: l' => storeA a ** store_list storeA l'
  end.

Definition store_recycle_task_stack (recycleList: list (RecycleTaskAbstractState)) : Assertion :=
  store_list 
    (fun recycle_tskabs =>  store_stack_memory recycle_tskabs.(recycle_tTopOfStack)) 
    recycleList.
  

Definition store_all_stack (st : TcbGlobalState) : Assertion :=
  store_used_task_stack st.(usedTask) **
  store_recycle_task_stack st.(recycleList).


(* how low level abstract state (TcbGlobalState) stores  *)   
Definition store_TcbGlobalState (sg: StableGlobVars) (st : TcbGlobalState) :=
  store_used_task_map sg st.(usedTask) **
  store_free_task_list sg st.(freeTask) **
  store_recycle_task_list sg st.(recycleList) **
  store_all_stack st **
  store_ghost_task sg st.(ghostTaskInfo) **
  store_runTask sg st.(runTask) ** store_newTask sg st.(newTask) **
  store_idleTaskID sg.(idleTaskID) ** store_swtmrTaskID sg.(swtmrTaskID) **
  store_losTaskLock st.(losTaskLock).

(* --------------------------prop on TcbGlobalState-------------------------*)

Definition vaild_cond1 (task_global: TcbGlobalState) : Prop :=
  forall taskID, 0 <= taskID < g_taskMaxNum -> (
  (
    (exists b, task_global.(usedTask) taskID = Some b) /\
    ~ (In taskID task_global.(freeTask) ) /\
    ~ (exists b, In b task_global.(recycleList) /\ b.(recycle_tID) = taskID)
  ) \/
  (
    ~ (exists b, task_global.(usedTask) taskID = Some b) /\
    (In taskID task_global.(freeTask) ) /\
    ~ (exists b, In b task_global.(recycleList) /\ b.(recycle_tID) = taskID)
  ) \/
  (
    ~ (exists b, task_global.(usedTask) taskID = Some b) /\
    ~ (In taskID task_global.(freeTask) ) /\
    (exists b, In b task_global.(recycleList) /\ b.(recycle_tID) = taskID)
  )  ).

Definition vaild_cond2 (task_global: TcbGlobalState) : Prop :=
  (
    NoDup task_global.(freeTask)
  ) /\ 
  (
    NoDup ( map (fun (a: RecycleTaskAbstractState) => a.(recycle_tID)) task_global.(recycleList))
  )
  .

Definition vaild_cond3 (st: TcbGlobalState) : Prop :=
  Forall (fun taskID => 0 <= taskID < g_taskMaxNum) st.(freeTask) /\ 
  Forall (fun recycle_tskabs => 0 <= recycle_tskabs.(recycle_tID) < g_taskMaxNum ) 
         st.(recycleList) /\ 
  forall taskID, (
                 match st.(usedTask) taskID with
                 | Some b => 0 <= taskID < g_taskMaxNum /\ 0 <= b.(tPrio) < 32
                 | None => True
                 end ).


Definition vaild_cond4  (task_global: TcbGlobalState) :Prop :=
  Forall (fun recycle_tskabs => Z.testbit recycle_tskabs.(recycle_status) STATUS_UNUSED = true /\ recycle_tskabs.(recycle_status) >=0 ) 
  task_global.(recycleList).


Definition vaild_usedTask_status (status : Z) : Prop :=
    (Z.testbit status STATUS_PEND_TIME = true -> Z.testbit status STATUS_PEND = true )  (* pend_time -> pend *)
    /\ 
    (Z.testbit status STATUS_DELAY = true -> Z.testbit status STATUS_PEND = false )     (* pend 和 delay 互斥 *)
    /\ 
    (Z.testbit status STATUS_PEND = true -> Z.testbit status STATUS_DELAY = false )     (* pend 和 delay 互斥 *)
    /\ 
    (Z.testbit status STATUS_UNUSED = false) 
    /\
    (Z.testbit status STATUS_RUNNING = true -> (Z.testbit status STATUS_READY = false /\ Z.testbit status STATUS_PEND = false /\ Z.testbit status STATUS_SUSPEND = false /\ Z.testbit status STATUS_DELAY = false)) 
    /\
    (Z.testbit status STATUS_READY = true -> (Z.testbit status STATUS_RUNNING = false /\ Z.testbit status STATUS_PEND = false /\ Z.testbit status STATUS_SUSPEND = false /\ Z.testbit status STATUS_DELAY = false)) 
    /\
    (Z.testbit status STATUS_RUNNING = true \/ Z.testbit status STATUS_READY = true \/ Z.testbit status STATUS_PEND = true \/ Z.testbit status STATUS_DELAY = true \/ Z.testbit status STATUS_SUSPEND = true).
    

Definition vaild_cond5 (st: TcbGlobalState) :Prop :=
  forall taskID,
  match st.(usedTask) taskID with
  | Some tskabs => tskabs.(status) >= 0 /\ vaild_usedTask_status tskabs.(status) /\ tskabs.(tTaskName) > 0
  | None => True
  end.

Definition vaild_cond6 (st : TcbGlobalState) : Prop :=
  exists tskabs, st.(usedTask) st.(runTask) = Some tskabs /\
                  Z.testbit tskabs.(status) STATUS_RUNNING = true.

Definition vaild_cond7 (sg: StableGlobVars) (st : TcbGlobalState) : Prop :=
  exists tskabs, st.(usedTask) sg.(idleTaskID) = Some tskabs /\ 
                 Z.testbit tskabs.(status) FLAG_SYSTEM_TASK = true /\ 
                 (Z.testbit tskabs.(status) STATUS_READY = true \/ Z.testbit tskabs.(status) STATUS_RUNNING = true).

Definition task_vaild_cond (sg: StableGlobVars) (st: TcbGlobalState) : Assertion :=
  [| vaild_cond1 st |] &&
  [| vaild_cond2 st |] &&
  [| vaild_cond3 st |] &&
  [| vaild_cond4 st |] &&
  [| vaild_cond5 st |] &&
  [| vaild_cond6 st |] &&
  [| vaild_cond7 sg st |].

Record task_vaild_cond_prop (sg: StableGlobVars) (st: TcbGlobalState) : Prop :=
  {
    task_cond1 : vaild_cond1 st;
    task_cond2 : vaild_cond2 st;
    task_cond3 : vaild_cond3 st;
    task_cond4 : vaild_cond4 st;
    task_cond5 : vaild_cond5 st;
    task_cond6 : vaild_cond6 st;
    task_cond7 : vaild_cond7 sg st;
  }.

Definition task_inv (sg: StableGlobVars) (st: TcbGlobalState): Assertion :=
  [| task_vaild_cond_prop sg st |] &&
  store_used_task_map sg st.(usedTask) **
  store_free_task_list sg st.(freeTask) **
  store_recycle_task_list sg st.(recycleList) **
  store_all_stack st **
  store_ghost_task sg st.(ghostTaskInfo) **
  store_runTask sg st.(runTask) ** store_newTask sg st.(newTask) **
  store_idleTaskID sg.(idleTaskID) ** store_swtmrTaskID sg.(swtmrTaskID) **
  store_losTaskLock st.(losTaskLock).


Definition task_inv_missing_usedtask (taskID : TaskID)  (sg: StableGlobVars) (st: TcbGlobalState): Assertion :=
  [| exists b, st.(usedTask) taskID = Some b |] &&
  [| task_vaild_cond_prop sg st |] &&
  store_used_task_map_exclude sg st.(usedTask) taskID **
  store_free_task_list sg st.(freeTask) **
  store_recycle_task_list sg st.(recycleList) **
  store_all_stack st **
  store_ghost_task sg st.(ghostTaskInfo) **
  store_runTask sg st.(runTask) ** store_newTask sg st.(newTask) **
  store_idleTaskID sg.(idleTaskID) ** store_swtmrTaskID sg.(swtmrTaskID) **
  store_losTaskLock st.(losTaskLock).

From SimpleC.ASRTFUN Require Import list_lemma.

Definition store_free_task_list_exclude (sg: StableGlobVars) (l : list TaskID) (tID : TaskID) : Assertion :=
  EX l0: list (DL_Node TaskID),
  [| map DLL.data l0 = l |] &&
  store_dll
    (fun p taskID =>
       EX ctrl_start: addr,
       [| ctrl_start = sg.(g_taskCBArray) + sizeof("LosTaskCB") * taskID |] &&
       [| p = &(ctrl_start # "LosTaskCB" ->ₛ "pendList") |] &&
       (if Z.eq_dec taskID tID then emp else unused_task ctrl_start taskID)
    )
    (&("g_losFreeTask")) l0. 
  
Definition task_inv_missing_unusedtask (taskID : TaskID)  (sg: StableGlobVars) (st: TcbGlobalState): Assertion :=
  [| In taskID st.(freeTask) |] &&
  [| task_vaild_cond_prop sg st |] &&
  store_used_task_map sg st.(usedTask) **
  store_free_task_list_exclude sg st.(freeTask) taskID  **
  store_recycle_task_list sg st.(recycleList) **
  store_all_stack st **
  store_ghost_task sg st.(ghostTaskInfo) **
  store_runTask sg st.(runTask) ** store_newTask sg st.(newTask) **
  store_idleTaskID sg.(idleTaskID) ** store_swtmrTaskID sg.(swtmrTaskID) **
  store_losTaskLock st.(losTaskLock).

Definition store_free_recycle_list_exclude (sg: StableGlobVars) (l : list RecycleTaskAbstractState) (tID : TaskID) : Assertion :=
  EX l0: list (DL_Node (RecycleTaskAbstractState)),
  [| map DLL.data l0 = l |] &&
  store_dll 
  (fun p recycle_tskabs =>
       EX ctrl_start: addr,
       [| ctrl_start = sg.(g_taskCBArray) + sizeof("LosTaskCB") * recycle_tskabs.(recycle_tID) |] &&
       [| p = &(ctrl_start # "LosTaskCB" ->ₛ "pendList") |] &&
       (if Z.eq_dec recycle_tskabs.(recycle_tID) tID then emp else recycle_task ctrl_start recycle_tskabs)
       )
    (&("g_taskRecycleList")) l0.



Definition task_inv_missing_recycletask (taskID : TaskID)  (sg: StableGlobVars) (st: TcbGlobalState): Assertion :=
  [| exists b, In b st.(recycleList) /\ b.(recycle_tID) = taskID |] &&
  [| task_vaild_cond_prop sg st |] &&
  store_used_task_map sg st.(usedTask) **
  store_free_task_list sg st.(freeTask) **
  store_free_recycle_list_exclude sg st.(recycleList) taskID **
  store_all_stack st **
  store_ghost_task sg st.(ghostTaskInfo) **
  store_runTask sg st.(runTask) ** store_newTask sg st.(newTask) **
  store_idleTaskID sg.(idleTaskID) ** store_swtmrTaskID sg.(swtmrTaskID) **
  store_losTaskLock st.(losTaskLock).


Lemma task_inv_implies_inv_missing_usedtask (taskID : TaskID) (sg: StableGlobVars) (st: TcbGlobalState) :
  ( exists b, st.(usedTask) taskID = Some b) -> (
  task_inv sg st |--
  EX b, [| st.(usedTask) taskID = Some b |] &&
  task_inv_missing_usedtask taskID sg st **
  (used_complete_task sg (sg.(g_taskCBArray) + sizeof("LosTaskCB") * taskID) taskID b)
  ).
  Proof. pre_process. destruct H.
  Exists x. entailer!.
  unfold task_inv. unfold task_inv_missing_usedtask.
  entailer!. 
  - unfold store_used_task_map_exclude. unfold store_used_task_map.  
  pose(f:= fun (taskID0 : Z) (t : TaskAbstractState) => 
  used_complete_task sg 
                    (sg.(g_taskCBArray) + sizeof ("LosTaskCB") * taskID0) 
                    taskID0 t
                    ).
  fold f.
  assert(HH: (f taskID x) = used_complete_task sg
  (sg.(g_taskCBArray) + sizeof ("LosTaskCB") * taskID) taskID x ).
  unfold f. simpl. auto. rewrite <- HH.
  apply (store_map_split). auto.
  - exists x. auto.
  Qed.

Lemma inv_missing_usedtask_implies_task_inv (taskID : TaskID) (sg: StableGlobVars) (st: TcbGlobalState) :
    EX b, [| st.(usedTask) taskID = Some b |] &&
    task_inv_missing_usedtask taskID sg st **
    (used_complete_task sg (sg.(g_taskCBArray) + sizeof("LosTaskCB") * taskID) taskID b)
    |--
    task_inv sg st.
  Proof. pre_process. Intros x.
  unfold task_inv. unfold task_inv_missing_usedtask. 
  entailer!. unfold store_used_task_map_exclude. 
  pose(f:= fun (taskID0 : Z) (t : TaskAbstractState) => 
  used_complete_task sg 
                    (sg.(g_taskCBArray) + sizeof ("LosTaskCB") * taskID0) 
                    taskID0 t
                    ).
  fold f. 
  assert(HH: (f taskID x) = used_complete_task sg
  (sg.(g_taskCBArray) + sizeof ("LosTaskCB") * taskID) taskID x ).
  unfold f. simpl. auto. rewrite <- HH. apply store_map_merge. auto.
  Qed.


Lemma task_inv_implies_inv_missing_unusedtask (taskID : TaskID) (sg: StableGlobVars) (st: TcbGlobalState) :
  (In taskID st.(freeTask)) -> (
  task_inv sg st |--
  task_inv_missing_unusedtask taskID sg st **
  (unused_task (sg.(g_taskCBArray) + sizeof ("LosTaskCB") * taskID) taskID)
  ).
  Proof. pre_process. 
  unfold task_inv, task_inv_missing_unusedtask.
  entailer!. 
  remember (freeTask st) as freelist. 
  assert(HH: NoDup freelist).
  - destruct H0. destruct task_cond9. rewrite <- Heqfreelist in H0. auto.
  - Admitted.

Lemma inv_missing_unusedtask_implies_task_inv (taskID : TaskID) (sg: StableGlobVars) (st: TcbGlobalState) :
  task_inv_missing_unusedtask taskID sg st **
  (unused_task (sg.(g_taskCBArray) + sizeof ("LosTaskCB") * taskID) taskID)
  |--
  task_inv sg st.
Proof. pre_process. 
unfold task_inv, task_inv_missing_unusedtask.
entailer!. Admitted.

Lemma task_inv_implies_inv_missing_recycletask (taskID : TaskID) (sg: StableGlobVars) (st: TcbGlobalState) :
( exists b, In b st.(recycleList) /\ b.(recycle_tID) = taskID ) -> (
task_inv sg st |--
EX b, [| In b st.(recycleList) /\ b.(recycle_tID) = taskID |] &&
task_inv_missing_recycletask taskID sg st **
(recycle_task (sg.(g_taskCBArray) + sizeof ("LosTaskCB") * taskID) b)
).

Proof. Admitted.

Lemma inv_missing_recycletask_implies_task_inv (taskID : TaskID) (sg: StableGlobVars) (st: TcbGlobalState) :
EX b, [| In b st.(recycleList) /\ b.(recycle_tID) = taskID |] &&
task_inv_missing_recycletask taskID sg st **
(recycle_task (sg.(g_taskCBArray) + sizeof ("LosTaskCB") * taskID) b)
|--
task_inv sg st
.
Proof. Admitted.

Lemma testbit_with_land : forall n i,
  n >= 0 /\ i >= 0 -> (Z.testbit n i = true <-> Z.land n (Z.shiftl 1 i) <> 0).
Proof. Admitted.

Lemma testbit_with_land_false : forall n i,
  n >= 0 /\ i >= 0 -> (Z.testbit n i = false <-> Z.land n (Z.shiftl 1 i) = 0).
Proof. Admitted.

(** Props on low level abstract state (concrete state) 

(* UsedTask(taskid) != none, then 0 <= taskID < g_taskMaxNum.  *)
Definition usedTask_id_in_range (st : TcbGlobalState): Prop  :=
  forall taskID,
    match st.(usedTask) taskID with
    | Some _ => 0 <= taskID < g_taskMaxNum
    | None => True
    end.

(* simillary, tasks in freelist and recycle list satisfies 0 <= taskID < g_taskMaxNum. *)
Definition freeTask_id_in_range (st : TcbGlobalState): Prop :=
  Forall (fun taskID => 0 <= taskID < g_taskMaxNum) st.(freeTask).

Definition recycleList_id_in_range (st : TcbGlobalState): Prop :=
  Forall (fun recycle_tskabs => 0 <= recycle_tskabs.(recycle_tID) < g_taskMaxNum ) 
         st.(recycleList).

(* disjointness on usedTask, freeTask, and recycleList *)
Definition disjointness_on_taskID (st : TcbGlobalState) : Prop :=
  (forall taskID, 
  match st.(usedTask) taskID with
    | Some _ => ~ (exists a , a.(recycle_tID) = taskID /\ In  a st.(recycleList)) /\ ~ In taskID st.(freeTask)
    | None => True
  end) 
  /\
  Forall (fun taskID => 
  st.(usedTask) taskID = None /\ ~ (exists a, a.(recycle_tID) = taskID /\ In  a st.(recycleList)) ) st.(freeTask) 
  /\
  Forall (fun recycle_tskabs =>  st.(usedTask) recycle_tskabs.(recycle_tID) = None /\ ~ In recycle_tskabs.(recycle_tID) st.(freeTask)) st.(recycleList).

(* status restriction on usedTask *)
Parameter exictly_one_true : bool -> bool ->bool -> Prop.

Definition vaild_usedTask_status (status : Z) : Prop :=
  (Z.testbit status STATUS_PEND_TIME = true -> Z.testbit status STATUS_PEND = true )  (* pend_time -> pend *)
  /\ 
  (Z.testbit status STATUS_DELAY = true -> Z.testbit status STATUS_PEND = false )     (* pend 和 delay 互斥 *)
  /\ 
  (Z.testbit status STATUS_PEND = true -> Z.testbit status STATUS_DELAY = false )     (* pend 和 delay 互斥 *)
  /\ 
  ( exictly_one_true (Z.testbit status STATUS_RUNNING)  
                     (Z.testbit status STATUS_READY)    
                     ( (Z.testbit status STATUS_PEND) || (Z.testbit status STATUS_PEND_TIME) || (Z.testbit status STATUS_SUSPEND) || (Z.testbit status STATUS_DELAY)) 
                     ).
  
Definition status_restriction_on_usedTask (st : TcbGlobalState) :Prop :=
  forall taskID,
  match st.(usedTask) taskID with
  | Some abstate => vaild_usedTask_status abstate.(status)
  | None => True
  end.

Definition vaild_runTask (st : TcbGlobalState) : Prop :=
  exists abstate, st.(usedTask) st.(runTask) = Some abstate /\
                  Z.testbit abstate.(status) STATUS_RUNNING = true.

**)


(** high level abstract state, encode only what OS user can perceive   **)

(*
Inductive block_status :=
| pend
| pend_and_pendtime : Z -> block_status  (* record waittime when pendtime *)
| delay : Z -> block_status  (* record waittime when delay *)
| pend_and_suspend
| pend_and_pendtime_and_suspend : Z -> block_status (* record waittime when pendtime *)
| delay_and_suspend:  Z -> block_status.  (* record waittime when delay *)
*)

Inductive used_status_h :=
 | ready
 | running
 | pend
 | pend_and_pendtime : Z -> used_status_h  (* record waittime when pendtime *)
 | delay : Z -> used_status_h  (* record waittime when delay *)
 | pend_and_suspend
 | pend_and_pendtime_and_suspend : Z -> used_status_h (* record waittime when pendtime *)
 | delay_and_suspend:  Z -> used_status_h  (* record waittime when delay *)
 | timeout
 | timeout_and_suspend.

 Record used_flag_h := mkflag {
    system_task : bool; 
    stack_free : bool;
    joinable : bool;
    freeze : bool
 }.

Record TaskHighAbstractState := mkTaskHighAbstractState {
    status_h : used_status_h;
    flag_h : used_flag_h;
    tPrio_h : Z;
    tTimeSlice_h : Z;
    tStartTime_h : Z;
    tTaskEntry_h : addr;
    tTaskSem_h : addr;
    tTaskMux_h : addr;
    tArg_h : Z;
    tTaskName_h : addr;
    tJoinList_h : list TaskID;
    tJoinRetval_h : Z;
    tMsg_h : addr;
}.

Record TcbHighGlobalState := mkTcbHighGlobalState {
    usedTask_h : TaskID -> option TaskHighAbstractState; 
    freeTask_and_recycleList_h : list TaskID;     
    runTask_h : TaskID;             
    newTask_h : TaskID;      
    losTaskLock_h : Z;      
    idleTaskID_h : TaskID;
    swtmrTaskID_h : TaskID;
}.


(* refinement between high level abstract state and low level abstract state *)

Parameter TcbGlobalState_to_TcbHighGlobalState:  TcbGlobalState -> TcbHighGlobalState.
 
Definition refinement_TcbGlobalState_TcbHighGlobalState 
              (st : TcbGlobalState) (st_h :TcbHighGlobalState) : Prop :=
  TcbGlobalState_to_TcbHighGlobalState st = st_h.
  


(*
emp ---- >   highlevelstate 
f:
...
enter_critical
sep_map(a)  a

sep_map(b)  abs_op (a) = b
exit_critical

                              
emp ----->  highlevelstate'


abs_op   --> coq: highlevelstate -> highlevelstate

invariant
critical
invariant
*)