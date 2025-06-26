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
Local Open Scope sac.
Require Import LOS_Verify.lib.dll.
Require Import LOS_Verify.lib.sortlink.
Import SDLL.

Record TaskFlag := mkTaskFlag {
    user_task : bool;
    system_task : bool;
    stack_free : bool;
    signal : bool;
    joinable : bool;
    freeze : bool
}.

Record waitstatus := mkWaitStatus{
    suspend : bool;
    pend : bool;
    delayed : option Z; (* WaitTimes *)
    time_out : bool;
    pend_time : option Z (* WaitTimes *)
}.

Inductive UsedStatus :=
    | recycle : UsedStatus (* in recycle list, running + exit + unused *)
    | ready : Z -> UsedStatus
    | running : UsedStatus
    | wait : waitstatus -> UsedStatus.


Record TaskAbstractState := mkTaskAbstractState {
    status : UsedStatus;
    taskFlag : TaskFlag;
    tPrio : Z;
    tStackPointer : addr;
    tStartTime : Z;
    tStackSize : Z;
    tTopOfStack : Z;
    tTaskName : Z;
    tTaskEntry : addr;
    tArg : Z;
    tJoinList : list TaskID;
    tJoinRetval : Z;
}.

Definition taskMaxNum := 32.

(* 任务的全局状态，包括所有已使用的任务的抽象状态，未使用的任务，回收列表等 *)
Record TcbGlobalState := mkTcbGlobalState {
    usedTask : TaskID -> option TaskAbstractState;
    freeTask : list TaskID;
    recycleList : list TaskID;
    runTask : TaskID;
    newTask : option TaskID;
    losTaskLock : Z;
    idleTaskID : TaskID;
    swtmrTaskID : TaskID;
}.

Definition check_ready_status (status : UsedStatus) : bool :=
  match status with
  | ready ts => if Z.eqb ts 0 then false else true (* status is ready with a non-zero timeSlice *)
  | _ => false (* status is not ready *)
  end.


Definition get_waitstatus_from_usedstatus (us : UsedStatus) : option waitstatus :=
  match us with
  | wait ws => Some ws (* Extract waitstatus if usedstatus is in wait state *)
  | _ => None (* Return None for other cases *)
  end.

Definition check_delay_status (us : UsedStatus) : bool :=
  match get_waitstatus_from_usedstatus us with
  | Some ws => 
      match ws with
      | mkWaitStatus _ _ (Some _) _ _ => true (* delayed is Some *)
      | _ => false (* other cases *)
      end
  | None => false (* No waitstatus *)
  end.

Definition check_pend_time_status (us : UsedStatus) : bool :=
  match get_waitstatus_from_usedstatus us with
  | Some ws => 
      match ws with
      | mkWaitStatus _ _ _ _ (Some _) => true (* pend_time is Some *)
      | _ => false (* other cases *)
      end
  | None => false (* No waitstatus *)
  end.

Definition get_delayed_from_usedstatus (us : UsedStatus) : option Z :=
  match us with
  | wait ws => delayed ws (* Extract delayed field from waitstatus if usedstatus is in wait state *)
  | _ => None (* Return None for other cases *)
  end.

Definition get_pend_time_from_usedstatus (us : UsedStatus) : option Z :=
  match us with
  | wait ws => pend_time ws (* Extract delayed field from waitstatus if usedstatus is in wait state *)
  | _ => None (* Return None for other cases *)
  end.

Definition check_stack_free_flag (tf : TaskFlag) : bool :=
  match tf with
  | mkTaskFlag _ _ true _ _ _ => true (* stack_free is false *)
  | _ => false (* stack_free is true or other cases *)
  end.

Definition check_joinable_flag (tf : TaskFlag) : bool :=
  match tf with
  | mkTaskFlag _ _ _ _ true _ => true (* stack_free is false *)
  | _ => false (* stack_free is true or other cases *)
  end.

(* 上面TaskNBitMap 与 FlagNBitMap 的定义*)     
  
Definition WaitNumberBitMap (ws : waitstatus) : Z :=
  let suspend := if ws.(suspend) then 1 else 0 in
  let pend := if ws.(pend) then 1 else 0 in
  let delayed := if ws.(delayed) then 1 else 0 in
  let time_out := if ws.(time_out) then 1 else 0 in
  let pend_time := if ws.(pend_time) then 1 else 0 in
  suspend * 2 + pend * 8 + delayed * 32 + time_out * 64 + pend_time * 128.


Definition UsedTaskNBitMap (ts : UsedStatus) : Z :=
match ts with
| ready _ => 4
| running => 16
| recycle => 256 + 16 + 1
| wait ws => WaitNumberBitMap ws
end.

Definition FlagNBitMap (ts : TaskFlag) : Z :=
  let user_task_num := if ts.(user_task) then 1 else 0 in
  let stack_free_num := if ts.(stack_free) then 1 else 0 in
  let system_task_num := if ts.(system_task) then 1 else 0 in
  let signal_num := if ts.(signal) then 1 else 0 in
  let joinable_num := if ts.(joinable) then 1 else 0 in
  let freeze_num := if ts.(freeze) then 1 else 0 in
  user_task_num * 512 + stack_free_num * 2048 + system_task_num * 4096 + signal_num * 8192 + freeze_num * 16384 + joinable_num * 32768.

Definition Check_not_system_task (st : TaskAbstractState) : Prop :=
  system_task (st.(taskFlag)) = false.

Definition get_ready_timeSlice (us : UsedStatus) : Z :=
  match us with
  | ready ts => ts (* Return timeSlice if the status is ready *)
  | _ => 0 (* Return 0 for other cases *)
  end.

Definition set_waitTimes (ctrl_start: addr) (us : UsedStatus): Assertion := 
  match us with
  | wait ws => 
    &(ctrl_start # "LosTaskCB" ->ₛ "waitTimes") # UInt |-> 
    match ws with
    | mkWaitStatus _ _ (Some ts) _ _ => ts (* delayed is Some *)
    | mkWaitStatus _ _ _ _ (Some ts ) => ts (* pend_time is Some *)
    | _ => 0 (* other cases *)
    end
  | _ => &(ctrl_start # "LosTaskCB" ->ₛ "waitTimes") # UInt |-> 0 (* No waitstatus *)
end.

Definition set_pendList (ctrl_start: addr) (us : UsedStatus): Assertion :=
  match us with
  | ready ts => emp(* status is ready *)
  | wait ws =>
      match ws with
      | mkWaitStatus _ true _ _ _ => emp (* pend *)
      | _ =>  (* other cases *)
         occupy_dll_node (&(ctrl_start # "LosTaskCB" ->ₛ "pendList"))
      end
  | _ =>  (* status is not ready or ready without a timeSlice *)
     occupy_dll_node (&(ctrl_start # "LosTaskCB" ->ₛ "pendList"))
  end.

Definition set_timeSlice (ctrl_start: addr) (us : UsedStatus): Assertion := 
  match us with
  | ready ts =>
        &(ctrl_start # "LosTaskCB" ->ₛ "timeSlice") # Int |-> ts
  | _ =>  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "timeSlice") # Int |-> __
  end.

(* 单个used 任务的高层抽象与其底层表示的对应 *)
Definition used_complete_task (sg: StableGlobVars) (ctrl_start: addr) (tID : TaskID) (tskabs: TaskAbstractState): Assertion :=
    (* 控制块信息，假设存储在ctrl_start开始的连续地址中 *)
    &(ctrl_start # "LosTaskCB" ->ₛ "taskID") # UInt |-> tID **
    &(ctrl_start # "LosTaskCB" ->ₛ "taskStatus") # UShort |-> (UsedTaskNBitMap(tskabs.(status)) + FlagNBitMap(tskabs.(taskFlag))) ** 
    &(ctrl_start # "LosTaskCB" ->ₛ "priority") # UShort |-> tskabs.(tPrio) **
    &(ctrl_start # "LosTaskCB" ->ₛ "stackPointer") # Ptr |-> tskabs.(tStackPointer) **
    &(ctrl_start # "LosTaskCB" ->ₛ "startTime") # UInt64 |-> tskabs.(tStartTime) **
    &(ctrl_start # "LosTaskCB" ->ₛ "stackSize") # UInt |-> tskabs.(tStackSize) **
    &(ctrl_start # "LosTaskCB" ->ₛ "taskName") # Ptr |-> tskabs.(tTaskName) **
    &(ctrl_start # "LosTaskCB" ->ₛ "topOfStack") # UInt |-> tskabs.(tTopOfStack) **
    &(ctrl_start # "LosTaskCB" ->ₛ "taskEntry") # Ptr |-> tskabs.(tTaskEntry) **
    &(ctrl_start # "LosTaskCB" ->ₛ "arg") # UInt |-> tskabs.(tArg) **
    &(ctrl_start # "LosTaskCB" ->ₛ "joinRetval") # UInt |-> tskabs.(tJoinRetval) **  (* 处于ready状态才有timeSlice *)
    (* 处于ready状态才有timeSlice *)
    set_timeSlice ctrl_start tskabs.(status) **
    (* 处于delay | pend_time状态才有waitTimes *)
    set_waitTimes ctrl_start tskabs.(status) **
    (* pend | ready  状态时，pendList的权限不在taskCB *)
    set_pendList ctrl_start tskabs.(status) **
    (* joinList 只有taskCB使用 *)
    store_pend_list_dll sg (&(ctrl_start # "LosTaskCB" ->ₛ "joinList")) tskabs.(tJoinList)
    .
(* 上面TaskNBitMap 与 FlagNBitMap 的定义*)     


(*  测试
Definition example_waitstatus := mkWaitStatus false false None false None.
Definition example_bitmap := 10.
Compute TaskStatusBitMap example_bitmap [example_waitstatus].
Definition example_waitstatus_1 := mkWaitStatus true false (Some (Z.of_nat 1)) false (Some (Z.of_nat 1)).
Definition example_taskstatus_1 := used (wait example_waitstatus_1).
Compute status_to_number example_taskstatus_1.
*)

Definition unused_task (ctrl_start: addr) (taskID : TaskID) : Assertion :=
  &(ctrl_start # "LosTaskCB" ->ₛ "taskID") # UInt |-> taskID **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "taskStatus") # UShort |-> __ ** 
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "priority") # UShort |-> __ **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "stackPointer") # Ptr |-> __ **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "startTime") # UInt64 |-> __ **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "stackSize") # UInt |-> __ **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "topOfStack") # UInt |-> __ **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "taskEntry") # Ptr |-> __ **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "taskName") # Ptr |-> __ **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "arg") # UInt |-> __ **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "joinRetval") # UInt |-> __ ** 
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "timeSlice") # Int |-> __ **
  EX __,  &(ctrl_start # "LosTaskCB" ->ₛ "waitTimes") # UInt |-> __ ** 
  occupy_dll_node (&(ctrl_start # "LosTaskCB" ->ₛ "joinList")).

Definition g_taskRecycleList_store (sg: StableGlobVars) (ts: list TaskID): Assertion :=
  store_pend_list_dll sg (&("g_taskRecycleList")) ts.

Notation "[ ]" := nil.

Definition range (i : Z) : list Z :=
    map Z.of_nat (List.seq 0 (Z.to_nat i)).

Fixpoint reverseRange (l : list nat) : list Z :=
  match l with
  | nil  => nil
  | a::l0 => reverseRange l0  ++ (Z.of_nat a::nil)
  end.

Definition check_single_task (st : TcbGlobalState) (taskID : TaskID): Prop :=
  In taskID st.(freeTask) ->
  st.(usedTask) taskID = None.

Definition check_task_list (st : TcbGlobalState): Prop :=
  forall taskID,
    0 <= taskID < taskMaxNum ->
    check_single_task st taskID.

Definition used_task_in_range (st : TcbGlobalState): Prop :=
  forall taskID,
    match st.(usedTask) taskID with
    | Some _ => 0 <= taskID < taskMaxNum
    | None => True
    end.

Definition free_task_in_range (st : TcbGlobalState): Prop :=
  Forall (fun taskID => 0 <= taskID < taskMaxNum) st.(freeTask).

Definition check_taskRecycleList (st : TcbGlobalState) (taskID : TaskID): Prop :=
    match st.(usedTask) taskID with
    | None => False
    | Some b => b.(status) = recycle
    end.

Definition check_recycle_task_list (st : TcbGlobalState): Prop :=
  forall a, In a st.(recycleList) <-> check_taskRecycleList st a.

(* 判断status是否vaild *)
Definition check_wait (states : waitstatus) : Prop :=
  match states with
  | mkWaitStatus true false None false None => True (* suspend *)
  | mkWaitStatus true false (Some _) false None => True (* suspend + delay *)
  | mkWaitStatus true true None false (Some _) => True (* suspend + pend + pendtime *)
  | mkWaitStatus false false None true None => True (* timeout *)
  | mkWaitStatus false true None false None => True (* pend *)
  | mkWaitStatus false true None false (Some _) => True (* pend + pendtime *)
  | mkWaitStatus false false (Some _) true None => True (* delay *)
  | mkWaitStatus _ _ _ _ _ => False
  end.

Definition valid_status_single_task (ts : UsedStatus) : Prop :=
  match ts with
  | recycle => True (* Unused status is always valid *)
  | ready _ => True
  | running => True
  | wait states => check_wait states
  end.

Definition status_restriction (st : TcbGlobalState) : Prop := 
  forall taskID, 
  if Z.eqb taskID st.(runTask) then
    exists tsk,st.(usedTask) taskID = Some tsk -> status tsk = running
  else
    match st.(usedTask) taskID with
    | Some tsk => valid_status_single_task (status tsk)
    | None => True
    end. 

Record valid_TcbGlobalState (st : TcbGlobalState): Prop :=
  {
    used_free: check_task_list st;
    used_range: used_task_in_range st;
    free_range: free_task_in_range st;
    recycle_status: check_recycle_task_list st;
    vaild_status: status_restriction st
  }.

(* vaild 条件 *)
(* for all tid not in free and usedTask Some(_) *)
(* init 函数的  *)
(* Pre Post Condition...*)
(*Todo: TSK_INIT_PARAM_S Record {...} *)
Inductive returnstatus: Type :=
  | LOS_ERRNO_TSK_NO_MEMORY 
  | LOS_NOK
  | LOS_OK
  | LOS_ERRNO_TSK_NOT_JOIN.


Definition sizeOfTaskCB : Z := 128.

Definition store_used_task_map
             (sg: StableGlobVars)
             (m: TaskID -> option TaskAbstractState): Assertion :=
  store_map
    (fun taskID t =>
      used_complete_task sg (sg.(g_taskCBArray) + sizeof( "LosTaskCB") * taskID) taskID t)
    m.

Definition store_used_task_map_exclude
            (sg: StableGlobVars)
            (m: TaskID -> option TaskAbstractState)
            (missingID: TaskID): Assertion :=
  store_map_missing_i
    (fun taskID t => 
      used_complete_task sg (sg.(g_taskCBArray) + sizeof( "LosTaskCB") * taskID) taskID t)
    m missingID.


Definition store_free_task_list (sg: StableGlobVars) (l: list TaskID): Assertion :=
  EX l0: list (DL_Node TaskID),
    [| map DLL.data l0 = l |] &&
    store_dll
      (fun p taskID =>
         EX ctrl_start: addr,
         [| ctrl_start = sg.(g_taskCBArray) + sizeof( "LosTaskCB") * taskID |] &&
         [| p = &(ctrl_start # "LosTaskCB" ->ₛ "pendList") |] &&
           unused_task ctrl_start taskID)
      (&("g_losFreeTask")) l0.

Definition store_glob_task (sg: StableGlobVars) (s: TcbGlobalState): Assertion :=
  store_used_task_map sg s.(usedTask) **
  store_free_task_list sg s.(freeTask) **
  g_taskRecycleList_store sg s.(recycleList).

Definition store_glob_task_states 
                (st: TcbGlobalState) 
                (sg: StableGlobVars): Assertion :=
  &((&("g_losTask")) ->ₛ "runTask") # Ptr |-> (sg.(g_taskCBArray) + st.(runTask) * sizeof( "LosTaskCB")) **
  match st.(newTask) with 
    | Some b =>&(&("g_losTask") ->ₛ "newTask") # Ptr |-> (sg.(g_taskCBArray) + b * sizeof( "LosTaskCB"))
    | None => &(&("g_losTask") ->ₛ "newTask") # Ptr |-> (sg.(g_taskCBArray) + sg.(idleTaskID) * sizeof( "LosTaskCB"))
  end
  ** &("g_losTaskLock") # UShort |-> st.(losTaskLock).

Import SDLL.
(* 表示调度中 sortedlink 的谓词在调度模块，l 为调度模块中的排序链表抽象状态，下方为vaild 条件 *)
Definition vaild_sortedLink (s : TcbGlobalState) (l : list (sortedLinkNode TaskID)): Prop :=
  forall sln:(sortedLinkNode TaskID) , (In sln l <->
    exists (tsk:TaskAbstractState) (t1: TaskID) (t2: TaskID) (_1 _2 _4: bool) (_3 _5: option Z), 
                     ((s.(usedTask) sln.(sl_data)) = Some tsk) 
                  /\ ((tsk.(status) = wait (mkWaitStatus _1 _2 (Some t1) _4 _5) ) \/ (tsk.(status) = wait (mkWaitStatus _1 _2 _3 _4 (Some t2 ) ))) (*status equals delayed / pendtime *)
                  /\ sln.(responseTime) = t1 + t2).

Fixpoint initialtaskCTB (base: addr) (l: list Z) (st: TcbGlobalState) : Assertion :=
  match l with
      | nil => emp
      | z :: l0 =>
          (unused_task (base + z*sizeOfTaskCB) z)
          ** initialtaskCTB base l0 st
  end.

Fixpoint mapallnone (l:list Z) (st: TcbGlobalState) : Prop :=
  match l with 
  | nil => True
  | z :: l0 => match (usedTask st) z with
                  | None => mapallnone l0 st
                  | Some _ => False
              end
  end.


(* OsTaskInit Pre_Post 

Definition PostOsTaskInit (base: addr) (st: TcbGlobalState) (result : returnstatus) : Assertion :=
  [| result = LOS_OK |] && 
  (let l := reverseRange (range (Z.to_nat taskMaxNum)) in
      [| l = st.(freeTask) |] && 
      [| mapallnone l st|] && 
      initialtaskCTB base l st).
*)

(* OsInsertTCBToFreeList Pre_Post *)

(* 
STATIC INLINE VOID OsInsertTCBToFreeList(LosTaskCB *taskCB)
{
    UINT32 taskID = taskCB->taskID;
    (VOID)memset_s(taskCB, sizeof(LosTaskCB), 0, sizeof(LosTaskCB));
    taskCB->taskID = taskID;
    taskCB->taskStatus = OS_TASK_STATUS_UNUSED;
    LOS_ListAdd(&g_losFreeTask, &taskCB->pendList);
} *)

Definition PreOsInsertTCBToFreeList'
    (taskID : TaskID) 
    (sg: StableGlobVars)
    (FreeTask: list TaskID)  : Assertion :=
    store_free_task_list sg FreeTask ** 
    EX __, (EX __0, used_complete_task sg __ taskID __0).

Definition PostOsInsertTCBToFreeList
    (taskID : TaskID) 
    (sg: StableGlobVars)
    (FreeTask FreeTask' : list TaskID) : Assertion :=
    [| FreeTask' = taskID :: FreeTask |] ** 
    EX __, unused_task __ taskID **
    store_free_task_list sg (taskID :: FreeTask).

(********************************************************************)
(* LOS_ListDelete Pre_Post *)

(* LITE_OS_SEC_ALW_INLINE STATIC_INLINE VOID LOS_ListDelete(LOS_DL_LIST *node)
{
    node->pstNext->pstPrev = node->pstPrev;
    node->pstPrev->pstNext = node->pstNext;
    node->pstNext = (LOS_DL_LIST * )NULL;
    node->pstPrev = (LOS_DL_LIST * )NULL;
} *)

Definition PreLOS_ListDelete
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr)
             (l1: list (DL_Node A)) (a: A) (l2: list (DL_Node A)): Assertion :=
  store_dll storeA x (l1 ++ {| DLL.data := a; DLL.ptr := u |} :: l2).

Definition PostLOS_ListDelete
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr)
             (l1: list (DL_Node A)) (a: A) (l2: list (DL_Node A)): Assertion :=
  storeA u a **
  &(u # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> 0 **
  &(u # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> 0 **
  store_dll storeA x (l1++l2).

(********************************************************************)
(* LOS_ListEmpty Pre_Post *)

(* LITE_OS_SEC_ALW_INLINE STATIC_INLINE BOOL LOS_ListEmpty(LOS_DL_LIST *node)
{
    return (BOOL)(node->pstNext == node);
} *)

Definition PreLOS_ListEmpty
  {A: Type} (storeA: addr -> A -> Assertion)
  (x: addr)(l: list (DL_Node A)): Assertion :=
store_dll storeA x l.

Definition PostLOS_ListEmpty
  {A: Type} (storeA: addr -> A -> Assertion)
  (x: addr) (l: list (DL_Node A))(__return: Z): Assertion :=
[| (l = nil /\ __return = 1) \/ (l <> nil /\ __return = 0) |] **
store_dll storeA x l.

(********************************************************************)
(* STATIC VOID OsRecycleTaskResources(LosTaskCB *taskCB, UINTPTR *stackPtr)
{
    if ((taskCB->taskStatus & OS_TASK_FLAG_STACK_FREE) && (taskCB->topOfStack != 0)) {
        taskCB->topOfStack = (UINT32)NULL;
        taskCB->taskStatus &= ~OS_TASK_FLAG_STACK_FREE;
    }
    if (!(taskCB->taskStatus & OS_TASK_FLAG_JOINABLE)) {
        OsInsertTCBToFreeList(taskCB);
    }
} *)

(* OsRecycleTaskResources Pre_Post *)
Definition PreOsRecycleTaskResources
  (tskabs : TaskAbstractState)
  (taskID : TaskID)
  (sg: StableGlobVars)
  (FreeTask : list TaskID) 
  (stackPtr : addr) : Assertion :=
  EX __, used_complete_task sg (__ + taskID * sizeOfTaskCB) taskID tskabs **
  store_free_task_list sg FreeTask.

Definition PostOsRecycleTaskResources
  (tskabs tskabs': TaskAbstractState)
  (taskID : TaskID)
  (sg: StableGlobVars)
  (FreeTask FreeTask': list TaskID) 
  (stackPtr : addr) : Assertion :=
  match (joinable (tskabs.(taskFlag))) with
    | true => (* not to unused *)
      match andb (stack_free (tskabs.(taskFlag)))%bool (Z.eqb (tTopOfStack tskabs) 0)%bool with
        | true => (* remove stack_free & clear topOfStack *)
          [| stack_free (tskabs'.(taskFlag)) = false |] &&
          [| (tTopOfStack tskabs') = 0  |] && (* topOfStack == null *)
          [| FreeTask' = taskID :: FreeTask |] &&
          EX __, used_complete_task sg (__ + taskID * sizeOfTaskCB) taskID tskabs' **
          store_free_task_list sg FreeTask'
        | false => 
        EX __, used_complete_task sg (__ + taskID * sizeOfTaskCB) taskID tskabs
      end
    | false =>
      EX __, unused_task (__ + taskID * sizeOfTaskCB) taskID
  end.

(********************************************************************)
(* STATIC UINT32 OsTaskJoinPendUnsafe(LosTaskCB *taskCB)
{
    if (taskCB->taskStatus & OS_TASK_STATUS_EXIT) {
        return LOS_OK;
    } else if ((taskCB->taskStatus & OS_TASK_FLAG_JOINABLE) && LOS_ListEmpty(&taskCB->joinList)) {
        OsSchedTaskWait(&taskCB->joinList, LOS_WAIT_FOREVER);
        return LOS_OK;
    }

    return LOS_NOK;
} *)

(* OsTaskJoinPendUnsafe Pre_Post *)
Definition List_empty {A: Type} (a : list A) : bool :=
  match a with
  | nil => true (* 如果列表为空，则返回 true *)
  | _ => false (* 否则返回 false *)
  end.

Definition PreOsTaskJoinPendUnsafe
  (tskabs tskabs_run: TaskAbstractState)
  (sg: StableGlobVars)
  (run_id: TaskID) : Assertion := 
  EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs) **
  EX __, used_complete_task sg (__ + run_id * sizeOfTaskCB) run_id tskabs_run.

Definition PostOsTaskJoinPendUnsafe
  (tskabs tskabs' tskabs_run tskabs_run' : TaskAbstractState)
  (run_id : TaskID) 
  (sg: StableGlobVars)
  (result : returnstatus) : Assertion := 
  match (tskabs.(status)) with
    | recycle => 
      [| result = LOS_OK |] &&
      EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs)
    | _ => 
      match andb (joinable (tskabs.(taskFlag)))%bool (List_empty (tJoinList tskabs)) with
        | true => 
          [| result = LOS_OK |] && 
          [| tskabs_run'.(status) = wait (mkWaitStatus false true None false None) |] &&
          [| tJoinList tskabs' = cons run_id (tJoinList tskabs) |] &&
          EX __, (used_complete_task sg (__ + run_id * sizeOfTaskCB) run_id tskabs_run) ** (* runtask *)
          EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs')
        | false => 
          [| result = LOS_NOK |]
      end
  end.

(********************************************************************)
(* STATIC UINT32 OsTaskSetDetachUnsafe(LosTaskCB *taskCB)
{
    if (taskCB->taskStatus & OS_TASK_FLAG_JOINABLE) {
        if (LOS_ListEmpty(&(taskCB->joinList))) {
            LOS_ListDelete(&(taskCB->joinList));
            taskCB->taskStatus &= ~OS_TASK_FLAG_JOINABLE;
            return LOS_OK;
        }
        /* This error code has a special purpose and is not allowed to appear again on the interface */
        return LOS_ERRNO_TSK_NOT_JOIN;
    }

    return LOS_NOK;
} *)

(* OsTaskSetDetachUnsafe Pre_Post*)
Definition PreOsTaskSetDetachUnsafe
  (sg: StableGlobVars)
  (tskabs : TaskAbstractState) : Assertion := 
  EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs).

Definition PostOsTaskSetDetachUnsafe
  (tskabs tskabs' : TaskAbstractState)
  (sg: StableGlobVars)
  (result : returnstatus): Assertion := 
  match joinable(tskabs.(taskFlag)) with
    | true => 
      match List_empty (tJoinList tskabs) with
      | true =>
        [| result = LOS_OK |] &&
        [| joinable(tskabs'.(taskFlag)) = false |] && 
        EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs')
      | false =>
        [| result = LOS_ERRNO_TSK_NOT_JOIN |] &&
        EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs)
      end
    | false =>
      [| result = LOS_NOK |] &&
      EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs)
  end.

(********************************************************************)
(* STATIC VOID OsTaskJoinPostUnsafe(LosTaskCB *taskCB)
{
    LosTaskCB *resumedTask = NULL;

    if (taskCB->taskStatus & OS_TASK_FLAG_JOINABLE) {
        if (!LOS_ListEmpty(&taskCB->joinList)) {
            resumedTask = OS_TCB_FROM_PENDLIST(LOS_DL_LIST_FIRST(&(taskCB->joinList)));
            OsSchedTaskWake(resumedTask);
        }
    }
} *)

(* OsTaskJoinPostUnsafe Pre_Post *) (* 只能在TcbGlobalState里找 *)
Definition PreOsTaskJoinPostUnsafe
  (sg: StableGlobVars)
  (tskabs tskabs_join : TaskAbstractState) : Assertion := 
  EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs) ** 
  EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs_join).

Definition PostOsTaskJoinPostUnsafe
  (sg: StableGlobVars)
  (tskabs tskabs' tskabs_join tskabs_join' : TaskAbstractState) : Assertion := 
  match andb (joinable(tskabs.(taskFlag)))%bool (negb(List_empty (tJoinList tskabs)))%bool with
    | true => 
      match tskabs_join.(status) with
      | wait ws => 
        [| pend(ws) = false |] && 
        [| pend_time(ws) = None |] &&
        match negb(suspend(ws)) with
        | true => [| (tskabs_join'.(status)) = ready 0 |]
        | false => emp
        end
      | ready _ => [| False |]
      | _ => [| (tskabs_join'.(status)) = ready 0 |]
      end &&
      EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs) **
      EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs_join')
    | false => 
      EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs) ** 
      EX __0, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ tskabs_join)
  end.

(********************************************************************)
(* LITE_OS_SEC_TEXT_INIT STATIC_INLINE VOID OsRunningTaskDelete(UINT32 taskID, LosTaskCB *taskCB)
{
    LOS_ListTailInsert(&g_taskRecycleList, &taskCB->pendList); // 将制定taskCB的pendlist加入g_taskRecycleList
    g_losTask.runTask = &g_taskCBArray[g_taskMaxNum];
    g_losTask.runTask->taskID = taskID;
    g_losTask.runTask->taskStatus = taskCB->taskStatus | OS_TASK_STATUS_RUNNING;
    g_losTask.runTask->topOfStack = taskCB->topOfStack;
    g_losTask.runTask->taskName = taskCB->taskName;
} *)

(* OsRunningTaskDelete Pre_Post *)
Definition PreOsRunningTaskDelete
  (sg: StableGlobVars)
  (tskabs runtskabs: TaskAbstractState)
  (st : TcbGlobalState)
  (tskRecycleList : list TaskID)
  (taskID run_id : TaskID) : Assertion := 
  g_taskRecycleList_store sg tskRecycleList **
  EX __, used_complete_task sg (__ + taskID * sizeOfTaskCB) taskID tskabs ** 
  EX __, used_complete_task sg (__ + run_id * sizeOfTaskCB) run_id runtskabs.

Definition PostOsRunningTaskDelete
  (sg: StableGlobVars)
  (st : TcbGlobalState)
  (tskabs runtskabs runtskabs' : TaskAbstractState)
  (tskRecycleList tskRecycleList' : list TaskID)
  (taskID run_id run_id': TaskID) : Assertion := 
  [| run_id' = taskID |] &&
  [| tskRecycleList' = cons taskID tskRecycleList |] &&
  [| runtskabs'.(status) = running /\ tTopOfStack runtskabs' = tTopOfStack tskabs /\ tTaskName runtskabs' = tTaskName tskabs |] &&
  g_taskRecycleList_store sg tskRecycleList' ** 
  EX __, used_complete_task sg (__ + run_id' * sizeOfTaskCB) run_id' runtskabs'.

(********************************************************************)
(* LITE_OS_SEC_TEXT UINT32 LOS_CurTaskIDGet(VOID)
{
    if (g_losTask.runTask == NULL) {
        return LOS_ERRNO_TSK_ID_INVALID;
    }
    return g_losTask.runTask->taskID;
} *)

(* LOS_CurTaskIDGet Pre_Post *)
Definition PreLOS_CurTaskIDGet 
  (sg: StableGlobVars) : Assertion := 
  EX __0, (EX __1, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ __1)).

Definition PostLOS_CurTaskIDGet
  (sg: StableGlobVars) : Assertion := 
  EX __0, (EX __1, (EX __, used_complete_task sg (__0 + __ * sizeOfTaskCB) __ __1)).
