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

Module Sem.

(* Definition SemID: Type := Z.

Definition semMaxNum:=6.

Record SemAbstractState :=  {
  semCount: Z;  (* 表示可用信号量的个数 *)
  maxSemCount: Z;  (* 表示可用信号量的最大容量 *)
  semList: list TaskID;  (* 等待写入的任务列表 *)
}. *)

(* Record Glob_SemAbstractState: Type := {
  inUsedSemStates: SemID -> option SemAbstractState;
  (* 所有消息队列的高层状态表示为从队列ID到队列状态的映射 *)
  (* Option表示可选的信号量状态，创建时被设置为Some，删除时被设置为none *)
  unUsedSemStates: list SemID
}. *)

Definition unused_sem_in_range (st:Glob_SemAbstractState): Prop := 
  Forall (fun semID => 0<=semID<semMaxNum) st.(unUsedSemStates).

Definition used_sem_in_range (st:Glob_SemAbstractState): Prop :=
  forall semID:SemID, 
  match st.(inUsedSemStates) semID with
    | Some _ => 0<=semID<semMaxNum
    | None => True
  end.

Definition check_sem_list (st:Glob_SemAbstractState): Prop :=
  forall semID:SemID,
  0<=semID<semMaxNum ->
  ((In semID st.(unUsedSemStates) /\ st.(inUsedSemStates) semID = None)\/
  (~ In semID st.(unUsedSemStates)  /\ exists b:SemAbstractState,st.(inUsedSemStates) semID = Some b)).

Definition valid_GlobSemAbstractState (st:Glob_SemAbstractState): Prop := 
  unused_sem_in_range st /\ used_sem_in_range st /\ check_sem_list st.

Definition used_complete_sem
             (sg: StableGlobVars)
             (ctrl_start: addr)
             (semID: SemID)
             (s: SemAbstractState): Assertion :=
  (* 控制块信息，假设互斥锁存储在ctrl_start开始的连续地址中 *)
  &(ctrl_start # "LosSemCB" ->ₛ "semStat") # UShort |-> 1 **
  &(ctrl_start # "LosSemCB" ->ₛ "semCount") # UShort |-> s.(semCount) **
  &(ctrl_start # "LosSemCB" ->ₛ "maxSemCount") # UShort |-> s.(maxSemCount) **
  &(ctrl_start # "LosSemCB" ->ₛ "semID") # UShort |-> semID **
  (* 等待信号量的任务列表起始地址 *)
  store_pend_list_dll sg (&(ctrl_start # "LosSemCB" ->ₛ "semList")) s.(semList).
  (* pend_list任务的循环双链表已经定义了*)

Definition unused_complete_sem
             (ctrl_start: addr)
             (semID: SemID): Assertion :=
    (* 控制块信息，假设存储在ctrl_start开始的连续地址中 *)
  &(ctrl_start # "LosSemCB" ->ₛ "semStat") # UShort |-> 0 **
  (EX __, &(ctrl_start # "LosSemCB" ->ₛ "semCount") # UShort |-> __) **
  &(ctrl_start # "LosSemCB" ->ₛ "semID") # UShort |-> semID **
  (EX __, &(ctrl_start # "LosSemCB" ->ₛ "maxSemCount") # UShort |-> __).

Definition store_used_sem_map
             (sg: StableGlobVars)
             (m: SemID -> option SemAbstractState): Assertion :=
  store_map
    (fun semID s =>
      used_complete_sem sg (sg.(g_allSem) + sizeof("LosSemCB") * semID) semID s)
    m.

Definition store_used_sem_map_missing_i
              (sg: StableGlobVars)
              (m: SemID -> option SemAbstractState)
              (missingID:SemID): Assertion :=
  store_map_missing_i
  (fun semID s =>
  used_complete_sem sg (sg.(g_allSem) + sizeof("LosSemCB") * semID) semID s)
    m missingID.

Definition store_free_sem_list
             (sg: StableGlobVars)
             (l: list SemID): Assertion :=
  EX l0: list (DL_Node SemID),
    [| map DLL.data l0 = l |] &&
    store_dll
      (fun p semID =>
         EX ctrl_start: addr,
           [| ctrl_start = sg.(g_allSem) + sizeof("LosSemCB") * semID |] &&
           [| p = &(ctrl_start # "LosSemCB" ->ₛ "semList") |] &&
           unused_complete_sem ctrl_start semID)
      (&("g_unusedSemList")) l0.


Definition store_free_sem_list_seg
              (sg: StableGlobVars)
              (x px y py: addr)
              (l: list SemID): Assertion :=
  EX l0: list (DL_Node SemID),
    [| map DLL.data l0 = l |] &&
    dllseg 
      (fun p semID =>
        EX ctrl_start: addr,
          [| ctrl_start = sg.(g_allSem) + sizeof("LosSemCB") * semID |] &&
          [| p = &(ctrl_start # "LosSemCB" ->ₛ "semList") |] &&
          unused_complete_sem ctrl_start semID)
      x px y py l0.


Definition store_glob_sem (sg: StableGlobVars) (s: Glob_SemAbstractState): Assertion :=
  store_used_sem_map sg s.(inUsedSemStates) **
  store_free_sem_list sg s.(unUsedSemStates).
  
(* Definition  GET_SEM_LIST(ptr: addr) :=
    ptr-8
. *)


(* Definition unused_complete_sem1
             (ptr: addr)
             (semID: SemID): Assertion :=
    let sem_addr := ptr - 8 in
    (* 控制块信息，假设存储在ctrl_start开始的连续地址中 *)
  [| ptr = &(("g_allSem"+ semID) ->ₛ "semList") |] && 
  &(sem_addr # "LosSemCB" ->ₛ "semStat") # Int |-> 0 **
  (EX __, &(sem_addr # "LosSemCB" ->ₛ "semCount") # Int |-> __) **
  &(sem_addr # "LosSemCB" ->ₛ "semID") # Int |-> semID **
  (EX __, &(sem_addr # "LosSemCB" ->ₛ "maxSemCount") # Int |-> __).


Definition store_free_sem_list1 (l: list SemID): Assertion :=
  EX l0: list (DL_Node SemID),
    [| map (DLL.data _) l0 = l |] &&
    store_dll unused_complete_sem1 (&("g_unusedSemList")) l0. *)


    (* 
Definition store_single_sem_aux (ele: SemID * SemAbstractState): Assertion :=
  let (semID, s) := ele in
  used_complete_sem (("g_taskCBArray" + taskID))
    


Definition store_used_sem_list (m: SemID -> option SemAbstractState): Assertion :=
  EX l: list (SemID * SemAbstractState),
    [| forall semID s, m semID = Some s <-> In (semID, s) l |] &&
    iter_sepcon (map (fun ele => let (semID, s) := ele in used_complete_sem )
*)

(* Inductive sem_addr_ret: Type :=
    | LOS_ERRNO_SEM_NO_MEMORY
    | LOS_ERRNO_SEM_INVALID
    | LOS_ERRNO_SEM_PTR_NULL
    | LOS_ERRNO_SEM_ALL_BUSY
    | LOS_ERRNO_SEM_UNAVAILABLE
    | LOS_ERRNO_SEM_PEND_INTERR
    | LOS_ERRNO_SEM_PEND_IN_LOCK
    | LOS_ERRNO_SEM_TIMEOUT
    | LOS_ERRNO_SEM_PENDED
    | LOS_OK. *)

Module OsSemInit.


Definition Post
                (sg: StableGlobVars) (l: list SemID): Assertion :=
                store_free_sem_list sg l.

End OsSemInit. 
    
(* Definition PostOsSemInit (base: addr) (st: Glob_SemAbstractState) (result : mux_ret) : Assertion :=
    [| result = LOS_OK |] && 
    (let l := reverseRange (range (Z.to_nat maxQueueNum)) in
       [| list_Z_eq l (gfreeList st) |] && 
       [| mapallnone l st|] && 
       globalLayout base st).  *)

End Sem.

