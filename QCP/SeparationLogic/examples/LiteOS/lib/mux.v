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

Module Mux.

(* Definition MuxID: Type := Z.

Record MuxAbstractState :=  {
  muxCount: Z;  (* 锁被持有的次数 *)
  muxList: list TaskID;  (* 等待写入的任务列表 *)
  owner: addr; (* 执行任务控制块的指针 *)
  priority: Z; (* 优先级 *)
}.

Record Glob_MuxAbstractState: Type := {
  inUsedMuxStates: MuxID -> option MuxAbstractState;
  (* 所有互斥锁的高层状态表示为从muxID到互斥锁抽象状态的映射 *)
  (* Option表示可选的互斥锁状态，创建时被设置为Some，删除时被设置为none *)
  unUsedMuxStates: list MuxID
}. *)

Definition used_complete_mux
             (sg: StableGlobVars)
             (ctrl_start: addr)
             (muxID: MuxID)
             (s: MuxAbstractState): Assertion :=
  (* 控制块信息，假设互斥锁存储在ctrl_start开始的连续地址中 *)
  &(ctrl_start # "LosMuxCB" ->ₛ "muxStat") # Int |-> 1 **
  &(ctrl_start # "LosMuxCB" ->ₛ "muxCount") # Int |-> s.(muxCount) **
  &(ctrl_start # "LosMuxCB" ->ₛ "muxID") # Int |-> muxID **
  &(ctrl_start # "LosMuxCB" ->ₛ "owner") # Ptr |-> s.(owner) **
  &(ctrl_start # "LosMuxCB" ->ₛ "priority") # Int |-> s.(priority) **
  (* 等待互斥锁的任务列表起始地址 *)
  store_pend_list_dll sg (&(ctrl_start # "LosMuxCB" ->ₛ "muxList")) s.(muxList).
  (* pend_list任务的循环双链表已经定义了*)

Definition unused_complete_mux
             (ctrl_start: addr)
             (muxID: MuxID): Assertion :=
    (* 控制块信息，假设存储在ctrl_start开始的连续地址中 *)
  &(ctrl_start # "LosMuxCB" ->ₛ "muxStat") # Int |-> 0 **
  (EX __, &(ctrl_start # "LosMuxCB" ->ₛ "muxCount") # Int |-> __) **
  &(ctrl_start # "LosMuxCB" ->ₛ "muxID") # Int |-> muxID **
  (EX __, &(ctrl_start # "LosMuxCB" ->ₛ "owner") # Ptr |-> __) **
  (EX __, &(ctrl_start # "LosMuxCB" ->ₛ "priority") # Int |-> __). 




Definition store_used_mux_map
             (sg: StableGlobVars)
             (m: MuxID -> option MuxAbstractState): Assertion :=
  store_map
    (fun muxID s =>
      used_complete_mux sg (sg.(g_allMux) + sizeof("LosMuxCB") * muxID) muxID s)
    m.

Definition store_free_mux_list
             (sg: StableGlobVars)
             (l: list MuxID): Assertion :=
  EX l0: list (DL_Node MuxID),
    [| map DLL.data l0 = l |] &&
    store_dll
      (fun p muxID =>
         EX ctrl_start: addr,
           [| ctrl_start = sg.(g_allMux) + sizeof("LosMuxCB") * muxID |] &&
           [| p = &(ctrl_start # "LosMuxCB" ->ₛ "muxList") |] &&
           unused_complete_mux ctrl_start muxID)
      (&("g_unusedMuxList")) l0.

Definition store_glob_mux (sg: StableGlobVars) (s: Glob_MuxAbstractState): Assertion :=
  store_used_mux_map sg s.(inUsedMuxStates) **
  store_free_mux_list sg s.(unUsedMuxStates).



(*似乎没有把semlist连起来，试着改写了一下*)
(* Definition  GET_MUX_LIST (ptr: addr) : addr:=
    ptr-12.


Definition unused_complete_mux1
             (ptr: addr)
             (muxID: muxID): Assertion :=
    let mux_addr := ptr - 12 in
    (* 控制块信息，假设存储在ctrl_start开始的连续地址中 *)
  [| ptr = &(("g_allMux"+ muxID) ->ₛ "muxList") |] && 
  &(mux_addr # "LosMuxCB" ->ₛ "muxStat") # Int |-> 0 **
  (EX __, &(mux_addr # "LosMuxCB" ->ₛ "muxCount") # Int |-> __) **
  &(mux_addr # "LosMuxCB" ->ₛ "muxID") # Int |-> muxID **
  (EX __, &(mux_addr # "LosMuxCB" ->ₛ "owner") # Ptr |-> __) **
  (EX __, &(mux_addr # "LosMuxCB" ->ₛ "priority") # Int |-> __). 

Definition store_free_sem_list1 (l: list muxID): Assertion :=
  EX l0: list (DL_Node muxID),
    [| map (DLL.data _) l0 = l |] &&
    store_dll unused_complete_mux1 (&("g_unusedMuxList")) l0. *)



    (* 
Definition store_single_sem_aux (ele: muxID * SemAbstractState): Assertion :=
  let (semID, s) := ele in
  used_complete_sem (("g_taskCBArray" + taskID))
    


Definition store_used_sem_list (m: muxID -> option SemAbstractState): Assertion :=
  EX l: list (muxID * SemAbstractState),
    [| forall semID s, m semID = Some s <-> In (semID, s) l |] &&
    iter_sepcon (map (fun ele => let (semID, s) := ele in used_complete_sem )
*)
End Mux.


(* Inductive mux_ret: Type :=
    | LOS_ERRNO_MUX_NO_MEMORY
    | LOS_ERRNO_MUX_INVALID
    | LOS_ERRNO_MUX_PTR_NULL
    | LOS_ERRNO_MUX_ALL_BUSY
    | LOS_ERRNO_MUX_UNAVAILABLE
    | LOS_ERRNO_MUX_PEND_INTERR
    | LOS_ERRNO_MUX_PEND_IN_LOCK
    | LOS_ERRNO_MUX_TIMEOUT
    | LOS_ERRNO_MUX_PENDED
    | LOS_OK. *)


