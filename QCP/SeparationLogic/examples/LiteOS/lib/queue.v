(* /**
 * @ingroup queue
 */
typedef struct {
    UINT8 *queue;      /**< Pointer to a queue handle */
    UINT16 queueState; /**< Queue state */
    UINT16 queueLen;   /**< Queue length */
    UINT16 queueSize;  /**< Node size */
    UINT16 queueID;    /**< queueID */
    UINT16 queueHead;  /**< Node head */
    UINT16 queueTail;  /**< Node tail */
    UINT16 readWriteableCnt[OS_READWRITE_LEN]; /**< Count of readable or writable resources, 0:readable, 1:writable */
    LOS_DL_LIST readWriteList[OS_READWRITE_LEN]; /**< Pointer to the linked list to be read or written,
                                                      0:readlist, 1:writelist */
    LOS_DL_LIST memList; /**< Pointer to the memory linked list */
} LosQueueCB;
*)

(* 2. 高层状态表示：抽象状态 *)
(* Require Import abstsortlink.
Require Import abstqueue. *)
Require Import dll.
Require Import glob_vars_and_defs.
Require Import Coq.Structures.OrderedTypeEx. (* Z_as_OT, NAT_as_OT *)
(* Require Import Coq.FSets.FMapFacts. 库SimpleC.SL中也定义了 [| P |] *)
(* Require Import PeanoNat. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List. (* List.In *)
(* Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms. *)
(* Require Import Coq.micromega.Psatz. *)
(* Require Import Permutation. *)
(* From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap. *)
Require Import SetsClass.SetsClass. 
(* Import SetsNotation. *)
From SimpleC.SL Require Import Mem SeparationLogic.
Local Open Scope Z_scope.
Local Open Scope sets. (* sets_scope: sets/: SetsProd.v, SetsClass.v, SetsDomain.v *)
Require Import String.
Local Open Scope string.
Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Local Open Scope sac.
Require Import LOS_Verify.lib.dll.

Definition sizeOfInt : Z := 8.
Definition sizeOfPtr : Z := 8.
Definition maxQueueNum : Z := 32. 
Definition sizeOfQueueCTB : Z := 128.
Definition maxMsgSize : Z := 128.


Module abstqueue.
    (* Definition QID := Z.  (* 队列ID *)
    Definition QSize := Z.  (* 节点大小 *)
    Definition MsgContent := list Z.
    Definition QueueContent := list MsgContent.  (* 队列内容，假设为值的列表 *)

    Record QueueAbstractState := mkQueueAbstractState {
        qSize : QSize;  (* 节点大小 *)
        qContent : QueueContent;  (* 队列内容 *)
        qReadList : list TaskID;  (* 等待读取的任务列表 *)
        qWriteList : list TaskID;  (* 等待写入的任务列表 *)
    }. *)

      (* 所有消息队列的高层状态表示为从队列ID到队列状态的映射，映射*)
    (* Definition QueueMap := QID -> option QueueAbstractState. 
    (*Module Import M := FMapAVL.Make(Z_as_OT).
    Definition QueueMap := M.t (option QueueAbstractState).*)
    (*QueueID -> option QueueAbstractState*)
    (* option表示可选的队列状态，创建时被设置为Some，删除时被设置为none *)


    Record Glob_QueueAbstractState := {
        gfreeList :  list QID; (* 空闲消息节点 list of QueueID*)
        qMap : QueueMap;
    }. *)

    (* 假设 addr 已经在某个地方定义了 *)
    
    (* 声明 sequence_maps_to 的存在，但暂不定义它。这里假设 sequence_maps_to 的类型为
   addr -> list Z -> Prop，意味着它是一个谓词，接受一个地址和一个整数列表，返回一个命题。 *)
    Parameter sequence_maps_to : addr -> Z -> list Z -> Assertion.
    (* 声明 sequence_maps_to_spaces 的存在，但暂不定义它 *)
    Parameter sequence_maps_to_spaces : addr -> Z -> Assertion.

    Definition single_space (array_head: addr)  (queueSize: QSize) : Assertion :=
        sequence_maps_to_spaces array_head queueSize.  (* 统一定义，计算并表示在内存中存储为空 *)

    (*单个消息的存储*)
    Definition single_msg (array_head: addr)  (queueSize: QSize) (msg: MsgContent) : Assertion :=
        [|Zlength msg = queueSize |] &&  (* 确保消息长度与queueSize一致 *)
        sequence_maps_to array_head queueSize msg.  (* 统一定义，计算并表示该消息在内存中的存储 *)

    Fixpoint queue_messages (array_head: addr) (queueSize: QSize)( queueLen: Z)
        (queueHead :Z) ( queueTail: Z) (msgs: list MsgContent) : Assertion :=
        match msgs with
            | nil => [|queueHead = queueTail|] && emp
            | msg :: rest =>
                (* 第一种情况：头指针未到达队列末尾 *)
                (* 第一种情况：头指针未到达队列末尾 *)
    ([|queueHead + 1< queueLen |] && single_msg (array_head + queueHead * queueSize) queueSize msg 
        ** queue_messages array_head queueSize queueLen (queueHead + 1) queueTail rest) ||
    (* 第二种情况：头指针到达队列末尾，需要回绕到开始 *)
    ([|queueHead + 1 = queueLen |] && single_msg (array_head + queueHead * queueSize) queueSize msg 
        ** queue_messages array_head queueSize queueLen 0 queueTail rest)
    end.


    Fixpoint queue_messages_spaces (array_head: addr) (queueSize :QSize)( queueLen: Z)
                               (queueHead queueTail: Z) (spaces: nat)  : Assertion :=
        match spaces with
    | O => [|queueHead = queueTail|] && emp
    | S spaces' =>
      (* 第一种情况：尾指针未到达队列末尾 *)
      ([|queueTail + 1 < queueLen|] && single_space (array_head + queueTail * queueSize) queueSize ** queue_messages_spaces array_head queueSize queueLen  queueHead (queueTail + 1) (spaces')) ||
      (* 第二种情况：尾指针到达队列末尾，需要回绕到开始 *)
      ([|queueTail + 1 = queueLen|] && single_space (array_head + queueTail * queueSize) queueSize ** queue_messages_spaces array_head queueSize queueLen  queueHead 0  (spaces'))
    end.

    Definition valid_queue  (queuest : QueueAbstractState) (*(qSize : Z) (qContent: list MsgContent)
                       (qReadTasks : list TaskID) (qWriteTasks : list TaskID) *)
        (qLen qHead qTail readCnt writeCnt : Z) : Prop :=
    (* 队列长度非负 *)
        readCnt = Zlength (qContent queuest) /\
        0 <= qLen /\
    (* 头尾指针在合法范围内 *)
        0 <= qHead < qLen /\ 0 <= qTail < qLen /\
    (* 可读写消息数量合法 *)
        0 <= readCnt <= qLen /\ 0 <= writeCnt <= qLen /\ readCnt + writeCnt <= qLen /\
    (* 等待读写的任务列表有效性 *)
        NoDup (qReadList queuest) /\ NoDup (qWriteList queuest). 


    Definition complete_queue  (sg: StableGlobVars)  (ctrl_start: addr) (qID : QID)(queuest : QueueAbstractState) : Assertion :=
    (*(qSize : Z)(qContent: list MsgContent) (qReadList : list TaskID) (qWriteList : list TaskID)*)
    EX (qLen qHead qTail readCnt writeCnt: Z),
        [|valid_queue queuest qLen qHead qTail readCnt writeCnt|] &&
    (* 控制块信息，假设存储在ctrl_start开始的连续地址中 *)
        &(ctrl_start # "LosQueueCB" ->ₛ "queueID") # Int |-> qID **
        &(ctrl_start # "LosQueueCB" ->ₛ "queueLen") # Int |-> qLen **
        &(ctrl_start # "LosQueueCB" ->ₛ "queueHead") # Int |-> qHead **
        &(ctrl_start # "LosQueueCB" ->ₛ "queueTail") # Int |-> qTail **
        (&(ctrl_start # "LosQueueCB" ->ₛ "readWriteableCnt") + 0 * sizeOfInt) # Int |-> readCnt **
        (&(ctrl_start # "LosQueueCB" ->ₛ "readWriteableCnt") + 1 * sizeOfInt) # Int |-> writeCnt **

    (* 等待读取的任务列表起始地址 *) (*直接就是地址*)
        store_pend_list_dll sg (&(ctrl_start # "LosQueueCB" ->ₛ "readWriteList") + 0 * sizeOfPtr) (qReadList queuest) **

    (* 等待写入的任务列表起始地址 *) (*直接就是地址*)
        store_pend_list_dll sg (&(ctrl_start # "LosQueueCB" ->ₛ "readWriteList") + 1 * sizeOfPtr) (qWriteList queuest) **
        

    (* 描述队列中消息的布局 *)
        EX msgs_start: addr, 
            &(ctrl_start # "LosQueueCB" ->ₛ "queue") # Ptr |-> msgs_start **
            queue_messages msgs_start (qSize queuest) qLen qHead qTail (qContent queuest) **
            queue_messages_spaces msgs_start (qSize queuest) qLen qHead qTail (Z.to_nat writeCnt).  

    Definition unused_queue (ctrl_start: addr) (qID : QID) : Assertion :=
    (*(qSize : Z)(qContent: list MsgContent) (qReadList : list TaskID) (qWriteList : list TaskID)*)
    &(ctrl_start # "LosQueueCB" ->ₛ "queueID") # Int |-> qID **
    EX __,  &(ctrl_start # "LosQueueCB" ->ₛ "queueLen") # Int |-> __ **
    EX __,  &(ctrl_start # "LosQueueCB" ->ₛ "queueHead") # Int |-> __ **
    EX __,  &(ctrl_start # "LosQueueCB" ->ₛ "queueTail") # Int |-> __ **
    EX __,  (&(ctrl_start # "LosQueueCB" ->ₛ "readWriteableCnt") + 0 * sizeOfInt) # Int |-> __ **
    EX __,  (&(ctrl_start # "LosQueueCB" ->ₛ "readWriteableCnt") + 1 * sizeOfInt) # Int |-> __ **

    (* 等待读取的任务列表起始地址 *) (*直接就是地址*)
    occupy_dll_node (&(ctrl_start # "LosQueueCB" ->ₛ "readWriteList") + 0 * sizeOfPtr) **

    (* 描述队列中消息的布局 *)
    EX __,  &(ctrl_start # "LosQueueCB" ->ₛ "queue") # Ptr |-> __ .  



Definition ValidGlobalState (st : Glob_QueueAbstractState): Prop :=
        forall id, (0 <= id < maxQueueNum)%Z -> 
        match (qMap st) id with
            | None => List.In id (gfreeList st)
            | Some _ => ~ List.In id (gfreeList st) (*不在gfreeList里面*)
end.

(*只需要串used部分*)


Definition allUsedQLayout
           (sg: StableGlobVars)
           (m: QID -> option QueueAbstractState) : Assertion :=
  store_map
    (fun queueID queue =>
       complete_queue sg
         (sg.(g_allQueue) + sizeof("LosQueueCB") * queueID) queueID queue)
    m.

Definition allUnUsedQLayout
             (sg: StableGlobVars)
             (l: list QID): Assertion :=
  EX l0: list (DL_Node QID),
    [| map DLL.data l0 = l |] &&
    store_dll
      (fun p queueID =>
         EX ctrl_start: addr,
           [| ctrl_start = sg.(g_allQueue) + sizeof("LosQueueCB") * queueID |] &&
           [| p = &(ctrl_start # "LosQueueCB" ->ₛ "readWriteList") + 1 * sizeOfPtr |] &&
           unused_queue ctrl_start queueID)
    &("g_freeQueueList") l0.

Definition globalLayout  (sg: StableGlobVars) (st: Glob_QueueAbstractState) : Assertion :=
  [| ValidGlobalState st |] && 
  allUsedQLayout sg st.(qMap) **
  allUnUsedQLayout sg st.(gfreeList).

End abstqueue.
