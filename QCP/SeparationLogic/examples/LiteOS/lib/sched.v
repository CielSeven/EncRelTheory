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
Import ListNotations.
Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Local Open Scope sac.
Local Open Scope string.
Local Open Scope list.
Require Import LOS_Verify.lib.task.
Require Import LOS_Verify.lib.glob_vars_and_defs.
Require Import LOS_Verify.lib.dll.
Require Import LOS_Verify.lib.sortlink.
Import SDLL.

Definition g_priQueueList_store (g_priQueueList: addr) (sg: StableGlobVars) (priQueueList: list (list TaskID)) : Assertion :=
    store_array (fun x lo a => (store_pend_list_dll sg (x + lo * sizeof("LOS_DL_LIST")) a)) g_priQueueList 32 priQueueList.

Definition g_priQueueList_prop (priQueueList : list (list TaskID)) (queueBitmap : Z) : Prop :=
    forall prio, 0 <= prio < 32  ->
         (Z.land queueBitmap (Z.shiftr 2147483648 prio) = 0) <->
        (Znth prio priQueueList [] = []).
(* 2147483648 = 2^31 对应的 32 位二进制数为 [1,0,...,0] *)
(* (Z.shiftr 2147483648 prio): 将 32 位二进制数 [1,0,...,0] 右移 prio 位 *)

Definition g_queueBitmap_store (queueBitmap: Z): Assertion :=
    &("g_queueBitmap") # UInt |-> queueBitmap.

Definition g_priQueueList_valid (g_priQueueList: addr) (sg: StableGlobVars) (priQueueList: list (list TaskID)) (queueBitmap: Z)  : Assertion :=
    (g_priQueueList_store g_priQueueList sg priQueueList) ** (g_queueBitmap_store queueBitmap) && [| g_priQueueList_prop priQueueList queueBitmap |]. 

(* g_taskSortLinkList 表示谓词: sortlink.v - store_task_sorted_dll *)





(*
Record SchedGlobalState := mkSchedGlobalState {
    taskScheduled : bool;
    taskSortLinkList : list TaskID;      (* iff task is pendtime / delay   *)
    priQueueList : list (list TaskID);   (*  priQueueList i stores the list of all ready task with prio = i  *)
    queueBitmap: Z;  
}.

Definition vaild_priQueueList (priQueueList: Z -> option (list TaskID)) 
                              (usedTask : TaskID -> option TaskAbstractState): Prop :=
        forall i tid, ( exists l, (priQueueList i = Some l) /\ (In tid l) ) <->
                      ( exists t, usedTask tid = Some t /\ t.(tPrio) = i ).

Fixpoint queueBit_to_int (queueBitmap: list Z) (power: Z) := 
    match queueBitmap with 
    | nil => 0
    | a :: queueBitmap' => a * power + (queueBit_to_int queueBitmap' (power * 2))
    end.

Definition valid_queueBitmap (priQueueList: list (list TaskID)) (queueBitmap: list Z) : Prop :=
    forall i : Z, (0 <= i < 32) -> ( 
          (  nth (Z.to_nat i) queueBitmap 0 = 0 \/ (nth (Z.to_nat i) queueBitmap 0 = 1 ) ) /\ 
        
          ( (nth (Z.to_nat i) queueBitmap 0 = 0 ) <-> (nth (Z.to_nat i) priQueueList nil = nil)  )
        ).
*)