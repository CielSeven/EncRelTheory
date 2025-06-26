Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
Require Import SL.ConAssertion SL.CriticalSTS SL.NestedCriticalSTS.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Local Open Scope stmonad.

Require Export LOS_Verify.lib.glob_vars_and_defs.
Require Export LOS_Verify.lib.Los_Verify_State_def.
Import TaskStateDef.

Definition Los_CS_C : critical_STS := {|
  critical_STS_state := StableGlobVars * Los_Verify_State;
  critical_STS_transition := fun s1 s2 => fst s1 = fst s2
|}.

Definition Los_CS_Abs : critical_STS := {|
  critical_STS_state := Los_Verify_State;
  critical_STS_transition := fun _ _ => 1 = 1
|}.

Module C_STS_Los <: critical_STS_def.
  Definition c_sts: critical_STS := Los_CS_C.
End C_STS_Los.

Module Los_C_Rules <: SeparationLogicSig.
  Include C_STS_Los.
  Include critical_STS_to_STS_def.
  Include ConAssertion.CSL.
  Include DerivedPredSig.
  Include StoreLibSig.
  Include ArrayLibSig.
  Include CriticalCSL.
End Los_C_Rules.

Module C_STS_Los_Abs <: critical_STS_def.
  Definition c_sts: critical_STS := Los_CS_Abs.
End C_STS_Los_Abs.

Module STS_Los_Abs.
  Include C_STS_Los_Abs.
  Include critical_STS_to_STS_def.
End STS_Los_Abs.

Export Los_C_Rules.

Local Open Scope sac.

(* Basic definition for AbsState *)

Definition InsideCritical p l: Assertion :=
  Los_C_Rules.InsideCritical (p, l).

Definition OutsideCritical p l: Assertion :=
  Los_C_Rules.OutsideCritical (p, l).

Definition RTrans_C p1 l1 p2 l2 : Prop :=
  Los_C_Rules.RTrans (p1, l1) (p2, l2).

Definition GTrans_C p1 l1 p2 l2 : Prop :=
  Los_C_Rules.GTrans (p1, l1) (p2, l2).

Definition RTrans_Abs l1 l2 : Prop :=
  STS_Los_Abs.RTrans l1 l2.

Definition GTrans_Abs l1 l2 : Prop :=
  STS_Los_Abs.GTrans l1 l2.

Definition atomic_cmd {A} (c: program (Los_Verify_State) A): program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c l1 a l2 /\
    X2 == (RTrans_Abs l2).

Definition LastSeen (s : Los_Verify_State) : (Los_Verify_State -> Prop) -> Prop :=
  fun B => RTrans_Abs s == B.

(* Definition for Task AbsState *)

Definition atomic_tsk_cmd {A} (c : program (TcbGlobalState) A) : program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (l1.(TskState)) a (l2.(TskState)) /\
    l1 = replace_tskS l1.(TskState) l2 /\
    X2 == (RTrans_Abs l2).

(* Definition for event AbsState *)

Definition atomic_evt_cmd {A} (c : program (EventAbstractState) A) : program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (l1.(EvtState)) a (l2.(EvtState)) /\
    l1 = replace_evtS l1.(EvtState) l2 /\
    X2 == (RTrans_Abs l2).

(* Definition for membox AbsState *)

Definition atomic_membox_cmd {A} (c : program (MemboxAbstractState) A) : program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (l1.(MemboxState)) a (l2.(MemboxState)) /\
    l1 = replace_memboxS l1.(MemboxState) l2 /\
    X2 == (RTrans_Abs l2).

(* Definition for queue AbsState *)

Definition atomic_queue_cmd {A} (c : program (Glob_QueueAbstractState) A) : program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (l1.(QueueState)) a (l2.(QueueState)) /\
    l1 = replace_queueS l1.(QueueState) l2 /\
    X2 == (RTrans_Abs l2).

(* Definition for sem AbsState *)

Definition atomic_sem_cmd {A} (c : program (Glob_SemAbstractState) A) : program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (l1.(SemState)) a (l2.(SemState)) /\
    l1 = replace_semS l1.(SemState) l2 /\
    X2 == (RTrans_Abs l2).

(* Definition for mutex AbsState *)

Definition atomic_mutex_cmd {A} (c : program (Glob_MuxAbstractState) A) : program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (l1.(MuxState)) a (l2.(MuxState)) /\
    l1 = replace_muxS l1.(MuxState) l2 /\
    X2 == (RTrans_Abs l2).

(* Definition for tick AbsState *)

Definition atomic_tick_cmd {A} (c : program (TickAbstractState) A) : program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (l1.(TickState)) a (l2.(TickState)) /\
    l1 = replace_tickS l1.(TickState) l2 /\
    X2 == (RTrans_Abs l2).

(* Definition for sched AbsState *)

Definition atomic_sched_cmd {A} (c : program (SchedAbstractState) A) : program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (l1.(SchedState)) a (l2.(SchedState)) /\
    l1 = replace_schedS l1.(SchedState) l2 /\
    X2 == (RTrans_Abs l2).

(* Definition for swtmr AbsState *)

Definition atomic_swtmr_cmd {A} (c : program (Glob_SWTMRAbstractState) A) : program (Los_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (l1.(SwtmrState)) a (l2.(SwtmrState)) /\
    l1 = replace_swtmrS l1.(SwtmrState) l2 /\
    X2 == (RTrans_Abs l2).
