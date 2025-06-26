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
Require Import LOS_Verify.lib.Los_Rules_lib.
Import TaskStateDef.
Local Open Scope sac.
Require Import LOS_Verify.lib.dll.
Require Import LOS_Verify.lib.sortlink.

Require Import LOS_Verify.lib.task.
Require Import LOS_Verify.lib.event.

Parameter event_inv : StableGlobVars -> EventAbstractState -> Assertion.

Require Import LOS_Verify.lib.membox.

Parameter membox_inv : StableGlobVars -> MemboxAbstractState -> Assertion.

Require Import LOS_Verify.lib.mux.

Parameter mux_inv : StableGlobVars -> Glob_MuxAbstractState -> Assertion.

Require Import LOS_Verify.lib.queue.

Parameter queue_inv : StableGlobVars -> Glob_QueueAbstractState -> Assertion.

Require Import LOS_Verify.lib.sched.

Parameter sched_inv : StableGlobVars -> SchedAbstractState -> Assertion.

Require Import LOS_Verify.lib.swtmr_port.
Require Import LOS_Verify.lib.tick.

Parameter tick_inv : StableGlobVars -> TickAbstractState -> Assertion.

Require Import LOS_Verify.lib.sem.

Parameter sem_inv : StableGlobVars -> Glob_SemAbstractState -> Assertion.

Definition LOS_Verify_inv (sg : StableGlobVars) (s: Los_Verify_State) : Assertion := 
  task_inv sg (s.(TskState)) ** 
  event_inv sg (s.(EvtState)) ** 
  mux_inv sg (s.(MuxState)) ** 
  sem_inv sg (s.(SemState)) ** 
  queue_inv sg (s.(QueueState)) **
  tick_inv sg (s.(TickState)) ** 
  membox_inv sg (s.(MemboxState)) ** 
  swtmr_inv sg s.
