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
Require Import compcert.lib.Zbits.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Local Open Scope sac.
Require Import LOS_Verify.lib.dll.
Export DLL.

(* Definition maxEventNum : Z := 32. 
Definition EventID := Z. *)

Module Event.

	(* Definition EventIDList := list EventID.  (* 事件列表，简化为自然数列表表示事件ID *)
	Definition EventMask := list EventID.  事件掩码对应的事件ID列表，简化为自然数列表表示事件ID *)

	(*
	Fixpoint conj2 (a:list Z) (b:list Z)(c:list Z)(d:list Z):Prop:=
		match a with
		| nil => c=d
		| x::l0 => 
			((In x b)->(conj2 l0 b c (x::d)))/\((~(In x b))->(conj2 l0 b c d))
		end.
	
	Definition conj (a:list Z) (b:list Z)(c:list Z):Prop:=
		conj2 a b c nil.
	*)

	(* Inductive EventMode : Type := (* 读取模式 *)
	| LOS_WAITMODE_AND
	| LOS_WAITMODE_OR.

	Definition ClearMode := bool. (*清除模式，是否在读取后清除*)

	Record EventReadAbstractState := mkEventReadAbstractState {
		eventMask : EventMask;
		eventMode : EventMode;
		clearMode : ClearMode;
	}.
	Record EventWriteAbstractState := mkEventWriteAbstractState {
		eventIDList : EventIDList;
		eventTaskList : list TaskID;
	}. *)
	
	Notation "x '.(eventMask)'" := (eventMask x) (at level 1).
	Notation "x '.(eventMode)'" := (eventMode x) (at level 1).
	Notation "x '.(clearMode)'" := (clearMode x) (at level 1).
	Notation "x '.(eventIDList)'" := (eventIDList x) (at level 1).
	Notation "x '.(eventTaskList)'" := (eventTaskList x) (at level 1).

	Definition checkEventID (uwEventID:Z) (eventIDList: EventIDList): Prop:=
		(powerserie eventIDList)=uwEventID.

	
	Definition checkEventMode(x:Z)(eventMode:EventMode)(clearMode:ClearMode):Prop:=
		let a:= (if eventMode then 4 else 2) in
		let b:= (if clearMode then 1 else 0) in
		x=a+b.
	Definition isEventMode(x:Z):Prop:=
		x=5/\x=4/\x=3/\x=2.
	Definition notEventMode(x:Z):Prop:=
		(Z.land x 6=0)\/(Z.land x 2<>0/\Z.land x 4<>0)\/(Z.land x  (Z.lnot 7)<>0).
	Definition notEventModeb(x:Z):bool:=
		(Z.eqb (Z.land x 6) 0)||(negb (Z.eqb (Z.land x 2) 0)&&negb (Z.eqb (Z.land x 4) 0))||negb (Z.eqb (Z.land x (unsigned_last_nbits (Z.lnot 7) 32))0).
	(*x=5/\x=4/\x=3/\x=2*)
	Definition checkEventSatisfied(ers:EventReadAbstractState)(ews:EventWriteAbstractState):Prop:=
		match ers.(eventMode) with
		| LOS_WAITMODE_AND => (forall i:EventID, List.In i ers.(eventMask) ->List.In i ews.(eventIDList))
		| LOS_WAITMODE_OR  => (exists i:EventID, List.In i ers.(eventMask)/\List.In i ews.(eventIDList))
		end.
	Definition checkEventReadParam (eventCB:addr)(x y:Z)(l:list Z)(mode:Z):Z:=
		match eventCB with
		| 0 => 33561606
		| _ => 
		match x,y with
		| 0,_ => 33561607
		| _,0 => 33561607
		| _,_ =>
		match l with
		| nil => 33561602
		| _ => 
		if in_dec Z.eq_dec 25 l
		then 33561600
		else if notEventModeb mode
		then 33561604
		else 0
		end
		end
		end.
	Definition OsEvent_store_pendList (g_taskCBArray: addr) (x: addr) (l: list TaskID): Assertion :=
		EX l0: list (DL_Node TaskID),
			[| map DLL.data l0 = l |] &&
			store_dll
			(fun p (taskID: TaskID) =>
				[| p = &((g_taskCBArray # "LosTaskCB" + taskID) ->ₛ "pendList") |] 
				&& emp)
			x l0.
			
	Definition complete_eventWriteCB (g_taskCBArray: addr)(ctrl_start: addr) (ews:EventWriteAbstractState) : Assertion :=
		EX (uwEventID: Z),
		[|checkEventID uwEventID ews.(eventIDList)|]&&
		(&(ctrl_start # "tagEvent" ->ₛ "uwEventID")# UInt |-> uwEventID)**
		(OsEvent_store_pendList g_taskCBArray &(ctrl_start # "tagEvent" ->ₛ "stEventList") ews.(eventTaskList)).

	Definition complete_eventReadCB (ctrl_start: addr) (ers:EventReadAbstractState) : Assertion :=
		EX (eventMask: Z)(eventMode: Z),
		[|checkEventID eventMask ers.(eventMask)|]&&
		[|checkEventMode eventMode ers.(eventMode) ers.(clearMode)|]&&
		(&(ctrl_start # "LosTaskCB" ->ₛ "eventMask")# UInt |-> eventMask)**
		(&(ctrl_start # "LosTaskCB" ->ₛ "eventMode")# UInt |-> eventMode)
		.
	
	
End Event.


