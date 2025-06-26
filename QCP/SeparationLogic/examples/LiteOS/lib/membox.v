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
Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Local Open Scope sac.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.

(* Module membox.
	Definition startAddr := addr. (* 内存池块起始地址 *)
  Definition uwBlkSize := Z.  (* 内存池块大小 *)
  Definition magicNum := Z. (* 内存块存储魔法字 *)

  Record FreeMemBoxNode : Type := mkFreeMemBoxNode{
        fnstartAddr : startAddr; (* 内存池块起始地址 *)
        fnuwBlkSize : uwBlkSize; (* 内存池块大小 *)
  }.

	Definition FreeList := list FreeMemBoxNode.  (* 未分配内存池块列表 *)

  Record AllocMemBoxNode : Type := mkAllocMemBoxNode{
        anstartAddr : startAddr; (* 内存池块起始地址 *)
        anuwBlkSize : uwBlkSize; (* 内存池块大小 *)
        anmagicNum : magicNum; (* 内存块存储魔法字 *)
  }.
  
  Definition AllocList := list AllocMemBoxNode. (* 已分配内存池块列表 *)


  Record MemBox : Type := mkMemBox{
        mstartAddr: startAddr; (* 内存池起始地址 *)
        muwBlkSize : uwBlkSize; (* 内存池块大小 *)
        mFreeList : FreeList; (* 未分配内存池块列表 *)
        mAllocList: AllocList; (* 已分配内存池块列表 *)
  }.

  Definition MemBoxList := list MemBox.

  Record MemboxAbstractState := mkMemboxAbstractState {
        mboxList : MemBoxList;  (* 内存池列表 *)
  }.

	Definition sizeof_Z := 4. 

End membox.

Import membox. *)

Definition completeFreeBlock (x: addr) (z: FreeMemBoxNode): Assertion :=
	[| z.(fnstartAddr) = x |] &&
	emp.

Fixpoint completeFreeBlockList (x: addr) (l: FreeList): Assertion :=
  match l with
    | nil      => [| x = NULL |] && emp
    | z :: l0 => completeFreeBlock x z &&
                       EX y: addr,
                      &(x # "LOS_MEMBOX_NODE" ->ₛ "pstNext") # Ptr |-> y ** 
                      completeFreeBlockList y l0
  end. 

Definition completeAllocBlock (z: AllocMemBoxNode): Assertion :=
	[| 0xa55a5a00 <= z.(anmagicNum) |] &&
	[| 0xa55a5aff >= z.(anmagicNum) |] &&
	EX y: addr,
	[| y = z.(anstartAddr) |] && 
	&( y # "LOS_MEMBOX_NODE" ->ₛ "pstNext") # Int |-> z.(anmagicNum).


Fixpoint completeAllocBlockList (l: list AllocMemBoxNode): Assertion :=
  match l with
    | nil     => emp
    | z :: l0 => completeAllocBlock z **
                 	completeAllocBlockList l0
  end.  
	
	Definition completeMembox (x: addr) (z: MemBox) : Assertion :=
		[| z.(muwBlkSize) mod sizeof_Z = 0 |] &&  [| z.(mstartAddr) = x |] &&
		EX x1: addr, 
		completeFreeBlockList x1 z.(mFreeList) **
		completeAllocBlockList z.(mAllocList) **
		&(x # "LOS_MEMBOX_INFO" ->ₛ "stFreeList") # Ptr |-> x1 **
		&(x # "LOS_MEMBOX_INFO" ->ₛ "uwBlkSize") # Int |-> z.(muwBlkSize) ** 
		&(x # "LOS_MEMBOX_INFO" ->ₛ "uwBlkNum") # Int |-> Z.of_nat ((List.length z.(mAllocList)) + (List.length z.(mFreeList))) **
		&(x # "LOS_MEMBOX_INFO" ->ₛ "uwBlkCnt") # Int |-> Z.of_nat (List.length z.(mAllocList)).
	
	Fixpoint completeMemboxList (x: addr) (l: MemBoxList): Assertion :=
		match l with
			| nil     => [| x = NULL |] && emp
			| z :: l0 => [| z.(muwBlkSize) mod sizeof_Z = 0 |] &&  [| z.(mstartAddr) = x |] &&
										EX x0: addr,
										completeMemboxList x0 l0 ** 
										&(x # "LOS_MEMBOX_INFO" ->ₛ "nextMembox") # Ptr |-> x0 **
										completeMembox x z
	end. 

(*
	Definition addrAuthority (x: addr) (s: nat): Prop := 暂
*)

(* question: This is copied from Coq.Lists.List. How to delete it? *)


Module LOS_MemboxInit.

(* Require：pool <> NULL && blkSize<>0 && poolSize >= 5 * sizeof_Z + blkSize *)

Definition completeLastMembox (x: addr) (poolSize: Z) (blkSize: Z) (m: MemBox): Prop :=
	 m.(mstartAddr) = x /\
   m.(muwBlkSize) = ( blkSize + sizeof_Z - 1  ) / sizeof_Z * sizeof_Z /\
   Z.of_nat (List.length m.(mFreeList)) = (poolSize - 5 * sizeof_Z) / m.(muwBlkSize) /\
   Z.of_nat (List.length m.(mAllocList)) = 0.

(* Definition Pre (pool: addr) (blkSize : Z) (poolSize: Z) := 
	[| pool <> NULL /\ blkSize > 0 /\ poolSize >= 5 * sizeof_Z + blkSize |] &&
	emp.

Definition Post (pool: addr) (blkSize : Z) (poolSize: Z) (__return : Z): Assertion :=
	EX m: MemBox,
		[|__return = 1 /\ completeLastMembox pool poolSize blkSize m |] && 
		completeMembox pool m.
*)

End LOS_MemboxInit.

Import LOS_MemboxInit.

Module OsMemBoxAdd.

Definition abstractMemboxAlloc (x: addr) (poolSize: Z) (blkSize: Z) (s1: MemboxAbstractState) (s2: MemboxAbstractState): Prop :=
  exists m:MemBox,
    s2.(mboxList) = s1.(mboxList) ++ [m] /\
    completeLastMembox x poolSize blkSize m.

	(* TODO: Pre Post when membox list exists --> wait for the determined macro *)
End OsMemBoxAdd.

Module LOS_MemboxAlloc.

(*
	LOS_MemboxAlloc
	Require：pool <> NULL 
*)

Definition abstractMemboxAllocOnAllocList (n1: AllocMemBoxNode) (m1: MemBox) (m2: MemBox) : Prop :=
    exists l1 l2: AllocList, 
        m1.(mAllocList) = l1 ++ l2 /\
        m2.(mAllocList) = l1 ++ [n1] ++ l2.

(* 	
	When use EX, it comes 
	Error: The reference l1 was not found in the current environment. Why?
*)

Definition abstractMemboxAllocOnFreeList (n1: FreeMemBoxNode) (m1: MemBox) (m2: MemBox) : Prop :=
    head m1.(mFreeList) = Some(n1) /\
    tail m1.(mFreeList) = m2.(mFreeList).

Definition abstractMemboxAlloc2 (x: addr) (s1: MemboxAbstractState) (s2: MemboxAbstractState) (__return: addr): Prop :=
    exists (m1 m2: MemBox) (l1 l2: MemBoxList),   
        s1.(mboxList) = (l1 ++ [m1] ++ l2) /\
        s2.(mboxList) = (l1 ++ [m2] ++ l2) /\
        m1.(mstartAddr) = x /\
        m2.(mstartAddr) = x /\
        exists (n1: FreeMemBoxNode) (n2: AllocMemBoxNode),
            n1.(fnstartAddr) = n2.(anstartAddr) /\
            __return = n2.(anstartAddr) /\
            abstractMemboxAllocOnFreeList n1 m1 m2 /\
            abstractMemboxAllocOnAllocList n2 m1 m2.

	
(* 
Definition Pre (pool: addr) (m: MemBox) (n1: FreeMemBoxNode) (n2: AllocMemBoxNode) (l1: FreeList) (l2: AllocList) : Assertion :=
	[| pool <> NULL /\ m.(mFreeList) = (n1 :: l1) /\ m.(mAllocList) = l2|] && 
	completeMembox pool m.
	
Definition Post (pool: addr) (m: MemBox) (n1: FreeMemBoxNode) (n2: AllocMemBoxNode) (l1: FreeList) (l2: AllocList) (__return: addr): Assertion :=
	[| __return = n2.(anstartAddr) /\ m.(mFreeList) = l1 /\ m.(mAllocList) = (n2 :: l2) /\ n2.(anstartAddr) = n1.(fnstartAddr) |] &&
	completeMembox pool m.
*)

End LOS_MemboxAlloc.  

Module LOS_MemboxFree.
(*
	Require: pool <> NULL && box <> NULL 内存块初始存放符合魔法字格式
*)

Definition abstractMemboxFreeOnAllocList (n: AllocMemBoxNode) (m1: MemBox) (m2: MemBox) : Prop :=
    exists (l1 l2: AllocList), 
        m2.(mAllocList) = l1 ++ l2 /\
        m1.(mAllocList) = l1 ++ [n] ++ l2.

Definition abstractMemboxFreeOnFreeList (n: FreeMemBoxNode) (m1: MemBox) (m2: MemBox) : Prop :=
    head m2.(mFreeList) = Some(n) /\
    tail m2.(mFreeList) = m1.(mFreeList).

Definition abstractMemboxFree (x: addr) (y: addr) (s1: MemboxAbstractState) (s2: MemboxAbstractState) : Prop :=
    exists (m1 m2: MemBox) (l1 l2: MemBoxList),    
        s1.(mboxList) = l1 ++ [m1] ++ l2 /\
        s2.(mboxList) = l1 ++ [m2] ++ l2 /\
        m1.(mstartAddr) = x /\
        m2.(mstartAddr) = x /\
        exists (n1: AllocMemBoxNode) (n2: FreeMemBoxNode),
            n2.(fnstartAddr) = n1.(anstartAddr) /\
            y = n1.(anstartAddr) /\
            abstractMemboxFreeOnAllocList n1 m1 m2 /\
            abstractMemboxFreeOnFreeList n2 m1 m2.

(* Definition checkBoxMem (box: addr) (node: addr) : Assertion :=
	[|box <> NULL /\ node <> NULL|].

	This might be included in the predicates?
*)
(*
Definition Pre (pool: addr) (box: addr) (m:MemBox) (n1: FreeMemBoxNode) (n2: AllocMemBoxNode) (l1: FreeList) (l2 l3: AllocList) : Assertion :=
	[|pool <> NULL /\ box <> NULL /\ m.(mFreeList) = l1 /\ m.(mAllocList) = (l2 ++ [n2] ++ l3)|] && 
	completeMembox pool m.

Definition Post (pool: addr) (box: addr) (m:MemBox) (n1: FreeMemBoxNode) (n2: AllocMemBoxNode) (l1: FreeList) (l2 l3: AllocList) (__return : bool): Assertion := 
	[| __return = true /\ m.(mFreeList) = (n1::l1) /\ m.(mAllocList) = (l2 ++ l3) /\ (n1.(fnstartAddr) = n2.(anstartAddr))|] &&
	completeMembox pool m. 
*)

End LOS_MemboxFree.

Module LOS_MemboxClr.

Definition abstractMemboxFree (x: addr) (y: addr) (s1: MemboxAbstractState) (s2: MemboxAbstractState) : Prop :=
    exists (m1 m2: MemBox) (l1 l2: MemBoxList),    
        s1.(mboxList) = l1 ++ [m1] ++ l2 /\
        s2.(mboxList) = l1 ++ [m2] ++ l2 /\
        m1.(mstartAddr) = x /\
        m2.(mstartAddr) = x /\
        exists (n1: AllocMemBoxNode) (n2: FreeMemBoxNode),
            n2.(fnstartAddr) = n1.(anstartAddr) /\
            y = n2.(fnstartAddr).
	(* TODO: should add n2? *)

Definition Pre (pool: addr) (box: addr) (m: MemBox) (y:Z) : Assertion :=
	([| pool = NULL \/ box = NULL |] && emp) ||
	([| pool <> NULL /\ box <> NULL |] && completeMembox pool m && ((EX a: AllocMemBoxNode, completeAllocBlock a ) || (EX (f: FreeMemBoxNode) (x: addr), completeFreeBlock x f)) **
	EX x v: Z,
	(&(box # "LOS_MEMBOX_INFO" ->ₛ "uwBlkSize") # Int |-> x **
	[| y >= 5 * sizeof_Z /\ y < x|] &&
	store_char (x + y) v)).

Definition Post (pool: addr) (box: addr) (m: MemBox) (y:Z): Assertion :=
	([| pool = NULL \/ box = NULL |] && emp) ||
	(EX x : Z,
	(&(box # "LOS_MEMBOX_INFO" ->ₛ "uwBlkSize") # Int |-> x **
	[| y >= 5 * sizeof_Z /\ y < x|] &&
	store_char (x + y) 0)).
End LOS_MemboxClr. 

(* TODO: organize the questions *)
 
             

