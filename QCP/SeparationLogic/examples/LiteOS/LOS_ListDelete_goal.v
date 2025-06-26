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
Require Import LOS_Verify.lib.sortlink.
Require Import LOS_Verify.lib.dll.
Require Import LOS_Verify.lib.tick_backup.
Local Open Scope sac.
From LOS_Verify.VC.strategy Require Import common_strategy_goal.
From LOS_Verify.VC.strategy Require Import common_strategy_proof.
From LOS_Verify.VC.strategy Require Import los_sortlink_strategy_goal.
From LOS_Verify.VC.strategy Require Import los_sortlink_strategy_proof.

(*----- Function LOS_ListDelete -----*)

Definition LOS_ListDelete_safety_wit_1 := 
forall (A: Type) (node_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  (dllseg_shift storeA node_pre node_pre nil )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
  **  (storeA node_pre a )
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition LOS_ListDelete_safety_wit_2 := 
forall (A: Type) (node_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  (dllseg_shift storeA node_pre node_pre nil )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
  **  (storeA node_pre a )
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> 0)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition LOS_ListDelete_return_wit_1 := 
forall (A: Type) (node_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  (dllseg_shift storeA node_pre node_pre nil )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> 0)
  **  (storeA node_pre a )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> 0)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |->_)
  **  (storeA node_pre a )
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
.

Definition LOS_ListDelete_partial_solve_wit_1 := 
forall (A: Type) (node_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  (dllseg_shift storeA prev node_pre (cons ((Build_DL_Node (a) (node_pre))) (nil)) )
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
  **  (dllseg_shift storeA node_pre node_pre nil )
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
  **  (storeA node_pre a )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
.

Definition LOS_ListDelete_partial_solve_wit_2 := 
forall (A: Type) (node_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  (dllseg_shift storeA prev node_pre (cons ((Build_DL_Node (a) (node_pre))) (nil)) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
  **  (dllseg_shift storeA node_pre node_pre nil )
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
  **  (storeA node_pre a )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
.

Definition LOS_ListDelete_partial_solve_wit_3 := 
forall (A: Type) (node_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  (dllseg_shift storeA prev node_pre (cons ((Build_DL_Node (a) (node_pre))) (nil)) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
|--
  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  (dllseg_shift storeA node_pre node_pre nil )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
  **  (storeA node_pre a )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
.

Definition LOS_ListDelete_derive_mid_level_spec_by_low_level_spec := 
forall (A: Type) ,
forall (node_pre: Z) (l2: (@list (@DL_Node A))) (l1: (@list (@DL_Node A))) (a: A) (p: Z) (storeA1: (Z -> (A -> Assertion))) ,
  (store_dll storeA1 p (app (l1) ((cons ((Build_DL_Node (a) (node_pre))) (l2)))) )
|--
EX (A: Type) ,
EX (storeA: (Z -> (A -> Assertion))) (a_2: A) (prev: Z) (next: Z) ,
  (((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  (dllseg_shift storeA prev node_pre (cons ((Build_DL_Node (a_2) (node_pre))) (nil)) ))
  **
  ((((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |->_)
  **  (storeA node_pre a_2 )
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev))
  -*
  ((store_dll storeA1 p (app (l1) (l2)) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |->_)
  **  (storeA1 node_pre a )))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_LOS_ListDelete_safety_wit_1 : LOS_ListDelete_safety_wit_1.
Axiom proof_of_LOS_ListDelete_safety_wit_2 : LOS_ListDelete_safety_wit_2.
Axiom proof_of_LOS_ListDelete_return_wit_1 : LOS_ListDelete_return_wit_1.
Axiom proof_of_LOS_ListDelete_partial_solve_wit_1 : LOS_ListDelete_partial_solve_wit_1.
Axiom proof_of_LOS_ListDelete_partial_solve_wit_2 : LOS_ListDelete_partial_solve_wit_2.
Axiom proof_of_LOS_ListDelete_partial_solve_wit_3 : LOS_ListDelete_partial_solve_wit_3.
Axiom proof_of_LOS_ListDelete_derive_mid_level_spec_by_low_level_spec : LOS_ListDelete_derive_mid_level_spec_by_low_level_spec.

End VC_Correct.
