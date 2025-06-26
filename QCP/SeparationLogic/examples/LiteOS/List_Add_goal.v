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

(*----- Function LOS_ListAdd -----*)

Definition LOS_ListAdd_return_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (list_pstNext: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext)
  **  (storeA node_pre a )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
  **  ((&((list_pstNext)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
|--
  ((&((list_pstNext)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext)
  **  (dllseg_shift storeA list_pre node_pre (cons ((Build_DL_Node (a) (node_pre))) (nil)) )
.

(*----- Function LOS_ListTailInsert -----*)

Definition LOS_ListTailInsert_return_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (list_pstPrev: Z) ,
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  (dllseg_shift storeA list_pstPrev node_pre (cons ((Build_DL_Node (a) (node_pre))) (nil)) )
  **  (dllseg_shift storeA list_pre list_pstPrev l )
|--
  (store_dll storeA list_pre (app (l) ((cons ((Build_DL_Node (a) (node_pre))) (nil)))) )
.

Definition LOS_ListTailInsert_partial_solve_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (pu: Z) (un: Z) ,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  (store_dll storeA list_pre l )
|--
  (store_dll storeA list_pre l )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
.

Definition LOS_ListTailInsert_partial_solve_wit_2 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (pu: Z) (un: Z) (list_pstPrev: Z) ,
  ((&((list_pstPrev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pstPrev)
  **  (dllseg_shift storeA list_pre list_pstPrev l )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  ((&((list_pstPrev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pstPrev)
  **  (dllseg_shift storeA list_pre list_pstPrev l )
.

Definition LOS_ListTailInsert_which_implies_wit_1 := 
forall (A: Type) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (list: Z) ,
  (store_dll storeA list l )
|--
  EX list_pstPrev,
  ((&((list_pstPrev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list)
  **  ((&((list)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pstPrev)
  **  (dllseg_shift storeA list list_pstPrev l )
.

(*----- Function LOS_ListHeadInsert -----*)

Definition LOS_ListHeadInsert_return_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (a: A) ,
  (store_dll storeA list_pre (cons ((Build_DL_Node (a) (node_pre))) (l)) )
|--
  (store_dll storeA list_pre (cons ((Build_DL_Node (a) (node_pre))) (l)) )
.

Definition LOS_ListHeadInsert_partial_solve_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (a: A) (pu: Z) (un: Z) ,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  (store_dll storeA list_pre l )
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  (store_dll storeA list_pre l )
.

Definition LOS_ListAdd_derive_high_level_spec_by_low_level_spec := 
forall (A: Type) ,
forall (node_pre: Z) (list_pre: Z) (a: A) (l: (@list (@DL_Node A))) (storeA1: (Z -> (A -> Assertion))) ,
  EX un pu,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA1 node_pre a )
  **  (store_dll storeA1 list_pre l )
|--
EX (A: Type) ,
EX (storeA: (Z -> (A -> Assertion))) (a_2: A) (list_pstNext: Z) ,
  (EX un_2 pu_2,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu_2)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un_2)
  **  (storeA node_pre a_2 )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext)
  **  ((&((list_pstNext)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre))
  **
  ((((&((list_pstNext)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext)
  **  (dllseg_shift storeA list_pre node_pre (cons ((Build_DL_Node (a_2) (node_pre))) (nil)) ))
  -*
  ((store_dll storeA1 list_pre (cons ((Build_DL_Node (a) (node_pre))) (l)) )))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_LOS_ListAdd_return_wit_1 : LOS_ListAdd_return_wit_1.
Axiom proof_of_LOS_ListTailInsert_return_wit_1 : LOS_ListTailInsert_return_wit_1.
Axiom proof_of_LOS_ListTailInsert_partial_solve_wit_1 : LOS_ListTailInsert_partial_solve_wit_1.
Axiom proof_of_LOS_ListTailInsert_partial_solve_wit_2 : LOS_ListTailInsert_partial_solve_wit_2.
Axiom proof_of_LOS_ListTailInsert_which_implies_wit_1 : LOS_ListTailInsert_which_implies_wit_1.
Axiom proof_of_LOS_ListHeadInsert_return_wit_1 : LOS_ListHeadInsert_return_wit_1.
Axiom proof_of_LOS_ListHeadInsert_partial_solve_wit_1 : LOS_ListHeadInsert_partial_solve_wit_1.
Axiom proof_of_LOS_ListAdd_derive_high_level_spec_by_low_level_spec : LOS_ListAdd_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
