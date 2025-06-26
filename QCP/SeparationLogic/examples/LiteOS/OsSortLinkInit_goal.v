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

(*----- Function LOS_ListInit -----*)

Definition LOS_ListInit_return_wit_1 := 
forall (A: Type) (list_pre: Z) (storeA: (Z -> (A -> Assertion))) ,
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
|--
  (store_dll storeA list_pre nil )
.

(*----- Function OsSortLinkInit -----*)

Definition OsSortLinkInit_return_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (storeA: (Z -> (A -> Assertion))) ,
  (store_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") nil )
|--
  [| (0 = 0) |]
  &&  (store_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") nil )
.

Definition OsSortLinkInit_partial_solve_wit_1 := 
forall (sortLinkHead_pre: Z) ,
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |->_)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |->_)
|--
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |->_)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |->_)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_LOS_ListInit_return_wit_1 : LOS_ListInit_return_wit_1.
Axiom proof_of_OsSortLinkInit_return_wit_1 : OsSortLinkInit_return_wit_1.
Axiom proof_of_OsSortLinkInit_partial_solve_wit_1 : OsSortLinkInit_partial_solve_wit_1.

End VC_Correct.
