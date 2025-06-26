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

(*----- Function OsGetSortLinkAttribute -----*)

Definition OsGetSortLinkAttribute_safety_wit_1 := 
forall (type_pre: Z) (u: Z) ,
  [| (( &( "g_taskSortLink" ) ) <> 0) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) <> 0) |] 
  &&  [| (type_pre = u) |]
  &&  ((( &( "type" ) )) # Int  |-> type_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition OsGetSortLinkAttribute_safety_wit_2 := 
forall (type_pre: Z) (u: Z) ,
  [| (type_pre <> 1) |] 
  &&  [| (( &( "g_taskSortLink" ) ) <> 0) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) <> 0) |] 
  &&  [| (type_pre = u) |]
  &&  ((( &( "type" ) )) # Int  |-> type_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition OsGetSortLinkAttribute_safety_wit_3 := 
forall (type_pre: Z) (u: Z) ,
  [| (type_pre <> 2) |] 
  &&  [| (type_pre <> 1) |] 
  &&  [| (( &( "g_taskSortLink" ) ) <> 0) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) <> 0) |] 
  &&  [| (type_pre = u) |]
  &&  ((( &( "type" ) )) # Int  |-> type_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition OsGetSortLinkAttribute_return_wit_1 := 
forall (type_pre: Z) (u: Z) ,
  [| (type_pre = 1) |] 
  &&  [| (( &( "g_taskSortLink" ) ) <> 0) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) <> 0) |] 
  &&  [| (type_pre = u) |]
  &&  emp
|--
  ([| (u <> 1) |] 
  &&  [| (u <> 2) |] 
  &&  [| (( &( "g_taskSortLink" ) ) = 0) |] 
  &&  [| (type_pre = u) |]
  &&  emp)
  ||
  ([| (u = 2) |] 
  &&  [| (( &( "g_taskSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) |] 
  &&  [| (type_pre = u) |]
  &&  emp)
  ||
  ([| (u = 1) |] 
  &&  [| (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) |] 
  &&  [| (type_pre = u) |]
  &&  emp)
.

Definition OsGetSortLinkAttribute_return_wit_2 := 
forall (type_pre: Z) (u: Z) ,
  [| (type_pre = 2) |] 
  &&  [| (type_pre <> 1) |] 
  &&  [| (( &( "g_taskSortLink" ) ) <> 0) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) <> 0) |] 
  &&  [| (type_pre = u) |]
  &&  emp
|--
  ([| (u <> 1) |] 
  &&  [| (u <> 2) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) = 0) |] 
  &&  [| (type_pre = u) |]
  &&  emp)
  ||
  ([| (u = 2) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) |] 
  &&  [| (type_pre = u) |]
  &&  emp)
  ||
  ([| (u = 1) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) = ( &( "g_taskSortLink" ) )) |] 
  &&  [| (type_pre = u) |]
  &&  emp)
.

Definition OsGetSortLinkAttribute_return_wit_3 := 
forall (type_pre: Z) (u: Z) ,
  [| (type_pre <> 2) |] 
  &&  [| (type_pre <> 1) |] 
  &&  [| (( &( "g_taskSortLink" ) ) <> 0) |] 
  &&  [| (( &( "g_swtmrSortLink" ) ) <> 0) |] 
  &&  [| (type_pre = u) |]
  &&  emp
|--
  ([| (u <> 1) |] 
  &&  [| (u <> 2) |] 
  &&  [| (0 = 0) |] 
  &&  [| (type_pre = u) |]
  &&  emp)
  ||
  ([| (u = 2) |] 
  &&  [| (0 = ( &( "g_swtmrSortLink" ) )) |] 
  &&  [| (type_pre = u) |]
  &&  emp)
  ||
  ([| (u = 1) |] 
  &&  [| (0 = ( &( "g_taskSortLink" ) )) |] 
  &&  [| (type_pre = u) |]
  &&  emp)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsGetSortLinkAttribute_safety_wit_1 : OsGetSortLinkAttribute_safety_wit_1.
Axiom proof_of_OsGetSortLinkAttribute_safety_wit_2 : OsGetSortLinkAttribute_safety_wit_2.
Axiom proof_of_OsGetSortLinkAttribute_safety_wit_3 : OsGetSortLinkAttribute_safety_wit_3.
Axiom proof_of_OsGetSortLinkAttribute_return_wit_1 : OsGetSortLinkAttribute_return_wit_1.
Axiom proof_of_OsGetSortLinkAttribute_return_wit_2 : OsGetSortLinkAttribute_return_wit_2.
Axiom proof_of_OsGetSortLinkAttribute_return_wit_3 : OsGetSortLinkAttribute_return_wit_3.

End VC_Correct.
