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
Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function max3 -----*)

Definition max3_return_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (y_pre < z_pre) |] 
  &&  [| (x_pre < y_pre) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= z_pre) |] 
  &&  [| (z_pre <= INT_MAX) |]
  &&  emp
|--
  [| (z_pre >= x_pre) |] 
  &&  [| (z_pre >= y_pre) |] 
  &&  [| (z_pre >= z_pre) |]
  &&  emp
.

Definition max3_return_wit_2 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (y_pre >= z_pre) |] 
  &&  [| (x_pre < y_pre) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= z_pre) |] 
  &&  [| (z_pre <= INT_MAX) |]
  &&  emp
|--
  [| (y_pre >= x_pre) |] 
  &&  [| (y_pre >= y_pre) |] 
  &&  [| (y_pre >= z_pre) |]
  &&  emp
.

Definition max3_return_wit_3 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (x_pre < z_pre) |] 
  &&  [| (x_pre >= y_pre) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= z_pre) |] 
  &&  [| (z_pre <= INT_MAX) |]
  &&  emp
|--
  [| (z_pre >= x_pre) |] 
  &&  [| (z_pre >= y_pre) |] 
  &&  [| (z_pre >= z_pre) |]
  &&  emp
.

Definition max3_return_wit_4 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (x_pre >= z_pre) |] 
  &&  [| (x_pre >= y_pre) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= z_pre) |] 
  &&  [| (z_pre <= INT_MAX) |]
  &&  emp
|--
  [| (x_pre >= x_pre) |] 
  &&  [| (x_pre >= y_pre) |] 
  &&  [| (x_pre >= z_pre) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_max3_return_wit_1 : max3_return_wit_1.
Axiom proof_of_max3_return_wit_2 : max3_return_wit_2.
Axiom proof_of_max3_return_wit_3 : max3_return_wit_3.
Axiom proof_of_max3_return_wit_4 : max3_return_wit_4.

End VC_Correct.
