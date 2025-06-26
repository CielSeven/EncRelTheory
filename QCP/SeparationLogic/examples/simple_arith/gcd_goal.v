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
Require Import common_strategy_goal.
Require Import common_strategy_proof.

(*----- Function gcd -----*)

Definition gcd_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition gcd_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre <> 0) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| ((x_pre <> (INT_MIN)) \/ (y_pre <> (-1))) |] 
  &&  [| (y_pre <> 0) |]
.

Definition gcd_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
.

Definition gcd_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (x_pre))) |] 
  &&  [| (y_pre = 0) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  emp
|--
  [| (retval = (Zgcd (x_pre) (y_pre))) |]
  &&  emp
.

Definition gcd_return_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (retval: Z) ,
  [| (retval = (Zgcd (y_pre) ((x_pre % ( y_pre ) )))) |] 
  &&  [| (y_pre <> 0) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  emp
|--
  [| (retval = (Zgcd (x_pre) (y_pre))) |]
  &&  emp
.

Definition gcd_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre = 0) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition gcd_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre = 0) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  emp
|--
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (y_pre = 0) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  emp
.

Definition gcd_partial_solve_wit_1 := gcd_partial_solve_wit_1_pure -> gcd_partial_solve_wit_1_aux.

Definition gcd_partial_solve_wit_2_pure := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre <> 0) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  [| (INT_MIN < y_pre) |] 
  &&  [| (INT_MIN < (x_pre % ( y_pre ) )) |]
.

Definition gcd_partial_solve_wit_2_aux := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre <> 0) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  emp
|--
  [| (INT_MIN < y_pre) |] 
  &&  [| (INT_MIN < (x_pre % ( y_pre ) )) |] 
  &&  [| (y_pre <> 0) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (INT_MIN < y_pre) |]
  &&  emp
.

Definition gcd_partial_solve_wit_2 := gcd_partial_solve_wit_2_pure -> gcd_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_gcd_safety_wit_1 : gcd_safety_wit_1.
Axiom proof_of_gcd_safety_wit_2 : gcd_safety_wit_2.
Axiom proof_of_gcd_entail_wit_1 : gcd_entail_wit_1.
Axiom proof_of_gcd_return_wit_1 : gcd_return_wit_1.
Axiom proof_of_gcd_return_wit_2 : gcd_return_wit_2.
Axiom proof_of_gcd_partial_solve_wit_1_pure : gcd_partial_solve_wit_1_pure.
Axiom proof_of_gcd_partial_solve_wit_1 : gcd_partial_solve_wit_1.
Axiom proof_of_gcd_partial_solve_wit_2_pure : gcd_partial_solve_wit_2_pure.
Axiom proof_of_gcd_partial_solve_wit_2 : gcd_partial_solve_wit_2.

End VC_Correct.
