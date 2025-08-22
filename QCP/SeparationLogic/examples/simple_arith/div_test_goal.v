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
Require Import PDiv_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function div_test -----*)

Definition div_test_safety_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition div_test_safety_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (c_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition div_test_safety_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (c_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (((a_pre * b_pre ) <> (-9223372036854775808)) \/ (c_pre <> (-1))) |] 
  &&  [| (c_pre <> 0) |]
.

Definition div_test_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (c_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre * b_pre ) <= 9223372036854775807) |] 
  &&  [| ((-9223372036854775808) <= (a_pre * b_pre )) |]
.

Definition div_test_safety_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (c_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int64  |-> ((a_pre * b_pre ) ÷ c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition div_test_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (((a_pre * b_pre ) ÷ c_pre ) < 0) |] 
  &&  [| (c_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int64  |-> ((a_pre * b_pre ) ÷ c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition div_test_return_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (c_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 = (Pos_Div ((a_pre * b_pre )) (c_pre) (0))) |]
  &&  emp
.

Definition div_test_return_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (((a_pre * b_pre ) ÷ c_pre ) < 0) |] 
  &&  [| (c_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 = (Pos_Div ((a_pre * b_pre )) (c_pre) (0))) |]
  &&  emp
.

Definition div_test_return_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (((a_pre * b_pre ) ÷ c_pre ) >= 0) |] 
  &&  [| (c_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (((a_pre * b_pre ) ÷ c_pre ) = (Pos_Div ((a_pre * b_pre )) (c_pre) (0))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_div_test_safety_wit_1 : div_test_safety_wit_1.
Axiom proof_of_div_test_safety_wit_2 : div_test_safety_wit_2.
Axiom proof_of_div_test_safety_wit_3 : div_test_safety_wit_3.
Axiom proof_of_div_test_safety_wit_4 : div_test_safety_wit_4.
Axiom proof_of_div_test_safety_wit_5 : div_test_safety_wit_5.
Axiom proof_of_div_test_safety_wit_6 : div_test_safety_wit_6.
Axiom proof_of_div_test_return_wit_1 : div_test_return_wit_1.
Axiom proof_of_div_test_return_wit_2 : div_test_return_wit_2.
Axiom proof_of_div_test_return_wit_3 : div_test_return_wit_3.

End VC_Correct.
