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

(*----- Function add -----*)

Definition add_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((x_pre + y_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + y_pre )) |]
.

Definition add_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  emp
|--
  [| ((x_pre + y_pre ) = (x_pre + y_pre )) |]
  &&  emp
.

(*----- Function slow_add -----*)

Definition slow_add_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) ,
  [| (0 <= x) |] 
  &&  [| (x <= 100) |] 
  &&  [| (0 <= y) |] 
  &&  [| (y <= 200) |] 
  &&  [| ((x + y ) = (x_pre + y_pre )) |] 
  &&  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition slow_add_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= 100) |] 
  &&  [| (0 <= y) |] 
  &&  [| (y <= 200) |] 
  &&  [| ((x + y ) = (x_pre + y_pre )) |] 
  &&  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  [| ((x - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x - 1 )) |]
.

Definition slow_add_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= 100) |] 
  &&  [| (0 <= y) |] 
  &&  [| (y <= 200) |] 
  &&  [| ((x + y ) = (x_pre + y_pre )) |] 
  &&  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition slow_add_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= 100) |] 
  &&  [| (0 <= y) |] 
  &&  [| (y <= 200) |] 
  &&  [| ((x + y ) = (x_pre + y_pre )) |] 
  &&  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  ((( &( "x" ) )) # Int  |-> (x - 1 ))
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  [| ((y + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y + 1 )) |]
.

Definition slow_add_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= 100) |] 
  &&  [| (0 <= y) |] 
  &&  [| (y <= 200) |] 
  &&  [| ((x + y ) = (x_pre + y_pre )) |] 
  &&  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  ((( &( "x" ) )) # Int  |-> (x - 1 ))
  **  ((( &( "y" ) )) # Int  |-> y)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition slow_add_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  emp
|--
  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 200) |] 
  &&  [| ((x_pre + y_pre ) = (x_pre + y_pre )) |] 
  &&  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  emp
.

Definition slow_add_entail_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) ,
  [| (x > 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= 100) |] 
  &&  [| (0 <= y) |] 
  &&  [| (y <= 200) |] 
  &&  [| ((x + y ) = (x_pre + y_pre )) |] 
  &&  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  emp
|--
  [| (0 <= (x - 1 )) |] 
  &&  [| ((x - 1 ) <= 100) |] 
  &&  [| (0 <= (y + 1 )) |] 
  &&  [| ((y + 1 ) <= 200) |] 
  &&  [| (((x - 1 ) + (y + 1 ) ) = (x_pre + y_pre )) |] 
  &&  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  emp
.

Definition slow_add_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (y: Z) (x: Z) ,
  [| (x <= 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (x <= 100) |] 
  &&  [| (0 <= y) |] 
  &&  [| (y <= 200) |] 
  &&  [| ((x + y ) = (x_pre + y_pre )) |] 
  &&  [| (0 <= x_pre) |] 
  &&  [| (x_pre <= 100) |] 
  &&  [| (0 <= y_pre) |] 
  &&  [| (y_pre <= 100) |]
  &&  emp
|--
  [| (y = (x_pre + y_pre )) |]
  &&  emp
.

(*----- Function add1_1 -----*)

Definition add1_1_safety_wit_1 := 
forall (x_pre: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre < INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((x_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + 1 )) |]
.

Definition add1_1_safety_wit_2 := 
forall (x_pre: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre < INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition add1_1_return_wit_1 := 
forall (x_pre: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre < INT_MAX) |]
  &&  emp
|--
  [| ((x_pre + 1 ) = (x_pre + 1 )) |]
  &&  emp
.

(*----- Function add1_2 -----*)

Definition add1_2_safety_wit_1 := 
forall (x_pre: Z) (v: Z) ,
  [| (INT_MIN <= v) |] 
  &&  [| (v < INT_MAX) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Int  |-> v)
|--
  [| ((v + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v + 1 )) |]
.

Definition add1_2_return_wit_1 := 
forall (x_pre: Z) (v: Z) ,
  [| (INT_MIN <= v) |] 
  &&  [| (v < INT_MAX) |]
  &&  ((x_pre) # Int  |-> (v + 1 ))
|--
  EX x_pre_v,
  [| (x_pre_v = (v + 1 )) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
.

(*----- Function add1_3 -----*)

Definition add1_3_safety_wit_1 := 
forall (x_pre: Z) (v: Z) (x_pre_v: Z) ,
  [| (INT_MIN <= v) |] 
  &&  [| (v < INT_MAX) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Ptr  |-> x_pre_v)
  **  ((x_pre_v) # Int  |-> v)
|--
  [| ((v + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (v + 1 )) |]
.

Definition add1_3_safety_wit_2 := 
forall (x_pre: Z) (v: Z) (x_pre_v: Z) ,
  [| (INT_MIN <= v) |] 
  &&  [| (v < INT_MAX) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((x_pre) # Ptr  |-> x_pre_v)
  **  ((x_pre_v) # Int  |-> v)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition add1_3_return_wit_1 := 
forall (x_pre: Z) (v: Z) (x_pre_v_2: Z) ,
  [| (INT_MIN <= v) |] 
  &&  [| (v < INT_MAX) |]
  &&  ((x_pre) # Ptr  |-> x_pre_v_2)
  **  ((x_pre_v_2) # Int  |-> (v + 1 ))
|--
  EX x_pre_v_v x_pre_v,
  [| (x_pre_v_v = (v + 1 )) |]
  &&  ((x_pre) # Ptr  |-> x_pre_v)
  **  ((x_pre_v) # Int  |-> x_pre_v_v)
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_add_safety_wit_1 : add_safety_wit_1.
Axiom proof_of_add_return_wit_1 : add_return_wit_1.
Axiom proof_of_slow_add_safety_wit_1 : slow_add_safety_wit_1.
Axiom proof_of_slow_add_safety_wit_2 : slow_add_safety_wit_2.
Axiom proof_of_slow_add_safety_wit_3 : slow_add_safety_wit_3.
Axiom proof_of_slow_add_safety_wit_4 : slow_add_safety_wit_4.
Axiom proof_of_slow_add_safety_wit_5 : slow_add_safety_wit_5.
Axiom proof_of_slow_add_entail_wit_1 : slow_add_entail_wit_1.
Axiom proof_of_slow_add_entail_wit_2 : slow_add_entail_wit_2.
Axiom proof_of_slow_add_return_wit_1 : slow_add_return_wit_1.
Axiom proof_of_add1_1_safety_wit_1 : add1_1_safety_wit_1.
Axiom proof_of_add1_1_safety_wit_2 : add1_1_safety_wit_2.
Axiom proof_of_add1_1_return_wit_1 : add1_1_return_wit_1.
Axiom proof_of_add1_2_safety_wit_1 : add1_2_safety_wit_1.
Axiom proof_of_add1_2_return_wit_1 : add1_2_return_wit_1.
Axiom proof_of_add1_3_safety_wit_1 : add1_3_safety_wit_1.
Axiom proof_of_add1_3_safety_wit_2 : add1_3_safety_wit_2.
Axiom proof_of_add1_3_return_wit_1 : add1_3_return_wit_1.

End VC_Correct.
