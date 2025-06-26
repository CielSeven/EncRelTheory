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

(*----- Function exgcd -----*)

Definition exgcd_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (1 <> (INT_MIN)) |]
.

Definition exgcd_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition exgcd_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_7 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition exgcd_safety_wit_8 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_10 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exgcd_safety_wit_11 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition exgcd_safety_wit_12 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v: Z) (x_pre_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v ) + ((a_pre % ( b_pre ) ) * y_pre_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| ((Zabs (y_pre_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
  **  ((x_pre) # Int  |-> y_pre_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((x_pre_v - ((a_pre ÷ b_pre ) * y_pre_v ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre_v - ((a_pre ÷ b_pre ) * y_pre_v ) )) |]
.

Definition exgcd_safety_wit_13 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v: Z) (x_pre_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v ) + ((a_pre % ( b_pre ) ) * y_pre_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| ((Zabs (y_pre_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
  **  ((x_pre) # Int  |-> y_pre_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (((a_pre ÷ b_pre ) * y_pre_v ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_pre_v )) |]
.

Definition exgcd_safety_wit_14 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v: Z) (x_pre_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v ) + ((a_pre % ( b_pre ) ) * y_pre_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| ((Zabs (y_pre_v)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
  **  ((x_pre) # Int  |-> y_pre_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition exgcd_safety_wit_15 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v: Z) (x_pre_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v ) + ((a_pre % ( b_pre ) ) * y_pre_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0) |] 
  &&  [| (x_pre_v = 0) |] 
  &&  [| ((Zabs (y_pre_v)) <= 1) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
  **  ((x_pre) # Int  |-> y_pre_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((x_pre_v - ((a_pre ÷ b_pre ) * y_pre_v ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre_v - ((a_pre ÷ b_pre ) * y_pre_v ) )) |]
.

Definition exgcd_safety_wit_16 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v: Z) (x_pre_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v ) + ((a_pre % ( b_pre ) ) * y_pre_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0) |] 
  &&  [| (x_pre_v = 0) |] 
  &&  [| ((Zabs (y_pre_v)) <= 1) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
  **  ((x_pre) # Int  |-> y_pre_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (((a_pre ÷ b_pre ) * y_pre_v ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_pre_v )) |]
.

Definition exgcd_safety_wit_17 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v: Z) (x_pre_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v ) + ((a_pre % ( b_pre ) ) * y_pre_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0) |] 
  &&  [| (x_pre_v = 0) |] 
  &&  [| ((Zabs (y_pre_v)) <= 1) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
  **  ((x_pre) # Int  |-> y_pre_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition exgcd_safety_wit_18 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v: Z) (x_pre_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v ) + ((a_pre % ( b_pre ) ) * y_pre_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
  **  ((x_pre) # Int  |-> y_pre_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((x_pre_v - ((a_pre ÷ b_pre ) * y_pre_v ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre_v - ((a_pre ÷ b_pre ) * y_pre_v ) )) |]
.

Definition exgcd_safety_wit_19 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v: Z) (x_pre_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v ) + ((a_pre % ( b_pre ) ) * y_pre_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
  **  ((x_pre) # Int  |-> y_pre_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (((a_pre ÷ b_pre ) * y_pre_v ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a_pre ÷ b_pre ) * y_pre_v )) |]
.

Definition exgcd_safety_wit_20 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v: Z) (x_pre_v: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v ) + ((a_pre % ( b_pre ) ) * y_pre_v ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> x_pre_v)
  **  ((x_pre) # Int  |-> y_pre_v)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition exgcd_return_wit_1_1 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (a_pre))) |] 
  &&  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  (EX y_pre_v x_pre_v,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX y_pre_v_2 x_pre_v_2,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX y_pre_v_3 x_pre_v_3,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_1_2 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (a_pre))) |] 
  &&  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  (EX y_pre_v x_pre_v,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX y_pre_v_2 x_pre_v_2,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX y_pre_v_3 x_pre_v_3,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_1_3 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (retval: Z) ,
  [| (retval = (Zabs (a_pre))) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  (EX y_pre_v x_pre_v,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX y_pre_v_2 x_pre_v_2,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX y_pre_v_3 x_pre_v_3,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_2_1 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v_4: Z) (x_pre_v_4: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v_4 ) + ((a_pre % ( b_pre ) ) * y_pre_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_4)) <= ((Zabs ((a_pre % ( b_pre ) ))) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| ((Zabs (y_pre_v_4)) <= ((Zabs (b_pre)) ÷ (Zgcd (b_pre) ((a_pre % ( b_pre ) ))) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> (x_pre_v_4 - ((a_pre ÷ b_pre ) * y_pre_v_4 ) ))
  **  ((x_pre) # Int  |-> y_pre_v_4)
|--
  (EX y_pre_v x_pre_v,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX y_pre_v_2 x_pre_v_2,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX y_pre_v_3 x_pre_v_3,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_2_2 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v_4: Z) (x_pre_v_4: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v_4 ) + ((a_pre % ( b_pre ) ) * y_pre_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((b_pre % ( (a_pre % ( b_pre ) ) ) ) = 0) |] 
  &&  [| (x_pre_v_4 = 0) |] 
  &&  [| ((Zabs (y_pre_v_4)) <= 1) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> (x_pre_v_4 - ((a_pre ÷ b_pre ) * y_pre_v_4 ) ))
  **  ((x_pre) # Int  |-> y_pre_v_4)
|--
  (EX y_pre_v x_pre_v,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX y_pre_v_2 x_pre_v_2,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX y_pre_v_3 x_pre_v_3,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_return_wit_2_3 := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) (y_pre_v_4: Z) (x_pre_v_4: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (((b_pre * x_pre_v_4 ) + ((a_pre % ( b_pre ) ) * y_pre_v_4 ) ) = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| ((Zabs (x_pre_v_4)) <= 1) |] 
  &&  [| (y_pre_v_4 = 0) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |-> (x_pre_v_4 - ((a_pre ÷ b_pre ) * y_pre_v_4 ) ))
  **  ((x_pre) # Int  |-> y_pre_v_4)
|--
  (EX y_pre_v x_pre_v,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v)) <= 1) |] 
  &&  [| (y_pre_v = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v))
  ||
  (EX y_pre_v_2 x_pre_v_2,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_2 = 0) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX y_pre_v_3 x_pre_v_3,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_3)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
.

Definition exgcd_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |]
.

Definition exgcd_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 1)
  **  ((y_pre) # Int  |-> 0)
.

Definition exgcd_partial_solve_wit_1 := exgcd_partial_solve_wit_1_pure -> exgcd_partial_solve_wit_1_aux.

Definition exgcd_partial_solve_wit_2_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |]
.

Definition exgcd_partial_solve_wit_2_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (a_pre = 0) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> 0)
  **  ((y_pre) # Int  |-> 0)
.

Definition exgcd_partial_solve_wit_2 := exgcd_partial_solve_wit_2_pure -> exgcd_partial_solve_wit_2_aux.

Definition exgcd_partial_solve_wit_3_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |]
.

Definition exgcd_partial_solve_wit_3_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
|--
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (a_pre < 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |-> (-1))
  **  ((y_pre) # Int  |-> 0)
.

Definition exgcd_partial_solve_wit_3 := exgcd_partial_solve_wit_3_pure -> exgcd_partial_solve_wit_3_aux.

Definition exgcd_partial_solve_wit_4_pure := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| ((a_pre % ( b_pre ) ) <= INT_MAX) |] 
  &&  [| (INT_MIN < (a_pre % ( b_pre ) )) |]
.

Definition exgcd_partial_solve_wit_4_aux := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| ((a_pre % ( b_pre ) ) <= INT_MAX) |] 
  &&  [| (INT_MIN < (a_pre % ( b_pre ) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((y_pre) # Int  |->_)
  **  ((x_pre) # Int  |->_)
.

Definition exgcd_partial_solve_wit_4 := exgcd_partial_solve_wit_4_pure -> exgcd_partial_solve_wit_4_aux.

Definition exgcd_derive_Inter_by_Proof := 
forall (y_pre: Z) (x_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_)
|--
  ([| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((x_pre) # Int  |->_)
  **  ((y_pre) # Int  |->_))
  **
  (((EX y_pre_v_2 x_pre_v_2 retval_2,
  [| (retval_2 = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_2 ) + (b_pre * y_pre_v_2 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) <> 0) |] 
  &&  [| ((Zabs (x_pre_v_2)) <= ((Zabs (b_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |] 
  &&  [| ((Zabs (y_pre_v_2)) <= ((Zabs (a_pre)) ÷ (Zgcd (a_pre) (b_pre)) )) |]
  &&  ((x_pre) # Int  |-> x_pre_v_2)
  **  ((y_pre) # Int  |-> y_pre_v_2))
  ||
  (EX y_pre_v_3 x_pre_v_3 retval_2,
  [| (retval_2 = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_3 ) + (b_pre * y_pre_v_3 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| ((a_pre % ( b_pre ) ) = 0) |] 
  &&  [| (x_pre_v_3 = 0) |] 
  &&  [| ((Zabs (y_pre_v_3)) <= 1) |]
  &&  ((x_pre) # Int  |-> x_pre_v_3)
  **  ((y_pre) # Int  |-> y_pre_v_3))
  ||
  (EX y_pre_v_4 x_pre_v_4 retval_2,
  [| (retval_2 = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v_4 ) + (b_pre * y_pre_v_4 ) ) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| ((Zabs (x_pre_v_4)) <= 1) |] 
  &&  [| (y_pre_v_4 = 0) |]
  &&  ((x_pre) # Int  |-> x_pre_v_4)
  **  ((y_pre) # Int  |-> y_pre_v_4)))
  -*
  (EX y_pre_v x_pre_v retval,
  [| (retval = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (((a_pre * x_pre_v ) + (b_pre * y_pre_v ) ) = (Zgcd (a_pre) (b_pre))) |]
  &&  ((x_pre) # Int  |-> x_pre_v)
  **  ((y_pre) # Int  |-> y_pre_v)))
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_exgcd_safety_wit_1 : exgcd_safety_wit_1.
Axiom proof_of_exgcd_safety_wit_2 : exgcd_safety_wit_2.
Axiom proof_of_exgcd_safety_wit_3 : exgcd_safety_wit_3.
Axiom proof_of_exgcd_safety_wit_4 : exgcd_safety_wit_4.
Axiom proof_of_exgcd_safety_wit_5 : exgcd_safety_wit_5.
Axiom proof_of_exgcd_safety_wit_6 : exgcd_safety_wit_6.
Axiom proof_of_exgcd_safety_wit_7 : exgcd_safety_wit_7.
Axiom proof_of_exgcd_safety_wit_8 : exgcd_safety_wit_8.
Axiom proof_of_exgcd_safety_wit_9 : exgcd_safety_wit_9.
Axiom proof_of_exgcd_safety_wit_10 : exgcd_safety_wit_10.
Axiom proof_of_exgcd_safety_wit_11 : exgcd_safety_wit_11.
Axiom proof_of_exgcd_safety_wit_12 : exgcd_safety_wit_12.
Axiom proof_of_exgcd_safety_wit_13 : exgcd_safety_wit_13.
Axiom proof_of_exgcd_safety_wit_14 : exgcd_safety_wit_14.
Axiom proof_of_exgcd_safety_wit_15 : exgcd_safety_wit_15.
Axiom proof_of_exgcd_safety_wit_16 : exgcd_safety_wit_16.
Axiom proof_of_exgcd_safety_wit_17 : exgcd_safety_wit_17.
Axiom proof_of_exgcd_safety_wit_18 : exgcd_safety_wit_18.
Axiom proof_of_exgcd_safety_wit_19 : exgcd_safety_wit_19.
Axiom proof_of_exgcd_safety_wit_20 : exgcd_safety_wit_20.
Axiom proof_of_exgcd_return_wit_1_1 : exgcd_return_wit_1_1.
Axiom proof_of_exgcd_return_wit_1_2 : exgcd_return_wit_1_2.
Axiom proof_of_exgcd_return_wit_1_3 : exgcd_return_wit_1_3.
Axiom proof_of_exgcd_return_wit_2_1 : exgcd_return_wit_2_1.
Axiom proof_of_exgcd_return_wit_2_2 : exgcd_return_wit_2_2.
Axiom proof_of_exgcd_return_wit_2_3 : exgcd_return_wit_2_3.
Axiom proof_of_exgcd_partial_solve_wit_1_pure : exgcd_partial_solve_wit_1_pure.
Axiom proof_of_exgcd_partial_solve_wit_1 : exgcd_partial_solve_wit_1.
Axiom proof_of_exgcd_partial_solve_wit_2_pure : exgcd_partial_solve_wit_2_pure.
Axiom proof_of_exgcd_partial_solve_wit_2 : exgcd_partial_solve_wit_2.
Axiom proof_of_exgcd_partial_solve_wit_3_pure : exgcd_partial_solve_wit_3_pure.
Axiom proof_of_exgcd_partial_solve_wit_3 : exgcd_partial_solve_wit_3.
Axiom proof_of_exgcd_partial_solve_wit_4_pure : exgcd_partial_solve_wit_4_pure.
Axiom proof_of_exgcd_partial_solve_wit_4 : exgcd_partial_solve_wit_4.
Axiom proof_of_exgcd_derive_Inter_by_Proof : exgcd_derive_Inter_by_Proof.

End VC_Correct.
