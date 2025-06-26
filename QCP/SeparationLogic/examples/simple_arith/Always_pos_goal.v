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
Require Import Apos_lib.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.

(*----- Function Always_positive_simple -----*)

Definition Always_positive_simple_safety_wit_1 := 
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

Definition Always_positive_simple_safety_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
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

Definition Always_positive_simple_safety_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (((b_pre * b_pre ) <> (-9223372036854775808)) \/ (4 <> (-1))) |] 
  &&  [| (4 <> 0) |]
.

Definition Always_positive_simple_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((b_pre * b_pre ) <= 9223372036854775807) |] 
  &&  [| ((-9223372036854775808) <= (b_pre * b_pre )) |]
.

Definition Always_positive_simple_safety_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition Always_positive_simple_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre * c_pre ) <= 9223372036854775807) |] 
  &&  [| ((-9223372036854775808) <= (a_pre * c_pre )) |]
.

Definition Always_positive_simple_safety_wit_7 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (((b_pre * b_pre ) ÷ 4 ) >= (a_pre * c_pre )) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_simple_safety_wit_8 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre )) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_simple_safety_wit_9 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre > 0) |] 
  &&  [| (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre )) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition Always_positive_simple_safety_wit_10 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <= 0) |] 
  &&  [| (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre )) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_simple_return_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 = (Always_pos (a_pre) (b_pre) (c_pre))) |]
  &&  emp
.

Definition Always_positive_simple_return_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (((b_pre * b_pre ) ÷ 4 ) >= (a_pre * c_pre )) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 = (Always_pos (a_pre) (b_pre) (c_pre))) |]
  &&  emp
.

Definition Always_positive_simple_return_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre > 0) |] 
  &&  [| (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre )) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (1 = (Always_pos (a_pre) (b_pre) (c_pre))) |]
  &&  emp
.

Definition Always_positive_simple_return_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <= 0) |] 
  &&  [| (((b_pre * b_pre ) ÷ 4 ) < (a_pre * c_pre )) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 = (Always_pos (a_pre) (b_pre) (c_pre))) |]
  &&  emp
.

(*----- Function Always_positive -----*)

Definition Always_positive_safety_wit_1 := 
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

Definition Always_positive_safety_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
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

Definition Always_positive_safety_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |->_)
  **  ((( &( "delta0" ) )) # Int64  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((b_pre * b_pre ) <= 9223372036854775807) |] 
  &&  [| ((-9223372036854775808) <= (b_pre * b_pre )) |]
.

Definition Always_positive_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre * c_pre ) <= 9223372036854775807) |] 
  &&  [| ((-9223372036854775808) <= (a_pre * c_pre )) |]
.

Definition Always_positive_safety_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| ((a_pre * c_pre ) <= 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_7 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition Always_positive_safety_wit_8 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((delta1 - delta2 ) <= 9223372036854775807) |] 
  &&  [| ((-9223372036854775808) <= (delta1 - delta2 )) |]
.

Definition Always_positive_safety_wit_9 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((d - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d - 1 )) |]
.

Definition Always_positive_safety_wit_10 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition Always_positive_safety_wit_11 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (d - 1 ))
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_12 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| ((d - 1 ) = 0) |] 
  &&  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (d - 1 ))
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_13 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| ((delta1 - delta2 ) < 0) |] 
  &&  [| ((d - 1 ) = 0) |] 
  &&  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (d - 1 ))
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| False |]
.

Definition Always_positive_safety_wit_14 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| ((delta1 - delta2 ) >= 0) |] 
  &&  [| ((d - 1 ) = 0) |] 
  &&  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (d - 1 ))
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_15 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| ((a_pre * c_pre ) <= 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_16 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (0 <> 0) |] 
  &&  [| ((a_pre * c_pre ) <= 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| False |]
.

Definition Always_positive_safety_wit_17 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (delta2 > delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_18 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (d = 0) |] 
  &&  [| (delta2 > delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| False |]
.

Definition Always_positive_safety_wit_19 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| ((delta1 - delta2 ) >= 0) |] 
  &&  [| ((d - 1 ) = 0) |] 
  &&  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_20 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (0 <> 0) |] 
  &&  [| ((delta1 - delta2 ) >= 0) |] 
  &&  [| ((d - 1 ) = 0) |] 
  &&  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| False |]
.

Definition Always_positive_safety_wit_21 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (0 = 0) |] 
  &&  [| ((a_pre * c_pre ) <= 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta2" ) )) # Int64  |-> (a_pre * c_pre ))
  **  ((( &( "delta1" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "delta0" ) )) # Int64  |-> (b_pre * b_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_22 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (0 = 0) |] 
  &&  [| ((delta1 - delta2 ) >= 0) |] 
  &&  [| ((d - 1 ) = 0) |] 
  &&  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> (delta1 - delta2 ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_23 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (d <> 0) |] 
  &&  [| (delta2 > delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_safety_wit_24 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (a_pre > 0) |] 
  &&  [| (d <> 0) |] 
  &&  [| (delta2 > delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition Always_positive_safety_wit_25 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (a_pre <= 0) |] 
  &&  [| (d <> 0) |] 
  &&  [| (delta2 > delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "delta0" ) )) # Int64  |-> delta0)
  **  ((( &( "delta2" ) )) # Int64  |-> delta2)
  **  ((( &( "delta1" ) )) # Int64  |-> delta1)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Always_positive_entail_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 < 4) |] 
  &&  [| (4 <= 4) |] 
  &&  [| ((b_pre * b_pre ) = (b_pre * b_pre )) |] 
  &&  [| ((a_pre * c_pre ) = (a_pre * c_pre )) |] 
  &&  [| ((b_pre * b_pre ) = ((b_pre * b_pre ) + ((4 - 4 ) * (a_pre * c_pre ) ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
.

Definition Always_positive_entail_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| ((d - 1 ) <> 0) |] 
  &&  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 < (d - 1 )) |] 
  &&  [| ((d - 1 ) <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = ((delta1 - delta2 ) + ((4 - (d - 1 ) ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
.

Definition Always_positive_return_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (a_pre = 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 = (Always_pos (a_pre) (b_pre) (c_pre))) |]
  &&  emp
.

Definition Always_positive_return_wit_2_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (0 = 0) |] 
  &&  [| ((delta1 - delta2 ) >= 0) |] 
  &&  [| ((d - 1 ) = 0) |] 
  &&  [| (delta2 <= delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 = (Always_pos (a_pre) (b_pre) (c_pre))) |]
  &&  emp
.

Definition Always_positive_return_wit_2_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) ,
  [| (0 = 0) |] 
  &&  [| ((a_pre * c_pre ) <= 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 = (Always_pos (a_pre) (b_pre) (c_pre))) |]
  &&  emp
.

Definition Always_positive_return_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (a_pre > 0) |] 
  &&  [| (d <> 0) |] 
  &&  [| (delta2 > delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (1 = (Always_pos (a_pre) (b_pre) (c_pre))) |]
  &&  emp
.

Definition Always_positive_return_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (delta1: Z) (delta2: Z) (delta0: Z) (d: Z) ,
  [| (a_pre <= 0) |] 
  &&  [| (d <> 0) |] 
  &&  [| (delta2 > delta1) |] 
  &&  [| (0 < d) |] 
  &&  [| (d <= 4) |] 
  &&  [| (delta0 = (b_pre * b_pre )) |] 
  &&  [| (delta2 = (a_pre * c_pre )) |] 
  &&  [| (delta0 = (delta1 + ((4 - d ) * delta2 ) )) |] 
  &&  [| ((a_pre * c_pre ) > 0) |] 
  &&  [| (a_pre <> 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < c_pre) |] 
  &&  [| (c_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 = (Always_pos (a_pre) (b_pre) (c_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_Always_positive_simple_safety_wit_1 : Always_positive_simple_safety_wit_1.
Axiom proof_of_Always_positive_simple_safety_wit_2 : Always_positive_simple_safety_wit_2.
Axiom proof_of_Always_positive_simple_safety_wit_3 : Always_positive_simple_safety_wit_3.
Axiom proof_of_Always_positive_simple_safety_wit_4 : Always_positive_simple_safety_wit_4.
Axiom proof_of_Always_positive_simple_safety_wit_5 : Always_positive_simple_safety_wit_5.
Axiom proof_of_Always_positive_simple_safety_wit_6 : Always_positive_simple_safety_wit_6.
Axiom proof_of_Always_positive_simple_safety_wit_7 : Always_positive_simple_safety_wit_7.
Axiom proof_of_Always_positive_simple_safety_wit_8 : Always_positive_simple_safety_wit_8.
Axiom proof_of_Always_positive_simple_safety_wit_9 : Always_positive_simple_safety_wit_9.
Axiom proof_of_Always_positive_simple_safety_wit_10 : Always_positive_simple_safety_wit_10.
Axiom proof_of_Always_positive_simple_return_wit_1 : Always_positive_simple_return_wit_1.
Axiom proof_of_Always_positive_simple_return_wit_2 : Always_positive_simple_return_wit_2.
Axiom proof_of_Always_positive_simple_return_wit_3 : Always_positive_simple_return_wit_3.
Axiom proof_of_Always_positive_simple_return_wit_4 : Always_positive_simple_return_wit_4.
Axiom proof_of_Always_positive_safety_wit_1 : Always_positive_safety_wit_1.
Axiom proof_of_Always_positive_safety_wit_2 : Always_positive_safety_wit_2.
Axiom proof_of_Always_positive_safety_wit_3 : Always_positive_safety_wit_3.
Axiom proof_of_Always_positive_safety_wit_4 : Always_positive_safety_wit_4.
Axiom proof_of_Always_positive_safety_wit_5 : Always_positive_safety_wit_5.
Axiom proof_of_Always_positive_safety_wit_6 : Always_positive_safety_wit_6.
Axiom proof_of_Always_positive_safety_wit_7 : Always_positive_safety_wit_7.
Axiom proof_of_Always_positive_safety_wit_8 : Always_positive_safety_wit_8.
Axiom proof_of_Always_positive_safety_wit_9 : Always_positive_safety_wit_9.
Axiom proof_of_Always_positive_safety_wit_10 : Always_positive_safety_wit_10.
Axiom proof_of_Always_positive_safety_wit_11 : Always_positive_safety_wit_11.
Axiom proof_of_Always_positive_safety_wit_12 : Always_positive_safety_wit_12.
Axiom proof_of_Always_positive_safety_wit_13 : Always_positive_safety_wit_13.
Axiom proof_of_Always_positive_safety_wit_14 : Always_positive_safety_wit_14.
Axiom proof_of_Always_positive_safety_wit_15 : Always_positive_safety_wit_15.
Axiom proof_of_Always_positive_safety_wit_16 : Always_positive_safety_wit_16.
Axiom proof_of_Always_positive_safety_wit_17 : Always_positive_safety_wit_17.
Axiom proof_of_Always_positive_safety_wit_18 : Always_positive_safety_wit_18.
Axiom proof_of_Always_positive_safety_wit_19 : Always_positive_safety_wit_19.
Axiom proof_of_Always_positive_safety_wit_20 : Always_positive_safety_wit_20.
Axiom proof_of_Always_positive_safety_wit_21 : Always_positive_safety_wit_21.
Axiom proof_of_Always_positive_safety_wit_22 : Always_positive_safety_wit_22.
Axiom proof_of_Always_positive_safety_wit_23 : Always_positive_safety_wit_23.
Axiom proof_of_Always_positive_safety_wit_24 : Always_positive_safety_wit_24.
Axiom proof_of_Always_positive_safety_wit_25 : Always_positive_safety_wit_25.
Axiom proof_of_Always_positive_entail_wit_1 : Always_positive_entail_wit_1.
Axiom proof_of_Always_positive_entail_wit_2 : Always_positive_entail_wit_2.
Axiom proof_of_Always_positive_return_wit_1 : Always_positive_return_wit_1.
Axiom proof_of_Always_positive_return_wit_2_1 : Always_positive_return_wit_2_1.
Axiom proof_of_Always_positive_return_wit_2_2 : Always_positive_return_wit_2_2.
Axiom proof_of_Always_positive_return_wit_3 : Always_positive_return_wit_3.
Axiom proof_of_Always_positive_return_wit_4 : Always_positive_return_wit_4.

End VC_Correct.
