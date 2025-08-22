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
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.

(*----- Function arr_sum -----*)

Definition arr_sum_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((ret + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + (Znth i l 0) )) |]
.

Definition arr_sum_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition arr_sum_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (sum ((sublist (0) (0) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (ret = (sum (l))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (store_int_array_missing_i_rec a_pre i_2 0 n_pre l )
.

(*----- Function arr_sum_do_while -----*)

Definition arr_sum_do_while_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_do_while_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_do_while_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((0 + (Znth 0 l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + (Znth 0 l 0) )) |]
.

Definition arr_sum_do_while_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "ret" ) )) # Int  |-> (0 + (Znth 0 l 0) ))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((0 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 1 )) |]
.

Definition arr_sum_do_while_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i <> n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((ret + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + (Znth i l 0) )) |]
.

Definition arr_sum_do_while_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i <> n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition arr_sum_do_while_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= (0 + 1 )) |] 
  &&  [| ((0 + 1 ) <= n_pre) |] 
  &&  [| ((0 + (Znth 0 l 0) ) = (sum ((sublist (0) ((0 + 1 )) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_do_while_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 <> n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_do_while_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i = n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (ret = (sum (l))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_do_while_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (store_int_array_missing_i_rec a_pre 0 0 n_pre l )
.

Definition arr_sum_do_while_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 <> n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (i_2 <> n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (store_int_array_missing_i_rec a_pre i_2 0 n_pre l )
.

(*----- Function arr_sum_for -----*)

Definition arr_sum_for_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_for_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_for_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((ret + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + (Znth i l 0) )) |]
.

Definition arr_sum_for_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition arr_sum_for_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (sum ((sublist (0) (0) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_for_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_for_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (ret = (sum (l))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_for_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (store_int_array_missing_i_rec a_pre i_2 0 n_pre l )
.

(*----- Function arr_sum_which_implies -----*)

Definition arr_sum_which_implies_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_which_implies_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_which_implies_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (store_int_array_missing_i_rec a_pre i 0 n_pre l )
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((ret + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + (Znth i l 0) )) |]
.

Definition arr_sum_which_implies_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_int_array a_pre n_pre l )
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition arr_sum_which_implies_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (sum ((sublist (0) (0) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_which_implies_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_which_implies_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (ret = (sum (l))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_which_implies_partial_solve_wit_1_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |]
.

Definition arr_sum_which_implies_partial_solve_wit_1_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_which_implies_partial_solve_wit_1 := arr_sum_which_implies_partial_solve_wit_1_pure -> arr_sum_which_implies_partial_solve_wit_1_aux.

Definition arr_sum_which_implies_partial_solve_wit_2_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (store_int_array_missing_i_rec a_pre i 0 n_pre l )
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |]
.

Definition arr_sum_which_implies_partial_solve_wit_2_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (store_int_array_missing_i_rec a_pre i_2 0 n_pre l )
|--
  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (store_int_array_missing_i_rec a_pre i_2 0 n_pre l )
.

Definition arr_sum_which_implies_partial_solve_wit_2 := arr_sum_which_implies_partial_solve_wit_2_pure -> arr_sum_which_implies_partial_solve_wit_2_aux.

Definition arr_sum_which_implies_which_implies_wit_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |]
  &&  (store_int_array a n_pre l )
|--
  (((a + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (store_int_array_missing_i_rec a i 0 n_pre l )
.

Definition arr_sum_which_implies_which_implies_wit_2 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (a: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |]
  &&  (((a + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (store_int_array_missing_i_rec a i 0 n_pre l )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |]
  &&  (store_int_array a n_pre l )
.

(*----- Function arr_sum_update -----*)

Definition arr_sum_update_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_update_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_update_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_int_array_missing_i_rec a_pre i 0 n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((ret + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + (Znth i l 0) )) |]
.

Definition arr_sum_update_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  (store_int_array_missing_i_rec a_pre i_2 0 n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
  **  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i_2 l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_update_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_int_array a_pre n_pre (app ((zeros ((i + 1 )))) ((sublist ((i + 1 )) (n_pre) (l)))) )
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition arr_sum_update_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 = (sum ((sublist (0) (0) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre (app ((zeros (0))) ((sublist (0) (n_pre) (l)))) )
.

Definition arr_sum_update_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre (app ((zeros ((i_2 + 1 )))) ((sublist ((i_2 + 1 )) (n_pre) (l)))) )
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre (app ((zeros ((i_2 + 1 )))) ((sublist ((i_2 + 1 )) (n_pre) (l)))) )
.

Definition arr_sum_update_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
|--
  [| (ret = (sum (l))) |]
  &&  (store_int_array a_pre n_pre (zeros (n_pre)) )
.

Definition arr_sum_update_partial_solve_wit_1_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_int_array a_pre n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |]
.

Definition arr_sum_update_partial_solve_wit_1_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
|--
  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
.

Definition arr_sum_update_partial_solve_wit_1 := arr_sum_update_partial_solve_wit_1_pure -> arr_sum_update_partial_solve_wit_1_aux.

Definition arr_sum_update_partial_solve_wit_2_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_int_array_missing_i_rec a_pre i 0 n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> 0)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |]
.

Definition arr_sum_update_partial_solve_wit_2_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array_missing_i_rec a_pre i_2 0 n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
  **  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> 0)
|--
  [| (0 <= i_2) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array_missing_i_rec a_pre i_2 0 n_pre (app ((zeros (i_2))) ((sublist (i_2) (n_pre) (l)))) )
  **  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> 0)
.

Definition arr_sum_update_partial_solve_wit_2 := arr_sum_update_partial_solve_wit_2_pure -> arr_sum_update_partial_solve_wit_2_aux.

Definition arr_sum_update_which_implies_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |]
  &&  (store_int_array a_pre n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
|--
  (store_int_array_missing_i_rec a_pre i 0 n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
.

Definition arr_sum_update_which_implies_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |]
  &&  (store_int_array_missing_i_rec a_pre i 0 n_pre (app ((zeros (i))) ((sublist (i) (n_pre) (l)))) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> 0)
|--
  (store_int_array a_pre n_pre (app ((zeros ((i + 1 )))) ((sublist ((i + 1 )) (n_pre) (l)))) )
.

(*----- Function arr_sum_pointer -----*)

Definition arr_sum_pointer_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_pointer_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_pointer_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "endp" ) )) # Ptr  |-> (a_pre + (n_pre * sizeof(INT) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_int_array a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition arr_sum_pointer_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i <> n_pre) |] 
  &&  [| ((((a_pre + (n_pre * sizeof(INT) ) ) - (a_pre + (i * sizeof(INT) ) ) ) ÷ sizeof(INT) ) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
  **  ((( &( "endp" ) )) # Ptr  |-> (a_pre + (n_pre * sizeof(INT) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((ret + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + (Znth i l 0) )) |]
.

Definition arr_sum_pointer_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| (i <> n_pre) |] 
  &&  [| ((((a_pre + (n_pre * sizeof(INT) ) ) - (a_pre + (i * sizeof(INT) ) ) ) ÷ sizeof(INT) ) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> (ret + (Znth i l 0) ))
  **  ((( &( "endp" ) )) # Ptr  |-> (a_pre + (n_pre * sizeof(INT) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition arr_sum_pointer_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (sum ((sublist (0) (0) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_pointer_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| ((((a_pre + (n_pre * sizeof(INT) ) ) - (a_pre + (i_2 * sizeof(INT) ) ) ) ÷ sizeof(INT) ) <> 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (i_2 <> n_pre) |] 
  &&  [| ((((a_pre + (n_pre * sizeof(INT) ) ) - (a_pre + (i_2 * sizeof(INT) ) ) ) ÷ sizeof(INT) ) <> 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_pointer_entail_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 <> n_pre) |] 
  &&  [| ((((a_pre + (n_pre * sizeof(INT) ) ) - (a_pre + (i_2 * sizeof(INT) ) ) ) ÷ sizeof(INT) ) <> 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((ret + (Znth i_2 l 0) ) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_pointer_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) (ret: Z) (i: Z) ,
  [| ((((a_pre + (n_pre * sizeof(INT) ) ) - (a_pre + (i * sizeof(INT) ) ) ) ÷ sizeof(INT) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (ret = (sum (l))) |]
  &&  (store_int_array a_pre n_pre l )
.

Definition arr_sum_pointer_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (ret: Z) (i_2: Z) ,
  [| (i_2 <> n_pre) |] 
  &&  [| ((((a_pre + (n_pre * sizeof(INT) ) ) - (a_pre + (i_2 * sizeof(INT) ) ) ) ÷ sizeof(INT) ) <> 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (store_int_array a_pre n_pre l )
|--
  [| (i_2 <> n_pre) |] 
  &&  [| ((((a_pre + (n_pre * sizeof(INT) ) ) - (a_pre + (i_2 * sizeof(INT) ) ) ) ÷ sizeof(INT) ) <> 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (ret = (sum ((sublist (0) (i_2) (l))))) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (store_int_array_missing_i_rec a_pre i_2 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_arr_sum_safety_wit_1 : arr_sum_safety_wit_1.
Axiom proof_of_arr_sum_safety_wit_2 : arr_sum_safety_wit_2.
Axiom proof_of_arr_sum_safety_wit_3 : arr_sum_safety_wit_3.
Axiom proof_of_arr_sum_safety_wit_4 : arr_sum_safety_wit_4.
Axiom proof_of_arr_sum_entail_wit_1 : arr_sum_entail_wit_1.
Axiom proof_of_arr_sum_entail_wit_2 : arr_sum_entail_wit_2.
Axiom proof_of_arr_sum_return_wit_1 : arr_sum_return_wit_1.
Axiom proof_of_arr_sum_partial_solve_wit_1 : arr_sum_partial_solve_wit_1.
Axiom proof_of_arr_sum_do_while_safety_wit_1 : arr_sum_do_while_safety_wit_1.
Axiom proof_of_arr_sum_do_while_safety_wit_2 : arr_sum_do_while_safety_wit_2.
Axiom proof_of_arr_sum_do_while_safety_wit_3 : arr_sum_do_while_safety_wit_3.
Axiom proof_of_arr_sum_do_while_safety_wit_4 : arr_sum_do_while_safety_wit_4.
Axiom proof_of_arr_sum_do_while_safety_wit_5 : arr_sum_do_while_safety_wit_5.
Axiom proof_of_arr_sum_do_while_safety_wit_6 : arr_sum_do_while_safety_wit_6.
Axiom proof_of_arr_sum_do_while_entail_wit_1 : arr_sum_do_while_entail_wit_1.
Axiom proof_of_arr_sum_do_while_entail_wit_2 : arr_sum_do_while_entail_wit_2.
Axiom proof_of_arr_sum_do_while_return_wit_1 : arr_sum_do_while_return_wit_1.
Axiom proof_of_arr_sum_do_while_partial_solve_wit_1 : arr_sum_do_while_partial_solve_wit_1.
Axiom proof_of_arr_sum_do_while_partial_solve_wit_2 : arr_sum_do_while_partial_solve_wit_2.
Axiom proof_of_arr_sum_for_safety_wit_1 : arr_sum_for_safety_wit_1.
Axiom proof_of_arr_sum_for_safety_wit_2 : arr_sum_for_safety_wit_2.
Axiom proof_of_arr_sum_for_safety_wit_3 : arr_sum_for_safety_wit_3.
Axiom proof_of_arr_sum_for_safety_wit_4 : arr_sum_for_safety_wit_4.
Axiom proof_of_arr_sum_for_entail_wit_1 : arr_sum_for_entail_wit_1.
Axiom proof_of_arr_sum_for_entail_wit_2 : arr_sum_for_entail_wit_2.
Axiom proof_of_arr_sum_for_return_wit_1 : arr_sum_for_return_wit_1.
Axiom proof_of_arr_sum_for_partial_solve_wit_1 : arr_sum_for_partial_solve_wit_1.
Axiom proof_of_arr_sum_which_implies_safety_wit_1 : arr_sum_which_implies_safety_wit_1.
Axiom proof_of_arr_sum_which_implies_safety_wit_2 : arr_sum_which_implies_safety_wit_2.
Axiom proof_of_arr_sum_which_implies_safety_wit_3 : arr_sum_which_implies_safety_wit_3.
Axiom proof_of_arr_sum_which_implies_safety_wit_4 : arr_sum_which_implies_safety_wit_4.
Axiom proof_of_arr_sum_which_implies_entail_wit_1 : arr_sum_which_implies_entail_wit_1.
Axiom proof_of_arr_sum_which_implies_entail_wit_2 : arr_sum_which_implies_entail_wit_2.
Axiom proof_of_arr_sum_which_implies_return_wit_1 : arr_sum_which_implies_return_wit_1.
Axiom proof_of_arr_sum_which_implies_partial_solve_wit_1_pure : arr_sum_which_implies_partial_solve_wit_1_pure.
Axiom proof_of_arr_sum_which_implies_partial_solve_wit_1 : arr_sum_which_implies_partial_solve_wit_1.
Axiom proof_of_arr_sum_which_implies_partial_solve_wit_2_pure : arr_sum_which_implies_partial_solve_wit_2_pure.
Axiom proof_of_arr_sum_which_implies_partial_solve_wit_2 : arr_sum_which_implies_partial_solve_wit_2.
Axiom proof_of_arr_sum_which_implies_which_implies_wit_1 : arr_sum_which_implies_which_implies_wit_1.
Axiom proof_of_arr_sum_which_implies_which_implies_wit_2 : arr_sum_which_implies_which_implies_wit_2.
Axiom proof_of_arr_sum_update_safety_wit_1 : arr_sum_update_safety_wit_1.
Axiom proof_of_arr_sum_update_safety_wit_2 : arr_sum_update_safety_wit_2.
Axiom proof_of_arr_sum_update_safety_wit_3 : arr_sum_update_safety_wit_3.
Axiom proof_of_arr_sum_update_safety_wit_4 : arr_sum_update_safety_wit_4.
Axiom proof_of_arr_sum_update_safety_wit_5 : arr_sum_update_safety_wit_5.
Axiom proof_of_arr_sum_update_entail_wit_1 : arr_sum_update_entail_wit_1.
Axiom proof_of_arr_sum_update_entail_wit_2 : arr_sum_update_entail_wit_2.
Axiom proof_of_arr_sum_update_return_wit_1 : arr_sum_update_return_wit_1.
Axiom proof_of_arr_sum_update_partial_solve_wit_1_pure : arr_sum_update_partial_solve_wit_1_pure.
Axiom proof_of_arr_sum_update_partial_solve_wit_1 : arr_sum_update_partial_solve_wit_1.
Axiom proof_of_arr_sum_update_partial_solve_wit_2_pure : arr_sum_update_partial_solve_wit_2_pure.
Axiom proof_of_arr_sum_update_partial_solve_wit_2 : arr_sum_update_partial_solve_wit_2.
Axiom proof_of_arr_sum_update_which_implies_wit_1 : arr_sum_update_which_implies_wit_1.
Axiom proof_of_arr_sum_update_which_implies_wit_2 : arr_sum_update_which_implies_wit_2.
Axiom proof_of_arr_sum_pointer_safety_wit_1 : arr_sum_pointer_safety_wit_1.
Axiom proof_of_arr_sum_pointer_safety_wit_2 : arr_sum_pointer_safety_wit_2.
Axiom proof_of_arr_sum_pointer_safety_wit_3 : arr_sum_pointer_safety_wit_3.
Axiom proof_of_arr_sum_pointer_safety_wit_4 : arr_sum_pointer_safety_wit_4.
Axiom proof_of_arr_sum_pointer_safety_wit_5 : arr_sum_pointer_safety_wit_5.
Axiom proof_of_arr_sum_pointer_entail_wit_1 : arr_sum_pointer_entail_wit_1.
Axiom proof_of_arr_sum_pointer_entail_wit_2 : arr_sum_pointer_entail_wit_2.
Axiom proof_of_arr_sum_pointer_entail_wit_3 : arr_sum_pointer_entail_wit_3.
Axiom proof_of_arr_sum_pointer_return_wit_1 : arr_sum_pointer_return_wit_1.
Axiom proof_of_arr_sum_pointer_partial_solve_wit_1 : arr_sum_pointer_partial_solve_wit_1.

End VC_Correct.
