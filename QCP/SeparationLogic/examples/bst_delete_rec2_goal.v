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
Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE Require Import bst_strategy_goal.
From SimpleC.EE Require Import bst_strategy_proof.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function get_pre -----*)

Definition get_pre_safety_wit_1 := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) ,
  [| (t_pre_v <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  (store_tree t_pre_v_right t_right )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition get_pre_return_wit_1 := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) ,
  [| (t_pre_v_right = 0) |] 
  &&  [| (t_pre_v <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |]
  &&  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  (store_tree t_pre_v_right t_right )
|--
  EX retval_v_left retval_v_right ret_left t_pt retval_v_value retval_v_key retval_v,
  [| (retval_v <> 0) |] 
  &&  [| (INT_MIN <= retval_v_key) |] 
  &&  [| (retval_v_key <= INT_MAX) |] 
  &&  [| (((find_pre (t_left) (t_key) (t_value) (t_right)).(k) ) = retval_v_key) |] 
  &&  [| (((find_pre (t_left) (t_key) (t_value) (t_right)).(v) ) = retval_v_value) |] 
  &&  [| (((find_pre (t_left) (t_key) (t_value) (t_right)).(pt) ) = t_pt) |] 
  &&  [| (((find_pre (t_left) (t_key) (t_value) (t_right)).(l_tree) ) = ret_left) |] 
  &&  [| (retval_v_right = 0) |]
  &&  ((t_pre) # Ptr  |-> retval_v)
  **  ((&((retval_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((retval_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((retval_v)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right)
  **  (store_ptb t_pre t_pre t_pt )
  **  ((&((retval_v)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left)
  **  (store_tree retval_v_left ret_left )
.

Definition get_pre_return_wit_2 := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) (l0: tree) (r0: tree) (t_v: Z) (t_k: Z) (retval_v_left_2: Z) (retval_v_right_2: Z) (ret_left_2: tree) (t_pt_2: partial_tree) (retval_v_value_2: Z) (retval_v_key_2: Z) (retval_v_2: Z) (retval: Z) ,
  [| (retval_v_2 <> 0) |] 
  &&  [| (INT_MIN <= retval_v_key_2) |] 
  &&  [| (retval_v_key_2 <= INT_MAX) |] 
  &&  [| (((find_pre (l0) (t_k) (t_v) (r0)).(k) ) = retval_v_key_2) |] 
  &&  [| (((find_pre (l0) (t_k) (t_v) (r0)).(v) ) = retval_v_value_2) |] 
  &&  [| (((find_pre (l0) (t_k) (t_v) (r0)).(pt) ) = t_pt_2) |] 
  &&  [| (((find_pre (l0) (t_k) (t_v) (r0)).(l_tree) ) = ret_left_2) |] 
  &&  [| (retval_v_right_2 = 0) |] 
  &&  [| (INT_MIN <= t_k) |] 
  &&  [| (t_k <= INT_MAX) |] 
  &&  [| (t_right = (make_tree (l0) (t_k) (t_v) (r0))) |] 
  &&  [| (t_pre_v_right <> 0) |] 
  &&  [| (t_pre_v <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |]
  &&  ((retval) # Ptr  |-> retval_v_2)
  **  ((&((retval_v_2)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key_2)
  **  ((&((retval_v_2)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value_2)
  **  ((&((retval_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right_2)
  **  (store_ptb retval &((t_pre_v)  # "tree" ->ₛ "right") t_pt_2 )
  **  ((&((retval_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left_2)
  **  (store_tree retval_v_left_2 ret_left_2 )
  **  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
|--
  EX retval_v_left retval_v_right ret_left t_pt retval_v_value retval_v_key retval_v,
  [| (retval_v <> 0) |] 
  &&  [| (INT_MIN <= retval_v_key) |] 
  &&  [| (retval_v_key <= INT_MAX) |] 
  &&  [| (((find_pre (t_left) (t_key) (t_value) (t_right)).(k) ) = retval_v_key) |] 
  &&  [| (((find_pre (t_left) (t_key) (t_value) (t_right)).(v) ) = retval_v_value) |] 
  &&  [| (((find_pre (t_left) (t_key) (t_value) (t_right)).(pt) ) = t_pt) |] 
  &&  [| (((find_pre (t_left) (t_key) (t_value) (t_right)).(l_tree) ) = ret_left) |] 
  &&  [| (retval_v_right = 0) |]
  &&  ((retval) # Ptr  |-> retval_v)
  **  ((&((retval_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((retval_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((retval_v)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right)
  **  (store_ptb retval t_pre t_pt )
  **  ((&((retval_v)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left)
  **  (store_tree retval_v_left ret_left )
.

Definition get_pre_partial_solve_wit_1_pure := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) ,
  [| (t_pre_v_right <> 0) |] 
  &&  [| (t_pre_v <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  (store_tree t_pre_v_right t_right )
|--
  [| (t_pre_v_right <> 0) |]
.

Definition get_pre_partial_solve_wit_1_aux := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) ,
  [| (t_pre_v_right <> 0) |] 
  &&  [| (t_pre_v <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |]
  &&  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  (store_tree t_pre_v_right t_right )
|--
  [| (t_pre_v_right <> 0) |] 
  &&  [| (t_pre_v_right <> 0) |] 
  &&  [| (t_pre_v <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |]
  &&  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  (store_tree t_pre_v_right t_right )
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
.

Definition get_pre_partial_solve_wit_1 := get_pre_partial_solve_wit_1_pure -> get_pre_partial_solve_wit_1_aux.

Definition get_pre_partial_solve_wit_2_pure := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) (t_v_right_right: Z) (t_v_right_left: Z) (l0: tree) (r0: tree) (t_v: Z) (t_k: Z) ,
  [| (INT_MIN <= t_k) |] 
  &&  [| (t_k <= INT_MAX) |] 
  &&  [| (t_right = (make_tree (l0) (t_k) (t_v) (r0))) |] 
  &&  [| (t_pre_v_right <> 0) |] 
  &&  [| (t_pre_v <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "key")) # Int  |-> t_k)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "value")) # Int  |-> t_v)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_right_left)
  **  (store_tree t_v_right_left l0 )
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right_right)
  **  (store_tree t_v_right_right r0 )
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
|--
  [| (t_pre_v_right <> 0) |] 
  &&  [| (INT_MIN <= t_k) |] 
  &&  [| (t_k <= INT_MAX) |]
.

Definition get_pre_partial_solve_wit_2_aux := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) (t_v_right_right: Z) (t_v_right_left: Z) (l0: tree) (r0: tree) (t_v: Z) (t_k: Z) ,
  [| (INT_MIN <= t_k) |] 
  &&  [| (t_k <= INT_MAX) |] 
  &&  [| (t_right = (make_tree (l0) (t_k) (t_v) (r0))) |] 
  &&  [| (t_pre_v_right <> 0) |] 
  &&  [| (t_pre_v <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |]
  &&  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "key")) # Int  |-> t_k)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "value")) # Int  |-> t_v)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_right_left)
  **  (store_tree t_v_right_left l0 )
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right_right)
  **  (store_tree t_v_right_right r0 )
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
|--
  [| (t_pre_v_right <> 0) |] 
  &&  [| (INT_MIN <= t_k) |] 
  &&  [| (t_k <= INT_MAX) |] 
  &&  [| (INT_MIN <= t_k) |] 
  &&  [| (t_k <= INT_MAX) |] 
  &&  [| (t_right = (make_tree (l0) (t_k) (t_v) (r0))) |] 
  &&  [| (t_pre_v_right <> 0) |] 
  &&  [| (t_pre_v <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |]
  &&  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "key")) # Int  |-> t_k)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "value")) # Int  |-> t_v)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_right_left)
  **  (store_tree t_v_right_left l0 )
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right_right)
  **  (store_tree t_v_right_right r0 )
  **  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
.

Definition get_pre_partial_solve_wit_2 := get_pre_partial_solve_wit_2_pure -> get_pre_partial_solve_wit_2_aux.

Definition get_pre_which_implies_wit_1 := 
forall (t_right: tree) (t: Z) (t_v_2: Z) (t_v_right: Z) ,
  [| (t_v_right <> 0) |]
  &&  ((t) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right)
  **  (store_tree t_v_right t_right )
|--
  EX t_v_right_right t_v_right_left l0 r0 t_v t_k,
  [| (INT_MIN <= t_k) |] 
  &&  [| (t_k <= INT_MAX) |] 
  &&  [| (t_right = (make_tree (l0) (t_k) (t_v) (r0))) |]
  &&  ((t) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right)
  **  ((&((t_v_right)  # "tree" ->ₛ "key")) # Int  |-> t_k)
  **  ((&((t_v_right)  # "tree" ->ₛ "value")) # Int  |-> t_v)
  **  ((&((t_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_right_left)
  **  (store_tree t_v_right_left l0 )
  **  ((&((t_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right_right)
  **  (store_tree t_v_right_right r0 )
.

(*----- Function delete -----*)

Definition delete_safety_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition delete_safety_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition delete_return_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_2: Z) ,
  [| (b_pre_v_2 = 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (store_tree b_pre_v_2 tr )
|--
  EX b_pre_v,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr)) )
.

Definition delete_return_wit_2_1 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_2: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (l0': tree) (r0': tree) (p_l_v: Z) (p_l_k: Z) (retval_v_left: Z) (retval_v_right: Z) (ret_left: tree) (t_pt: partial_tree) (retval_v_value: Z) (retval_v_key: Z) (retval_v: Z) (retval: Z) ,
  [| (retval_v <> 0) |] 
  &&  [| (INT_MIN <= retval_v_key) |] 
  &&  [| (retval_v_key <= INT_MAX) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(k) ) = retval_v_key) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(v) ) = retval_v_value) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(pt) ) = t_pt) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(l_tree) ) = ret_left) |] 
  &&  [| (retval_v_right = 0) |] 
  &&  [| (INT_MIN <= p_l_k) |] 
  &&  [| (p_l_k <= INT_MAX) |] 
  &&  [| (l0 = (make_tree (l0') (p_l_k) (p_l_v) (r0'))) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v_2 <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((retval) # Ptr  |-> retval_v_left)
  **  (store_ptb retval &((b_pre_v_2)  # "tree" ->ₛ "left") t_pt )
  **  (store_tree retval_v_left ret_left )
  **  ((&((b_pre_v_2)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((b_pre_v_2)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((b_pre_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v_2)
|--
  EX b_pre_v,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr)) )
.

Definition delete_return_wit_2_2 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_2: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_left = 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v_2 <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree p_left l0 )
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> p_right)
|--
  EX b_pre_v,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr)) )
.

Definition delete_return_wit_2_3 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_3: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (b_pre_v_2: Z) ,
  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v_3 <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v_3)  # "tree" ->ₛ "right")) # Ptr  |-> b_pre_v_2)
  **  (store_tree b_pre_v_2 (tree_delete' (x_pre) (r0)) )
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((b_pre) # Ptr  |-> b_pre_v_3)
|--
  EX b_pre_v,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr)) )
.

Definition delete_return_wit_2_4 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_3: Z) (p_right: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (b_pre_v_2: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v_3 <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v_3)  # "tree" ->ₛ "left")) # Ptr  |-> b_pre_v_2)
  **  (store_tree b_pre_v_2 (tree_delete' (x_pre) (l0)) )
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v_3)
|--
  EX b_pre_v,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr)) )
.

Definition delete_partial_solve_wit_1_pure := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) ,
  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr )
|--
  [| (b_pre_v <> 0) |]
.

Definition delete_partial_solve_wit_1_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) ,
  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr )
|--
  [| (b_pre_v <> 0) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_pre_v tr )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_partial_solve_wit_1 := delete_partial_solve_wit_1_pure -> delete_partial_solve_wit_1_aux.

Definition delete_partial_solve_wit_2_pure := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition delete_partial_solve_wit_2_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (x_pre < p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_partial_solve_wit_2 := delete_partial_solve_wit_2_pure -> delete_partial_solve_wit_2_aux.

Definition delete_partial_solve_wit_3_pure := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition delete_partial_solve_wit_3_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_partial_solve_wit_3 := delete_partial_solve_wit_3_pure -> delete_partial_solve_wit_3_aux.

Definition delete_partial_solve_wit_4 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_left = 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> p_right)
|--
  [| (p_left = 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_left l0 )
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> p_right)
.

Definition delete_partial_solve_wit_5_pure := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (p_left <> 0) |]
.

Definition delete_partial_solve_wit_5_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (p_left <> 0) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_partial_solve_wit_5 := delete_partial_solve_wit_5_pure -> delete_partial_solve_wit_5_aux.

Definition delete_partial_solve_wit_6_pure := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (p_left_right: Z) (p_left_left: Z) (l0': tree) (r0': tree) (p_l_v: Z) (p_l_k: Z) ,
  [| (INT_MIN <= p_l_k) |] 
  &&  [| (p_l_k <= INT_MAX) |] 
  &&  [| (l0 = (make_tree (l0') (p_l_k) (p_l_v) (r0'))) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "pre" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p_left)  # "tree" ->ₛ "key")) # Int  |-> p_l_k)
  **  ((&((p_left)  # "tree" ->ₛ "value")) # Int  |-> p_l_v)
  **  ((&((p_left)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_left)
  **  (store_tree p_left_left l0' )
  **  ((&((p_left)  # "tree" ->ₛ "right")) # Ptr  |-> p_left_right)
  **  (store_tree p_left_right r0' )
  **  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (p_left <> 0) |] 
  &&  [| (INT_MIN <= p_l_k) |] 
  &&  [| (p_l_k <= INT_MAX) |]
.

Definition delete_partial_solve_wit_6_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (p_left_right: Z) (p_left_left: Z) (l0': tree) (r0': tree) (p_l_v: Z) (p_l_k: Z) ,
  [| (INT_MIN <= p_l_k) |] 
  &&  [| (p_l_k <= INT_MAX) |] 
  &&  [| (l0 = (make_tree (l0') (p_l_k) (p_l_v) (r0'))) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p_left)  # "tree" ->ₛ "key")) # Int  |-> p_l_k)
  **  ((&((p_left)  # "tree" ->ₛ "value")) # Int  |-> p_l_v)
  **  ((&((p_left)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_left)
  **  (store_tree p_left_left l0' )
  **  ((&((p_left)  # "tree" ->ₛ "right")) # Ptr  |-> p_left_right)
  **  (store_tree p_left_right r0' )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (p_left <> 0) |] 
  &&  [| (INT_MIN <= p_l_k) |] 
  &&  [| (p_l_k <= INT_MAX) |] 
  &&  [| (INT_MIN <= p_l_k) |] 
  &&  [| (p_l_k <= INT_MAX) |] 
  &&  [| (l0 = (make_tree (l0') (p_l_k) (p_l_v) (r0'))) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p_left)  # "tree" ->ₛ "key")) # Int  |-> p_l_k)
  **  ((&((p_left)  # "tree" ->ₛ "value")) # Int  |-> p_l_v)
  **  ((&((p_left)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_left)
  **  (store_tree p_left_left l0' )
  **  ((&((p_left)  # "tree" ->ₛ "right")) # Ptr  |-> p_left_right)
  **  (store_tree p_left_right r0' )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_partial_solve_wit_6 := delete_partial_solve_wit_6_pure -> delete_partial_solve_wit_6_aux.

Definition delete_partial_solve_wit_7 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (l0': tree) (r0': tree) (p_l_v: Z) (p_l_k: Z) (retval_v_left: Z) (retval_v_right: Z) (ret_left: tree) (t_pt: partial_tree) (retval_v_value: Z) (retval_v_key: Z) (retval_v: Z) (retval: Z) ,
  [| (retval_v <> 0) |] 
  &&  [| (INT_MIN <= retval_v_key) |] 
  &&  [| (retval_v_key <= INT_MAX) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(k) ) = retval_v_key) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(v) ) = retval_v_value) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(pt) ) = t_pt) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(l_tree) ) = ret_left) |] 
  &&  [| (retval_v_right = 0) |] 
  &&  [| (INT_MIN <= p_l_k) |] 
  &&  [| (p_l_k <= INT_MAX) |] 
  &&  [| (l0 = (make_tree (l0') (p_l_k) (p_l_v) (r0'))) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((retval) # Ptr  |-> retval_v_left)
  **  ((&((retval_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((retval_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((retval_v)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right)
  **  (store_ptb retval &((b_pre_v)  # "tree" ->ₛ "left") t_pt )
  **  ((&((retval_v)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left)
  **  (store_tree retval_v_left ret_left )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (retval_v <> 0) |] 
  &&  [| (INT_MIN <= retval_v_key) |] 
  &&  [| (retval_v_key <= INT_MAX) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(k) ) = retval_v_key) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(v) ) = retval_v_value) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(pt) ) = t_pt) |] 
  &&  [| (((find_pre (l0') (p_l_k) (p_l_v) (r0')).(l_tree) ) = ret_left) |] 
  &&  [| (retval_v_right = 0) |] 
  &&  [| (INT_MIN <= p_l_k) |] 
  &&  [| (p_l_k <= INT_MAX) |] 
  &&  [| (l0 = (make_tree (l0') (p_l_k) (p_l_v) (r0'))) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((retval_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((retval_v)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left)
  **  ((&((retval_v)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right)
  **  ((retval) # Ptr  |-> retval_v_left)
  **  (store_ptb retval &((b_pre_v)  # "tree" ->ₛ "left") t_pt )
  **  (store_tree retval_v_left ret_left )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_which_implies_wit_1 := 
forall (tr: tree) (p: Z) ,
  [| (p <> 0) |]
  &&  (store_tree p tr )
|--
  EX p_right p_left l0 p_value r0 p_key,
  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition delete_which_implies_wit_2 := 
forall (l0: tree) (p: Z) (p_left: Z) ,
  [| (p_left <> 0) |]
  &&  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
|--
  EX p_left_right p_left_left l0' r0' p_l_v p_l_k,
  [| (INT_MIN <= p_l_k) |] 
  &&  [| (p_l_k <= INT_MAX) |] 
  &&  [| (l0 = (make_tree (l0') (p_l_k) (p_l_v) (r0'))) |]
  &&  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p_left)  # "tree" ->ₛ "key")) # Int  |-> p_l_k)
  **  ((&((p_left)  # "tree" ->ₛ "value")) # Int  |-> p_l_v)
  **  ((&((p_left)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_left)
  **  (store_tree p_left_left l0' )
  **  ((&((p_left)  # "tree" ->ₛ "right")) # Ptr  |-> p_left_right)
  **  (store_tree p_left_right r0' )
.

Definition delete_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (b_pre: Z) (m: mapping) ,
  EX b_pre_v,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_map b_pre_v m )
|--
EX (tr: tree) ,
  (EX b_pre_v_3,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v_3)
  **  (store_tree b_pre_v_3 tr ))
  **
  ((EX b_pre_v_4,
  ((b_pre) # Ptr  |-> b_pre_v_4)
  **  (store_tree b_pre_v_4 (tree_delete' (x_pre) (tr)) ))
  -*
  (EX b_pre_v_2,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (store_map b_pre_v_2 (map_delete (x_pre) (m)) )))
.

Module Type VC_Correct.

Include bst_Strategy_Correct.
Include common_Strategy_Correct.

Axiom proof_of_get_pre_safety_wit_1 : get_pre_safety_wit_1.
Axiom proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Axiom proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Axiom proof_of_get_pre_partial_solve_wit_1_pure : get_pre_partial_solve_wit_1_pure.
Axiom proof_of_get_pre_partial_solve_wit_1 : get_pre_partial_solve_wit_1.
Axiom proof_of_get_pre_partial_solve_wit_2_pure : get_pre_partial_solve_wit_2_pure.
Axiom proof_of_get_pre_partial_solve_wit_2 : get_pre_partial_solve_wit_2.
Axiom proof_of_get_pre_which_implies_wit_1 : get_pre_which_implies_wit_1.
Axiom proof_of_delete_safety_wit_1 : delete_safety_wit_1.
Axiom proof_of_delete_safety_wit_2 : delete_safety_wit_2.
Axiom proof_of_delete_return_wit_1 : delete_return_wit_1.
Axiom proof_of_delete_return_wit_2_1 : delete_return_wit_2_1.
Axiom proof_of_delete_return_wit_2_2 : delete_return_wit_2_2.
Axiom proof_of_delete_return_wit_2_3 : delete_return_wit_2_3.
Axiom proof_of_delete_return_wit_2_4 : delete_return_wit_2_4.
Axiom proof_of_delete_partial_solve_wit_1_pure : delete_partial_solve_wit_1_pure.
Axiom proof_of_delete_partial_solve_wit_1 : delete_partial_solve_wit_1.
Axiom proof_of_delete_partial_solve_wit_2_pure : delete_partial_solve_wit_2_pure.
Axiom proof_of_delete_partial_solve_wit_2 : delete_partial_solve_wit_2.
Axiom proof_of_delete_partial_solve_wit_3_pure : delete_partial_solve_wit_3_pure.
Axiom proof_of_delete_partial_solve_wit_3 : delete_partial_solve_wit_3.
Axiom proof_of_delete_partial_solve_wit_4 : delete_partial_solve_wit_4.
Axiom proof_of_delete_partial_solve_wit_5_pure : delete_partial_solve_wit_5_pure.
Axiom proof_of_delete_partial_solve_wit_5 : delete_partial_solve_wit_5.
Axiom proof_of_delete_partial_solve_wit_6_pure : delete_partial_solve_wit_6_pure.
Axiom proof_of_delete_partial_solve_wit_6 : delete_partial_solve_wit_6.
Axiom proof_of_delete_partial_solve_wit_7 : delete_partial_solve_wit_7.
Axiom proof_of_delete_which_implies_wit_1 : delete_which_implies_wit_1.
Axiom proof_of_delete_which_implies_wit_2 : delete_which_implies_wit_2.
Axiom proof_of_delete_derive_high_level_spec_by_low_level_spec : delete_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
