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
Local Open Scope sac.
From SimpleC.EE Require Import bst_strategy_goal.
From SimpleC.EE Require Import bst_strategy_proof.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function insert -----*)

Definition insert_safety_wit_1 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_tree b_pre tr )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insert_safety_wit_2 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |->_)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> retval)
  **  (store_tree b_pre tr )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insert_safety_wit_3 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> retval)
  **  (store_tree b_pre tr )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insert_return_wit_1 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (b_pre = 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_tree b_pre tr )
|--
  (store_tree retval (tree_insert (x_pre) (value_pre) (tr)) )
.

Definition insert_return_wit_2 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_right: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (retval: Z) ,
  [| (x_pre < b_key) |] 
  &&  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (b_key) (b_value) (r0))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree retval (tree_insert (x_pre) (value_pre) (l0)) )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr)) )
.

Definition insert_return_wit_3 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (retval: Z) ,
  [| (b_key < x_pre) |] 
  &&  [| (x_pre >= b_key) |] 
  &&  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (b_key) (b_value) (r0))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree retval (tree_insert (x_pre) (value_pre) (r0)) )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> retval)
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr)) )
.

Definition insert_return_wit_4 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) ,
  [| (b_key >= x_pre) |] 
  &&  [| (x_pre >= b_key) |] 
  &&  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (b_key) (b_value) (r0))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr)) )
.

Definition insert_partial_solve_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) ,
  [| (b_pre = 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_pre tr )
|--
  [| (b_pre = 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_pre tr )
.

Definition insert_partial_solve_wit_2_pure := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) ,
  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_tree b_pre tr )
|--
  [| (b_pre <> 0) |]
.

Definition insert_partial_solve_wit_2_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) ,
  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_pre tr )
|--
  [| (b_pre <> 0) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_pre tr )
.

Definition insert_partial_solve_wit_2 := insert_partial_solve_wit_2_pure -> insert_partial_solve_wit_2_aux.

Definition insert_partial_solve_wit_3_pure := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) ,
  [| (x_pre < b_key) |] 
  &&  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (b_key) (b_value) (r0))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition insert_partial_solve_wit_3_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) ,
  [| (x_pre < b_key) |] 
  &&  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (b_key) (b_value) (r0))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (x_pre < b_key) |] 
  &&  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (b_key) (b_value) (r0))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
.

Definition insert_partial_solve_wit_3 := insert_partial_solve_wit_3_pure -> insert_partial_solve_wit_3_aux.

Definition insert_partial_solve_wit_4_pure := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) ,
  [| (b_key < x_pre) |] 
  &&  [| (x_pre >= b_key) |] 
  &&  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (b_key) (b_value) (r0))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition insert_partial_solve_wit_4_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) ,
  [| (b_key < x_pre) |] 
  &&  [| (x_pre >= b_key) |] 
  &&  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (b_key) (b_value) (r0))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (b_key < x_pre) |] 
  &&  [| (x_pre >= b_key) |] 
  &&  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (b_key) (b_value) (r0))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_right r0 )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
.

Definition insert_partial_solve_wit_4 := insert_partial_solve_wit_4_pure -> insert_partial_solve_wit_4_aux.

Definition insert_which_implies_wit_1 := 
forall (tr0: tree) (b: Z) ,
  [| (b <> 0) |]
  &&  (store_tree b tr0 )
|--
  EX b_right b_left l0 b_value r0 b_key,
  [| (INT_MIN <= b_key) |] 
  &&  [| (b_key <= INT_MAX) |] 
  &&  [| (tr0 = (make_tree (l0) (b_key) (b_value) (r0))) |]
  &&  ((&((b)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
.

Definition insert_derive_high_level_spec_by_low_level_spec := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (m: mapping) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_map b_pre m )
|--
EX (tr: tree) ,
  ([| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_pre tr ))
  **
  ((EX retval_2,
  (store_tree retval_2 (tree_insert (x_pre) (value_pre) (tr)) ))
  -*
  (EX retval,
  (store_map retval (map_insert (x_pre) (value_pre) (m)) )))
.

Module Type VC_Correct.

Include bst_Strategy_Correct.
Include common_Strategy_Correct.

Axiom proof_of_insert_safety_wit_1 : insert_safety_wit_1.
Axiom proof_of_insert_safety_wit_2 : insert_safety_wit_2.
Axiom proof_of_insert_safety_wit_3 : insert_safety_wit_3.
Axiom proof_of_insert_return_wit_1 : insert_return_wit_1.
Axiom proof_of_insert_return_wit_2 : insert_return_wit_2.
Axiom proof_of_insert_return_wit_3 : insert_return_wit_3.
Axiom proof_of_insert_return_wit_4 : insert_return_wit_4.
Axiom proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1.
Axiom proof_of_insert_partial_solve_wit_2_pure : insert_partial_solve_wit_2_pure.
Axiom proof_of_insert_partial_solve_wit_2 : insert_partial_solve_wit_2.
Axiom proof_of_insert_partial_solve_wit_3_pure : insert_partial_solve_wit_3_pure.
Axiom proof_of_insert_partial_solve_wit_3 : insert_partial_solve_wit_3.
Axiom proof_of_insert_partial_solve_wit_4_pure : insert_partial_solve_wit_4_pure.
Axiom proof_of_insert_partial_solve_wit_4 : insert_partial_solve_wit_4.
Axiom proof_of_insert_which_implies_wit_1 : insert_which_implies_wit_1.
Axiom proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
