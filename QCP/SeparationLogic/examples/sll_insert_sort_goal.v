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
Require Import sll_lib.
Require Import sll_insert_sort_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import sll_strategy_goal.
From SimpleC.EE Require Import sll_strategy_proof.

(*----- Function insertion -----*)

Definition insertion_safety_wit_1 := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insertion_entail_wit_1 := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) ,
  [| (node_pre <> 0) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sll p_pre l )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX l1 l2,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) ( &( "res" ) ) l1 )
  **  (sll p_pre l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

Definition insertion_entail_wit_2 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v_2: Z) (p2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x_81: Z) (l0_82: (@list Z)) (p2_v_next: Z) (p2_v_data: Z) (l3: (@list Z)) ,
  [| ((cons (x_81) (l0_82)) = (cons (p2_v_data) (l3))) |] 
  &&  [| (x_81 < a) |] 
  &&  [| (l2_2 = (cons (x_81) (l0_82))) |] 
  &&  [| (p2_v_2 <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (strict_upperbound a l1_2 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((p2) # Ptr  |-> p2_v_2)
  **  ((&((p2_v_2)  # "list" ->ₛ "data")) # Int  |-> p2_v_data)
  **  ((&((p2_v_2)  # "list" ->ₛ "next")) # Ptr  |-> p2_v_next)
  **  (sll p2_v_next l3 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX p2_v l1 l2,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) &((p2_v_2)  # "list" ->ₛ "next") l1 )
  **  ((&((p2_v_2)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

Definition insertion_return_wit_1_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (l1: (@list Z)) (l2: (@list Z)) (res: Z) ,
  [| (p2_v = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  (sllseg res node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  EX l0,
  [| (l0 = (insert (a) (l))) |]
  &&  (sll res l0 )
.

Definition insertion_return_wit_1_2 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (l1: (@list Z)) (l2: (@list Z)) (x_81: Z) (l0_82: (@list Z)) (y_83: Z) (res: Z) ,
  [| (x_81 >= a) |] 
  &&  [| (l2 = (cons (x_81) (l0_82))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  (sllseg res node_pre l1 )
  **  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x_81)
  **  (sll y_83 l0_82 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y_83)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  EX l0,
  [| (l0 = (insert (a) (l))) |]
  &&  (sll res l0 )
.

Definition insertion_partial_solve_wit_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p2_v <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX y_83 l0_82 x_81,
  [| (l2 = (cons (x_81) (l0_82))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x_81)
  **  (sll y_83 l0_82 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y_83)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

Definition insertion_partial_solve_wit_2_pure := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (x_81: Z) (l0_82: (@list Z)) (y_83: Z) ,
  [| (x_81 < a) |] 
  &&  [| (l2 = (cons (x_81) (l0_82))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x_81)
  **  (sll y_83 l0_82 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y_83)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (p2_v <> 0) |]
.

Definition insertion_partial_solve_wit_2_aux := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (x_81: Z) (l0_82: (@list Z)) (y_83: Z) ,
  [| (x_81 < a) |] 
  &&  [| (l2 = (cons (x_81) (l0_82))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x_81)
  **  (sll y_83 l0_82 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y_83)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  [| (p2_v <> 0) |] 
  &&  [| (x_81 < a) |] 
  &&  [| (l2 = (cons (x_81) (l0_82))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v (cons (x_81) (l0_82)) )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

Definition insertion_partial_solve_wit_2 := insertion_partial_solve_wit_2_pure -> insertion_partial_solve_wit_2_aux.

Definition insertion_partial_solve_wit_3_pure := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p2_v = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> node_pre)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (node_pre = node_pre) |]
.

Definition insertion_partial_solve_wit_3_aux := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p2_v = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> node_pre)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  [| (node_pre = node_pre) |] 
  &&  [| (p2_v = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((p2) # Ptr  |-> node_pre)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
.

Definition insertion_partial_solve_wit_3 := insertion_partial_solve_wit_3_pure -> insertion_partial_solve_wit_3_aux.

Definition insertion_partial_solve_wit_4_pure := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (x_81: Z) (l0_82: (@list Z)) (y_83: Z) ,
  [| (x_81 >= a) |] 
  &&  [| (l2 = (cons (x_81) (l0_82))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x_81)
  **  (sll y_83 l0_82 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y_83)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (node_pre = node_pre) |]
.

Definition insertion_partial_solve_wit_4_aux := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) (x_81: Z) (l0_82: (@list Z)) (y_83: Z) ,
  [| (x_81 >= a) |] 
  &&  [| (l2 = (cons (x_81) (l0_82))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x_81)
  **  (sll y_83 l0_82 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y_83)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
|--
  [| (node_pre = node_pre) |] 
  &&  [| (x_81 >= a) |] 
  &&  [| (l2 = (cons (x_81) (l0_82))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |] 
  &&  [| (node_pre <> 0) |]
  &&  ((p2) # Ptr  |-> node_pre)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x_81)
  **  (sll y_83 l0_82 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y_83)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
.

Definition insertion_partial_solve_wit_4 := insertion_partial_solve_wit_4_pure -> insertion_partial_solve_wit_4_aux.

Definition insertion_which_implies_wit_1 := 
forall (l2: (@list Z)) (p2: Z) (p2_v: Z) ,
  [| (p2_v <> 0) |]
  &&  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
|--
  EX p2_v_next p2_v_data l3,
  [| (l2 = (cons (p2_v_data) (l3))) |]
  &&  ((p2) # Ptr  |-> p2_v)
  **  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> p2_v_data)
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> p2_v_next)
  **  (sll p2_v_next l3 )
.

Definition insertion_which_implies_wit_2 := 
forall (l1: (@list Z)) (p2: Z) (p2_v: Z) (node: Z) ,
  [| (p2_v = node) |]
  &&  ((p2) # Ptr  |-> p2_v)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
|--
  EX res,
  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sllseg res node l1 )
.

(*----- Function insertion_sort -----*)

Definition insertion_sort_safety_wit_1 := 
forall (x_pre: Z) (l: (@list Z)) ,
  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insertion_sort_safety_wit_2 := 
forall (x_pre: Z) (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l2 )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insertion_sort_entail_wit_1 := 
forall (x_pre: Z) (l: (@list Z)) ,
  (sll x_pre l )
|--
  EX l0 l1 l2,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll 0 l0 )
  **  (sll x_pre l2 )
.

Definition insertion_sort_entail_wit_2 := 
forall (l: (@list Z)) (p: Z) (l0_3: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) (l0_2: (@list Z)) (retval: Z) ,
  [| (l0_2 = (insert (p_data) (l0_3))) |] 
  &&  [| (l2_2 = (cons (p_data) (l3))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (Permutation l1_2 l0_3 ) |] 
  &&  [| (increasing l0_3 ) |]
  &&  (sll retval l0_2 )
  **  (sll p_next l3 )
  **  ((( &( "q" ) )) # Ptr  |-> p_next)
|--
  EX l0 l1 l2,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll retval l0 )
  **  (sll p_next l2 )
  **  ((( &( "q" ) )) # Ptr  |->_)
.

Definition insertion_sort_return_wit_1 := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0_2: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0_2 ) |] 
  &&  [| (increasing l0_2 ) |]
  &&  (sll res l0_2 )
  **  (sll p l2 )
|--
  EX l0,
  [| (Permutation l l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll res l0 )
.

Definition insertion_sort_partial_solve_wit_1_pure := 
forall (x_pre: Z) (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l2 )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (p <> 0) |]
.

Definition insertion_sort_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll res l0 )
  **  (sll p l2 )
|--
  [| (p <> 0) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll p l2 )
  **  (sll res l0 )
.

Definition insertion_sort_partial_solve_wit_1 := insertion_sort_partial_solve_wit_1_pure -> insertion_sort_partial_solve_wit_1_aux.

Definition insertion_sort_partial_solve_wit_2_pure := 
forall (x_pre: Z) (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) ,
  [| (l2 = (cons (p_data) (l3))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "q" ) )) # Ptr  |-> p_next)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (p <> 0) |]
.

Definition insertion_sort_partial_solve_wit_2_aux := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) ,
  [| (l2 = (cons (p_data) (l3))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sll res l0 )
|--
  [| (p <> 0) |] 
  &&  [| (l2 = (cons (p_data) (l3))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  (sll res l0 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sll p_next l3 )
.

Definition insertion_sort_partial_solve_wit_2 := insertion_sort_partial_solve_wit_2_pure -> insertion_sort_partial_solve_wit_2_aux.

Definition insertion_sort_which_implies_wit_1 := 
forall (l2: (@list Z)) (p: Z) ,
  [| (p <> 0) |]
  &&  (sll p l2 )
|--
  EX p_next p_data l3,
  [| (l2 = (cons (p_data) (l3))) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_insertion_safety_wit_1 : insertion_safety_wit_1.
Axiom proof_of_insertion_entail_wit_1 : insertion_entail_wit_1.
Axiom proof_of_insertion_entail_wit_2 : insertion_entail_wit_2.
Axiom proof_of_insertion_return_wit_1_1 : insertion_return_wit_1_1.
Axiom proof_of_insertion_return_wit_1_2 : insertion_return_wit_1_2.
Axiom proof_of_insertion_partial_solve_wit_1 : insertion_partial_solve_wit_1.
Axiom proof_of_insertion_partial_solve_wit_2_pure : insertion_partial_solve_wit_2_pure.
Axiom proof_of_insertion_partial_solve_wit_2 : insertion_partial_solve_wit_2.
Axiom proof_of_insertion_partial_solve_wit_3_pure : insertion_partial_solve_wit_3_pure.
Axiom proof_of_insertion_partial_solve_wit_3 : insertion_partial_solve_wit_3.
Axiom proof_of_insertion_partial_solve_wit_4_pure : insertion_partial_solve_wit_4_pure.
Axiom proof_of_insertion_partial_solve_wit_4 : insertion_partial_solve_wit_4.
Axiom proof_of_insertion_which_implies_wit_1 : insertion_which_implies_wit_1.
Axiom proof_of_insertion_which_implies_wit_2 : insertion_which_implies_wit_2.
Axiom proof_of_insertion_sort_safety_wit_1 : insertion_sort_safety_wit_1.
Axiom proof_of_insertion_sort_safety_wit_2 : insertion_sort_safety_wit_2.
Axiom proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Axiom proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2.
Axiom proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_1_pure : insertion_sort_partial_solve_wit_1_pure.
Axiom proof_of_insertion_sort_partial_solve_wit_1 : insertion_sort_partial_solve_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_2_pure : insertion_sort_partial_solve_wit_2_pure.
Axiom proof_of_insertion_sort_partial_solve_wit_2 : insertion_sort_partial_solve_wit_2.
Axiom proof_of_insertion_sort_which_implies_wit_1 : insertion_sort_which_implies_wit_1.

End VC_Correct.
