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
Require Import sll_merge_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import sll_strategy_goal.
From SimpleC.EE Require Import sll_strategy_proof.

(*----- Function merge -----*)

Definition merge_safety_wit_1 := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition merge_safety_wit_2 := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_safety_wit_3 := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (s2: (@list Z)) (s1: (@list Z)) ,
  (sll x_pre s1 )
  **  (sll y_pre s2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
  **  (sllbseg ( &( "ret" ) ) ( &( "ret" ) ) l3 )
.

Definition merge_entail_wit_2_1 := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (y_next: Z) (y_data: Z) (l2_new: (@list Z)) ,
  [| (x_data < y_data) |] 
  &&  [| (l2_2 = (cons (y_data) (l2_new))) |] 
  &&  [| (l1_2 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1_2 l2_2 l3_2 ) |]
  &&  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x_next l1 )
  **  (sll y l2 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) &((x)  # "list" ->ₛ "next") l3 )
.

Definition merge_entail_wit_2_2 := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (y_next: Z) (y_data: Z) (l2_new: (@list Z)) ,
  [| (x_data >= y_data) |] 
  &&  [| (l2_2 = (cons (y_data) (l2_new))) |] 
  &&  [| (l1_2 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1_2 l2_2 l3_2 ) |]
  &&  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y_next l2 )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) &((y)  # "list" ->ₛ "next") l3 )
.

Definition merge_return_wit_1_1 := 
forall (s2: (@list Z)) (s1: (@list Z)) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (ret: Z) ,
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sllseg ret x l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)) ,
  [| (merge_rel s1 s2 s3 ) |]
  &&  (sll ret s3 )
.

Definition merge_return_wit_1_2 := 
forall (s2: (@list Z)) (s1: (@list Z)) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (ret: Z) ,
  [| (x = 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sllseg ret y l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)) ,
  [| (merge_rel s1 s2 s3 ) |]
  &&  (sll ret s3 )
.

Definition merge_partial_solve_wit_1_pure := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (x <> 0) |]
.

Definition merge_partial_solve_wit_1_aux := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (x <> 0) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
.

Definition merge_partial_solve_wit_1 := merge_partial_solve_wit_1_pure -> merge_partial_solve_wit_1_aux.

Definition merge_partial_solve_wit_2_pure := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (y <> 0) |]
.

Definition merge_partial_solve_wit_2_aux := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  (sll y l2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (y <> 0) |] 
  &&  [| (l1 = (cons (x_data) (l1_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll y l2 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
.

Definition merge_partial_solve_wit_2 := merge_partial_solve_wit_2_pure -> merge_partial_solve_wit_2_aux.

Definition merge_partial_solve_wit_3 := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_partial_solve_wit_4 := 
forall (s2: (@list Z)) (s1: (@list Z)) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (x = 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  [| (x = 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_which_implies_wit_1 := 
forall (l1: (@list Z)) (x: Z) ,
  [| (x <> 0) |]
  &&  (sll x l1 )
|--
  EX (x_next: Z)  (x_data: Z)  (l1_new: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
.

Definition merge_which_implies_wit_2 := 
forall (l2: (@list Z)) (y: Z) ,
  [| (y <> 0) |]
  &&  (sll y l2 )
|--
  EX (y_next: Z)  (y_data: Z)  (l2_new: (@list Z)) ,
  [| (l2 = (cons (y_data) (l2_new))) |]
  &&  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
.

Definition merge_which_implies_wit_3 := 
forall (l3: (@list Z)) (u: Z) (t: Z) ,
  ((t) # Ptr  |-> u)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  EX (ret: Z) ,
  ((( &( "ret" ) )) # Ptr  |-> ret)
  **  (sllseg ret u l3 )
.

(*----- Function split_rec -----*)

Definition split_rec_safety_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition split_rec_return_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (p_pre_v_2: Z) (q_pre_v_2: Z) ,
  [| (x_pre = 0) |]
  &&  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
  **  (sll p_pre_v_2 l1 )
  **  ((q_pre) # Ptr  |-> q_pre_v_2)
  **  (sll q_pre_v_2 l2 )
|--
  EX (q_pre_v: Z)  (p_pre_v: Z)  (s1: (@list Z))  (s2: (@list Z)) ,
  [| (split_rec_rel l l1 l2 s1 s2 ) |]
  &&  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v s1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v s2 )
.

Definition split_rec_return_wit_2 := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (x_data: Z) (l_new: (@list Z)) (q_pre_v_2: Z) (p_pre_v_2: Z) (s1_2: (@list Z)) (s2_2: (@list Z)) ,
  [| (split_rec_rel l_new l2 (cons (x_data) (l1)) s1_2 s2_2 ) |] 
  &&  [| (l = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((q_pre) # Ptr  |-> p_pre_v_2)
  **  (sll p_pre_v_2 s1_2 )
  **  ((p_pre) # Ptr  |-> q_pre_v_2)
  **  (sll q_pre_v_2 s2_2 )
|--
  EX (q_pre_v: Z)  (p_pre_v: Z)  (s1: (@list Z))  (s2: (@list Z)) ,
  [| (split_rec_rel l l1 l2 s1 s2 ) |]
  &&  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v s1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v s2 )
.

Definition split_rec_partial_solve_wit_1_pure := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) ,
  [| (x_pre <> 0) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2 )
|--
  [| (x_pre <> 0) |]
.

Definition split_rec_partial_solve_wit_1_aux := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) ,
  [| (x_pre <> 0) |]
  &&  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2 )
|--
  [| (x_pre <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2 )
.

Definition split_rec_partial_solve_wit_1 := split_rec_partial_solve_wit_1_pure -> split_rec_partial_solve_wit_1_aux.

Definition split_rec_partial_solve_wit_2_pure := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) ,
  [| (l = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> x_next)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_pre_v)
  **  (sll x_next l_new )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll p_pre_v l1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2 )
|--
  [| (x_pre <> 0) |]
.

Definition split_rec_partial_solve_wit_2_aux := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) ,
  [| (l = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_pre_v)
  **  (sll x_next l_new )
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll p_pre_v l1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2 )
|--
  [| (x_pre <> 0) |] 
  &&  [| (l = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((p_pre) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1 )
  **  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2 )
.

Definition split_rec_partial_solve_wit_2 := split_rec_partial_solve_wit_2_pure -> split_rec_partial_solve_wit_2_aux.

Definition split_rec_partial_solve_wit_3 := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (q_pre_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) ,
  [| (l = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((p_pre) # Ptr  |-> x_pre)
  **  (sll x_pre (cons (x_data) (l1)) )
  **  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2 )
|--
  [| (l = (cons (x_data) (l_new))) |] 
  &&  [| (x_pre <> 0) |]
  &&  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v l2 )
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll x_pre (cons (x_data) (l1)) )
.

Definition split_rec_which_implies_wit_1 := 
forall (l: (@list Z)) (x: Z) ,
  [| (x <> 0) |]
  &&  (sll x l )
|--
  EX (x_next: Z)  (x_data: Z)  (l_new: (@list Z)) ,
  [| (l = (cons (x_data) (l_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l_new )
.

Definition split_rec_which_implies_wit_2 := 
forall (l1: (@list Z)) (x_data: Z) (p: Z) (p_v: Z) (p_v_next: Z) ,
  [| (p_v <> 0) |]
  &&  ((p) # Ptr  |-> p_v)
  **  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> p_v_next)
  **  (sll p_v_next l1 )
|--
  ((p) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_data) (l1)) )
.

(*----- Function merge_sort -----*)

Definition merge_sort_safety_wit_1 := 
forall (x_pre: Z) (l: (@list Z)) ,
  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sort_safety_wit_2 := 
forall (x_pre: Z) (l: (@list Z)) ,
  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 nil )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sort_safety_wit_3 := 
forall (x_pre: Z) (l: (@list Z)) (q_pre_v: Z) (p_pre_v: Z) (s1: (@list Z)) (s2: (@list Z)) ,
  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v s1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v s2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_sort_return_wit_1 := 
forall (l: (@list Z)) (q_pre_v: Z) (p_pre_v: Z) (s1: (@list Z)) (s2: (@list Z)) ,
  [| (q_pre_v = 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll p_pre_v s1 )
  **  (sll q_pre_v s2 )
|--
  EX (l0: (@list Z)) ,
  [| (merge_sort_rel l l0 ) |]
  &&  (sll p_pre_v l0 )
.

Definition merge_sort_return_wit_2 := 
forall (l: (@list Z)) (q_pre_v: Z) (s1: (@list Z)) (s2: (@list Z)) (l0_2: (@list Z)) (l0_3: (@list Z)) (s3: (@list Z)) (retval: Z) ,
  [| (merge_rel l0_2 l0_3 s3 ) |] 
  &&  [| (merge_sort_rel s2 l0_3 ) |] 
  &&  [| (merge_sort_rel s1 l0_2 ) |] 
  &&  [| (s2 <> nil) |] 
  &&  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll retval s3 )
|--
  EX (l0: (@list Z)) ,
  [| (merge_sort_rel l l0 ) |]
  &&  (sll retval l0 )
.

Definition merge_sort_partial_solve_wit_1_pure := 
forall (x_pre: Z) (l: (@list Z)) ,
  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l )
|--
  [| (0 = 0) |]
.

Definition merge_sort_partial_solve_wit_1_aux := 
forall (x_pre: Z) (l: (@list Z)) ,
  (sll x_pre l )
|--
  [| (0 = 0) |]
  &&  (sll x_pre l )
.

Definition merge_sort_partial_solve_wit_1 := merge_sort_partial_solve_wit_1_pure -> merge_sort_partial_solve_wit_1_aux.

Definition merge_sort_partial_solve_wit_2_pure := 
forall (x_pre: Z) (l: (@list Z)) ,
  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 nil )
  **  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l )
|--
  [| (0 = 0) |]
.

Definition merge_sort_partial_solve_wit_2_aux := 
forall (x_pre: Z) (l: (@list Z)) ,
  (sll 0 nil )
  **  (sll x_pre l )
|--
  [| (0 = 0) |]
  &&  (sll x_pre l )
.

Definition merge_sort_partial_solve_wit_2 := merge_sort_partial_solve_wit_2_pure -> merge_sort_partial_solve_wit_2_aux.

Definition merge_sort_partial_solve_wit_3 := 
forall (x_pre: Z) (l: (@list Z)) ,
  (sll 0 nil )
  **  (sll x_pre l )
|--
  (sll x_pre l )
  **  (sll 0 nil )
  **  (sll 0 nil )
.

Definition merge_sort_partial_solve_wit_4_pure := 
forall (x_pre: Z) (l: (@list Z)) (q_pre_v: Z) (p_pre_v: Z) (s1: (@list Z)) (s2: (@list Z)) ,
  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v s1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v s2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (q_pre_v <> 0) |]
.

Definition merge_sort_partial_solve_wit_4_aux := 
forall (l: (@list Z)) (q_pre_v: Z) (p_pre_v: Z) (s1: (@list Z)) (s2: (@list Z)) ,
  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll p_pre_v s1 )
  **  (sll q_pre_v s2 )
|--
  [| (q_pre_v <> 0) |] 
  &&  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll q_pre_v s2 )
  **  (sll p_pre_v s1 )
.

Definition merge_sort_partial_solve_wit_4 := merge_sort_partial_solve_wit_4_pure -> merge_sort_partial_solve_wit_4_aux.

Definition merge_sort_partial_solve_wit_5 := 
forall (l: (@list Z)) (q_pre_v: Z) (p_pre_v: Z) (s1: (@list Z)) (s2: (@list Z)) ,
  [| (s2 <> nil) |] 
  &&  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll q_pre_v s2 )
  **  (sll p_pre_v s1 )
|--
  [| (s2 <> nil) |] 
  &&  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll p_pre_v s1 )
  **  (sll q_pre_v s2 )
.

Definition merge_sort_partial_solve_wit_6 := 
forall (l: (@list Z)) (q_pre_v: Z) (s1: (@list Z)) (s2: (@list Z)) (l0: (@list Z)) (retval: Z) ,
  [| (merge_sort_rel s1 l0 ) |] 
  &&  [| (s2 <> nil) |] 
  &&  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll retval l0 )
  **  (sll q_pre_v s2 )
|--
  [| (merge_sort_rel s1 l0 ) |] 
  &&  [| (s2 <> nil) |] 
  &&  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll q_pre_v s2 )
  **  (sll retval l0 )
.

Definition merge_sort_partial_solve_wit_7 := 
forall (l: (@list Z)) (q_pre_v: Z) (s1: (@list Z)) (s2: (@list Z)) (l0: (@list Z)) (retval: Z) (l0_2: (@list Z)) (retval_2: Z) ,
  [| (merge_sort_rel s2 l0_2 ) |] 
  &&  [| (merge_sort_rel s1 l0 ) |] 
  &&  [| (s2 <> nil) |] 
  &&  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll retval_2 l0_2 )
  **  (sll retval l0 )
|--
  [| (merge_sort_rel s2 l0_2 ) |] 
  &&  [| (merge_sort_rel s1 l0 ) |] 
  &&  [| (s2 <> nil) |] 
  &&  [| (q_pre_v <> 0) |] 
  &&  [| (split_rec_rel l nil nil s1 s2 ) |]
  &&  (sll retval l0 )
  **  (sll retval_2 l0_2 )
.

Definition merge_sort_which_implies_wit_1 := 
forall (p: Z) ,
  [| (p = 0) |]
  &&  emp
|--
  (sll p nil )
.

Definition merge_sort_which_implies_wit_2 := 
forall (q: Z) ,
  [| (q = 0) |]
  &&  emp
|--
  (sll q nil )
.

Definition merge_sort_which_implies_wit_3 := 
forall (l1: (@list Z)) (q: Z) ,
  [| (q <> 0) |]
  &&  (sll q l1 )
|--
  [| (l1 <> nil) |]
  &&  (sll q l1 )
.

(*----- Function merge_malloc -----*)

Definition merge_malloc_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (s2: (@list Z)) (s1: (@list Z)) ,
  ((( &( "ret" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "pret" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre s1 )
  **  (sll y_pre s2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_malloc_safety_wit_2 := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (u: Z) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |-> u)
  **  ((( &( "pret" ) )) # Ptr  |-> pret)
  **  (sllbseg pret t l3 )
  **  ((( &( "ret" ) )) # Ptr  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition merge_malloc_safety_wit_3 := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (u: Z) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |-> u)
  **  ((( &( "pret" ) )) # Ptr  |-> pret)
  **  (sllbseg pret t l3 )
  **  ((( &( "ret" ) )) # Ptr  |-> 0)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_malloc_safety_wit_4 := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (u: Z) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |-> u)
  **  ((( &( "pret" ) )) # Ptr  |-> pret)
  **  (sllbseg pret t l3 )
  **  ((( &( "ret" ) )) # Ptr  |-> 0)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition merge_malloc_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (s2: (@list Z)) (s1: (@list Z)) (p: Z) (retval: Z) ,
  ((retval) # Ptr  |-> p)
  **  (sll x_pre s1 )
  **  (sll y_pre s2 )
|--
  EX (u: Z)  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
  **  ((retval) # Ptr  |-> u)
  **  (sllbseg retval retval l3 )
.

Definition merge_malloc_entail_wit_2_1 := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (y_next: Z) (x_next: Z) (y_data: Z) (l2_new: (@list Z)) (x_data: Z) (l1_new: (@list Z)) ,
  [| (x_data < y_data) |] 
  &&  [| (l1_2 = (cons (x_data) (l1_new))) |] 
  &&  [| (l2_2 = (cons (y_data) (l2_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1_2 l2_2 l3_2 ) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg pret t l3_2 )
|--
  EX (u: Z)  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x_next l1 )
  **  (sll y l2 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (sllbseg pret &((x)  # "list" ->ₛ "next") l3 )
.

Definition merge_malloc_entail_wit_2_2 := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (y_next: Z) (x_next: Z) (y_data: Z) (l2_new: (@list Z)) (x_data: Z) (l1_new: (@list Z)) ,
  [| (x_data >= y_data) |] 
  &&  [| (l1_2 = (cons (x_data) (l1_new))) |] 
  &&  [| (l2_2 = (cons (y_data) (l2_new))) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1_2 l2_2 l3_2 ) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg pret t l3_2 )
|--
  EX (u: Z)  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y_next l2 )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (sllbseg pret &((y)  # "list" ->ₛ "next") l3 )
.

Definition merge_malloc_return_wit_1_1 := 
forall (s2: (@list Z)) (s1: (@list Z)) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (r: Z) ,
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sllseg r x l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)) ,
  [| (merge_rel s1 s2 s3 ) |]
  &&  (sll r s3 )
.

Definition merge_malloc_return_wit_1_2 := 
forall (s2: (@list Z)) (s1: (@list Z)) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (r: Z) ,
  [| (x = 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sllseg r y l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)) ,
  [| (merge_rel s1 s2 s3 ) |]
  &&  (sll r s3 )
.

Definition merge_malloc_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (s2: (@list Z)) (s1: (@list Z)) ,
  (sll x_pre s1 )
  **  (sll y_pre s2 )
|--
  (sll x_pre s1 )
  **  (sll y_pre s2 )
.

Definition merge_malloc_partial_solve_wit_2_pure := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (u: Z) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |-> u)
  **  ((( &( "pret" ) )) # Ptr  |-> pret)
  **  (sllbseg pret t l3 )
  **  ((( &( "ret" ) )) # Ptr  |-> 0)
|--
  [| (x <> 0) |] 
  &&  [| (y <> 0) |]
.

Definition merge_malloc_partial_solve_wit_2_aux := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (u: Z) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> u)
  **  (sllbseg pret t l3 )
|--
  [| (x <> 0) |] 
  &&  [| (y <> 0) |] 
  &&  [| (y <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> u)
  **  (sllbseg pret t l3 )
.

Definition merge_malloc_partial_solve_wit_2 := merge_malloc_partial_solve_wit_2_pure -> merge_malloc_partial_solve_wit_2_aux.

Definition merge_malloc_partial_solve_wit_3 := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg pret t l3 )
|--
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((t) # Ptr  |-> x)
  **  (sllbseg pret t l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_malloc_partial_solve_wit_4 := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (x = 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg pret t l3 )
|--
  [| (x = 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((t) # Ptr  |-> y)
  **  (sllbseg pret t l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_malloc_partial_solve_wit_5 := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (r: Z) ,
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((pret) # Ptr  |-> r)
  **  (sllseg r x l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  [| (y = 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((pret) # Ptr  |-> r)
  **  (sllseg r x l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_malloc_partial_solve_wit_6 := 
forall (s2: (@list Z)) (s1: (@list Z)) (pret: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (r: Z) ,
  [| (x = 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((pret) # Ptr  |-> r)
  **  (sllseg r y l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  [| (x = 0) |] 
  &&  [| (merge_steps s1 s2 nil l1 l2 l3 ) |]
  &&  ((pret) # Ptr  |-> r)
  **  (sllseg r y l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_malloc_which_implies_wit_1 := 
forall (l2: (@list Z)) (l1: (@list Z)) (x: Z) (y: Z) ,
  [| (x <> 0) |] 
  &&  [| (y <> 0) |]
  &&  (sll x l1 )
  **  (sll y l2 )
|--
  EX (y_next: Z)  (x_next: Z)  (y_data: Z)  (l2_new: (@list Z))  (x_data: Z)  (l1_new: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1_new))) |] 
  &&  [| (l2 = (cons (y_data) (l2_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
.

Definition merge_malloc_which_implies_wit_2 := 
forall (l3: (@list Z)) (u: Z) (t: Z) (pret: Z) ,
  ((t) # Ptr  |-> u)
  **  (sllbseg pret t l3 )
|--
  EX (r: Z) ,
  ((pret) # Ptr  |-> r)
  **  (sllseg r u l3 )
.

Definition merge_sort_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l: (@list Z)) ,
  (sll x_pre l )
|--
EX (l_2: (@list Z)) ,
  ((sll x_pre l_2 ))
  **
  ((EX l0_2 retval_2,
  [| (merge_sort_rel l_2 l0_2 ) |]
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  [| (Permutation l l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll retval l0 )))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_merge_safety_wit_1 : merge_safety_wit_1.
Axiom proof_of_merge_safety_wit_2 : merge_safety_wit_2.
Axiom proof_of_merge_safety_wit_3 : merge_safety_wit_3.
Axiom proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Axiom proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Axiom proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Axiom proof_of_merge_return_wit_1_1 : merge_return_wit_1_1.
Axiom proof_of_merge_return_wit_1_2 : merge_return_wit_1_2.
Axiom proof_of_merge_partial_solve_wit_1_pure : merge_partial_solve_wit_1_pure.
Axiom proof_of_merge_partial_solve_wit_1 : merge_partial_solve_wit_1.
Axiom proof_of_merge_partial_solve_wit_2_pure : merge_partial_solve_wit_2_pure.
Axiom proof_of_merge_partial_solve_wit_2 : merge_partial_solve_wit_2.
Axiom proof_of_merge_partial_solve_wit_3 : merge_partial_solve_wit_3.
Axiom proof_of_merge_partial_solve_wit_4 : merge_partial_solve_wit_4.
Axiom proof_of_merge_which_implies_wit_1 : merge_which_implies_wit_1.
Axiom proof_of_merge_which_implies_wit_2 : merge_which_implies_wit_2.
Axiom proof_of_merge_which_implies_wit_3 : merge_which_implies_wit_3.
Axiom proof_of_split_rec_safety_wit_1 : split_rec_safety_wit_1.
Axiom proof_of_split_rec_return_wit_1 : split_rec_return_wit_1.
Axiom proof_of_split_rec_return_wit_2 : split_rec_return_wit_2.
Axiom proof_of_split_rec_partial_solve_wit_1_pure : split_rec_partial_solve_wit_1_pure.
Axiom proof_of_split_rec_partial_solve_wit_1 : split_rec_partial_solve_wit_1.
Axiom proof_of_split_rec_partial_solve_wit_2_pure : split_rec_partial_solve_wit_2_pure.
Axiom proof_of_split_rec_partial_solve_wit_2 : split_rec_partial_solve_wit_2.
Axiom proof_of_split_rec_partial_solve_wit_3 : split_rec_partial_solve_wit_3.
Axiom proof_of_split_rec_which_implies_wit_1 : split_rec_which_implies_wit_1.
Axiom proof_of_split_rec_which_implies_wit_2 : split_rec_which_implies_wit_2.
Axiom proof_of_merge_sort_safety_wit_1 : merge_sort_safety_wit_1.
Axiom proof_of_merge_sort_safety_wit_2 : merge_sort_safety_wit_2.
Axiom proof_of_merge_sort_safety_wit_3 : merge_sort_safety_wit_3.
Axiom proof_of_merge_sort_return_wit_1 : merge_sort_return_wit_1.
Axiom proof_of_merge_sort_return_wit_2 : merge_sort_return_wit_2.
Axiom proof_of_merge_sort_partial_solve_wit_1_pure : merge_sort_partial_solve_wit_1_pure.
Axiom proof_of_merge_sort_partial_solve_wit_1 : merge_sort_partial_solve_wit_1.
Axiom proof_of_merge_sort_partial_solve_wit_2_pure : merge_sort_partial_solve_wit_2_pure.
Axiom proof_of_merge_sort_partial_solve_wit_2 : merge_sort_partial_solve_wit_2.
Axiom proof_of_merge_sort_partial_solve_wit_3 : merge_sort_partial_solve_wit_3.
Axiom proof_of_merge_sort_partial_solve_wit_4_pure : merge_sort_partial_solve_wit_4_pure.
Axiom proof_of_merge_sort_partial_solve_wit_4 : merge_sort_partial_solve_wit_4.
Axiom proof_of_merge_sort_partial_solve_wit_5 : merge_sort_partial_solve_wit_5.
Axiom proof_of_merge_sort_partial_solve_wit_6 : merge_sort_partial_solve_wit_6.
Axiom proof_of_merge_sort_partial_solve_wit_7 : merge_sort_partial_solve_wit_7.
Axiom proof_of_merge_sort_which_implies_wit_1 : merge_sort_which_implies_wit_1.
Axiom proof_of_merge_sort_which_implies_wit_2 : merge_sort_which_implies_wit_2.
Axiom proof_of_merge_sort_which_implies_wit_3 : merge_sort_which_implies_wit_3.
Axiom proof_of_merge_malloc_safety_wit_1 : merge_malloc_safety_wit_1.
Axiom proof_of_merge_malloc_safety_wit_2 : merge_malloc_safety_wit_2.
Axiom proof_of_merge_malloc_safety_wit_3 : merge_malloc_safety_wit_3.
Axiom proof_of_merge_malloc_safety_wit_4 : merge_malloc_safety_wit_4.
Axiom proof_of_merge_malloc_entail_wit_1 : merge_malloc_entail_wit_1.
Axiom proof_of_merge_malloc_entail_wit_2_1 : merge_malloc_entail_wit_2_1.
Axiom proof_of_merge_malloc_entail_wit_2_2 : merge_malloc_entail_wit_2_2.
Axiom proof_of_merge_malloc_return_wit_1_1 : merge_malloc_return_wit_1_1.
Axiom proof_of_merge_malloc_return_wit_1_2 : merge_malloc_return_wit_1_2.
Axiom proof_of_merge_malloc_partial_solve_wit_1 : merge_malloc_partial_solve_wit_1.
Axiom proof_of_merge_malloc_partial_solve_wit_2_pure : merge_malloc_partial_solve_wit_2_pure.
Axiom proof_of_merge_malloc_partial_solve_wit_2 : merge_malloc_partial_solve_wit_2.
Axiom proof_of_merge_malloc_partial_solve_wit_3 : merge_malloc_partial_solve_wit_3.
Axiom proof_of_merge_malloc_partial_solve_wit_4 : merge_malloc_partial_solve_wit_4.
Axiom proof_of_merge_malloc_partial_solve_wit_5 : merge_malloc_partial_solve_wit_5.
Axiom proof_of_merge_malloc_partial_solve_wit_6 : merge_malloc_partial_solve_wit_6.
Axiom proof_of_merge_malloc_which_implies_wit_1 : merge_malloc_which_implies_wit_1.
Axiom proof_of_merge_malloc_which_implies_wit_2 : merge_malloc_which_implies_wit_2.
Axiom proof_of_merge_sort_derive_high_level_spec_by_low_level_spec : merge_sort_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
