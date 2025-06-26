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
Require Import functional_queue_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import sll_strategy_goal.
From SimpleC.EE Require Import sll_strategy_proof.
From SimpleC.EE Require Import functional_queue_strategy_goal.
From SimpleC.EE Require Import functional_queue_strategy_proof.

(*----- Function push -----*)

Definition push_return_wit_1 := 
forall (x_pre: Z) (p_pre: Z) (l: (@list Z)) (p_pre_v_2: Z) (retval_data: Z) (retval_next: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_data = 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> p_pre_v_2)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((p_pre) # Ptr  |-> retval)
  **  (sll p_pre_v_2 l )
|--
  EX p_pre_v,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v (cons (x_pre) (l)) )
.

Definition push_partial_solve_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l )
|--
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l )
.

(*----- Function pop -----*)

Definition pop_return_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (x: Z) (y_105: Z) ,
  (sll y_105 l )
  **  ((p_pre) # Ptr  |-> y_105)
|--
  EX p_pre_v,
  [| (x = x) |]
  &&  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l )
.

Definition pop_partial_solve_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (x: Z) (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v (cons (x) (l)) )
|--
  EX y_105,
  ((&((p_pre_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y_105 l )
  **  ((&((p_pre_v)  # "list" ->ₛ "next")) # Ptr  |-> y_105)
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition pop_partial_solve_wit_2 := 
forall (p_pre: Z) (l: (@list Z)) (x: Z) (p_pre_v: Z) (y_105: Z) ,
  ((&((p_pre_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y_105 l )
  **  ((&((p_pre_v)  # "list" ->ₛ "next")) # Ptr  |-> y_105)
  **  ((p_pre) # Ptr  |-> y_105)
|--
  ((&((p_pre_v)  # "list" ->ₛ "next")) # Ptr  |-> y_105)
  **  ((&((p_pre_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y_105 l )
  **  ((p_pre) # Ptr  |-> y_105)
.

(*----- Function enqueue -----*)

Definition enqueue_return_wit_1 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) (p_pre_v: Z) ,
  [| (l = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v (cons (x_pre) (l2)) )
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
|--
  (store_queue q_pre (app (l) ((cons (x_pre) (nil)))) )
.

Definition enqueue_partial_solve_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) ,
  (store_queue q_pre l )
|--
  (store_queue q_pre l )
.

Definition enqueue_partial_solve_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (q_l2: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (l = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
|--
  [| (l = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
.

Definition enqueue_which_implies_wit_1 := 
forall (l: (@list Z)) (q: Z) ,
  (store_queue q l )
|--
  EX q_l2 q_l1 l1 l2,
  [| (l = (app (l1) ((rev (l2))))) |]
  &&  ((&((q)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
  **  ((&((q)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
.

(*----- Function dequeue -----*)

Definition dequeue_safety_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l2: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dequeue_safety_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l2: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) (retval: Z) ,
  [| (q_l1 = 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  (sll retval (rev (l2)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> retval)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dequeue_return_wit_1_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l2: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) (z: Z) (l1_tail: (@list Z)) (p_pre_v: Z) (retval: Z) ,
  [| (retval = z) |] 
  &&  [| (l1 = (cons (z) (l1_tail))) |] 
  &&  [| (q_l1 <> 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l1_tail )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
|--
  [| (retval = x) |]
  &&  (store_queue q_pre l )
.

Definition dequeue_return_wit_1_2 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) (p_pre_v: Z) (retval: Z) ,
  [| (retval = x) |] 
  &&  [| (q_l1 = 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v l )
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> 0)
|--
  [| (retval = x) |]
  &&  (store_queue q_pre l )
.

Definition dequeue_partial_solve_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) ,
  (store_queue q_pre (cons (x) (l)) )
|--
  (store_queue q_pre (cons (x) (l)) )
.

Definition dequeue_partial_solve_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l2: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (q_l1 = 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
|--
  [| (q_l1 = 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  (sll q_l2 l2 )
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
.

Definition dequeue_partial_solve_wit_3_pure := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) (retval: Z) ,
  [| (q_l1 = 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  (sll retval (rev (l2)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> retval)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> 0)
|--
  [| ((cons (x) (l)) = (cons (x) (l))) |] 
  &&  [| ((rev (l2)) = (cons (x) (l))) |]
.

Definition dequeue_partial_solve_wit_3_aux := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) (retval: Z) ,
  [| (q_l1 = 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  (sll retval (rev (l2)) )
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> retval)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> 0)
|--
  [| ((cons (x) (l)) = (cons (x) (l))) |] 
  &&  [| ((rev (l2)) = (cons (x) (l))) |] 
  &&  [| (q_l1 = 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> retval)
  **  (sll retval (cons (x) (l)) )
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> 0)
.

Definition dequeue_partial_solve_wit_3 := dequeue_partial_solve_wit_3_pure -> dequeue_partial_solve_wit_3_aux.

Definition dequeue_partial_solve_wit_4_pure := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l2: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (q_l1 <> 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
|--
  [| (q_l1 <> 0) |]
.

Definition dequeue_partial_solve_wit_4_aux := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l2: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (q_l1 <> 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
|--
  [| (q_l1 <> 0) |] 
  &&  [| (q_l1 <> 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
.

Definition dequeue_partial_solve_wit_4 := dequeue_partial_solve_wit_4_pure -> dequeue_partial_solve_wit_4_aux.

Definition dequeue_partial_solve_wit_5 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) (retval: Z) ,
  [| (q_l1 = 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> retval)
  **  (sll retval (cons (x) (l)) )
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> 0)
|--
  [| (q_l1 = 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> retval)
  **  (sll retval (cons (x) (l)) )
  **  (sll q_l1 l1 )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> 0)
.

Definition dequeue_partial_solve_wit_6 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_l2: Z) (q_l1: Z) (l1: (@list Z)) (l2: (@list Z)) (z: Z) (l1_tail: (@list Z)) ,
  [| (l1 = (cons (z) (l1_tail))) |] 
  &&  [| (q_l1 <> 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 (cons (z) (l1_tail)) )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
|--
  [| (l1 = (cons (z) (l1_tail))) |] 
  &&  [| (q_l1 <> 0) |] 
  &&  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 (cons (z) (l1_tail)) )
  **  ((&((q_pre)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
.

Definition dequeue_which_implies_wit_1 := 
forall (l: (@list Z)) (x: Z) (q: Z) ,
  (store_queue q (cons (x) (l)) )
|--
  EX q_l2 q_l1 l1 l2,
  [| ((cons (x) (l)) = (app (l1) ((rev (l2))))) |]
  &&  ((&((q)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
  **  ((&((q)  # "queue" ->ₛ "l2")) # Ptr  |-> q_l2)
  **  (sll q_l2 l2 )
.

Definition dequeue_which_implies_wit_2 := 
forall (l: (@list Z)) (x: Z) (rev_l2: (@list Z)) (q: Z) (q_l1: Z) ,
  [| ((cons (x) (l)) = rev_l2) |]
  &&  ((&((q)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 rev_l2 )
|--
  ((&((q)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 (cons (x) (l)) )
.

Definition dequeue_which_implies_wit_3 := 
forall (l1: (@list Z)) (q: Z) (q_l1: Z) ,
  [| (q_l1 <> 0) |]
  &&  ((&((q)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 l1 )
|--
  EX z l1_tail,
  [| (l1 = (cons (z) (l1_tail))) |]
  &&  ((&((q)  # "queue" ->ₛ "l1")) # Ptr  |-> q_l1)
  **  (sll q_l1 (cons (z) (l1_tail)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.
Include functional_queue_Strategy_Correct.

Axiom proof_of_push_return_wit_1 : push_return_wit_1.
Axiom proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1.
Axiom proof_of_pop_return_wit_1 : pop_return_wit_1.
Axiom proof_of_pop_partial_solve_wit_1 : pop_partial_solve_wit_1.
Axiom proof_of_pop_partial_solve_wit_2 : pop_partial_solve_wit_2.
Axiom proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Axiom proof_of_enqueue_partial_solve_wit_1 : enqueue_partial_solve_wit_1.
Axiom proof_of_enqueue_partial_solve_wit_2 : enqueue_partial_solve_wit_2.
Axiom proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Axiom proof_of_dequeue_safety_wit_1 : dequeue_safety_wit_1.
Axiom proof_of_dequeue_safety_wit_2 : dequeue_safety_wit_2.
Axiom proof_of_dequeue_return_wit_1_1 : dequeue_return_wit_1_1.
Axiom proof_of_dequeue_return_wit_1_2 : dequeue_return_wit_1_2.
Axiom proof_of_dequeue_partial_solve_wit_1 : dequeue_partial_solve_wit_1.
Axiom proof_of_dequeue_partial_solve_wit_2 : dequeue_partial_solve_wit_2.
Axiom proof_of_dequeue_partial_solve_wit_3_pure : dequeue_partial_solve_wit_3_pure.
Axiom proof_of_dequeue_partial_solve_wit_3 : dequeue_partial_solve_wit_3.
Axiom proof_of_dequeue_partial_solve_wit_4_pure : dequeue_partial_solve_wit_4_pure.
Axiom proof_of_dequeue_partial_solve_wit_4 : dequeue_partial_solve_wit_4.
Axiom proof_of_dequeue_partial_solve_wit_5 : dequeue_partial_solve_wit_5.
Axiom proof_of_dequeue_partial_solve_wit_6 : dequeue_partial_solve_wit_6.
Axiom proof_of_dequeue_which_implies_wit_1 : dequeue_which_implies_wit_1.
Axiom proof_of_dequeue_which_implies_wit_2 : dequeue_which_implies_wit_2.
Axiom proof_of_dequeue_which_implies_wit_3 : dequeue_which_implies_wit_3.

End VC_Correct.
