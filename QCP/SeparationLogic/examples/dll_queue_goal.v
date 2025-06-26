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
Require Import dll_queue_lib.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import dll_queue_strategy_goal.
Require Import dll_queue_strategy_proof.

(*----- Function enqueue -----*)

Definition enqueue_safety_wit_1 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval: Z) ,
  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (dllseg q_head 0 0 q_tail l )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition enqueue_safety_wit_2 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval: Z) ,
  [| (q_head = 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> retval)
  **  (dllseg q_head 0 0 q_tail l )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition enqueue_safety_wit_3 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval: Z) ,
  [| (q_head = 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> retval)
  **  (dllseg q_head 0 0 q_tail l )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition enqueue_safety_wit_4 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval: Z) (q_tail_prev: Z) (q_tail_next: Z) (l0: (@list Z)) (q_tail_data: Z) ,
  [| (q_tail <> 0) |] 
  &&  [| (l = (app (l0) ((cons (q_tail_data) (nil))))) |] 
  &&  [| (q_tail_next = 0) |] 
  &&  [| (q_head <> 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> q_tail_data)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((q_tail)  # "list" ->ₛ "prev")) # Ptr  |-> q_tail_prev)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (dllseg q_head q_tail 0 q_tail_prev l0 )
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> q_tail)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition enqueue_return_wit_1_1 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval: Z) (q_tail_prev: Z) (q_tail_next: Z) (l0: (@list Z)) (q_tail_data: Z) ,
  [| (q_tail <> 0) |] 
  &&  [| (l = (app (l0) ((cons (q_tail_data) (nil))))) |] 
  &&  [| (q_tail_next = 0) |] 
  &&  [| (q_head <> 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> q_tail_data)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((q_tail)  # "list" ->ₛ "prev")) # Ptr  |-> q_tail_prev)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (dllseg q_head q_tail 0 q_tail_prev l0 )
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> q_tail)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
|--
  (store_queue q_pre (app (l) ((cons (x_pre) (nil)))) )
.

Definition enqueue_return_wit_1_2 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval: Z) ,
  [| (q_head = 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> retval)
  **  (dllseg q_head 0 0 q_tail l )
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
forall (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) ,
  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (dllseg q_head 0 0 q_tail l )
|--
  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (dllseg q_head 0 0 q_tail l )
.

Definition enqueue_partial_solve_wit_3_pure := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval: Z) ,
  [| (q_head <> 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (dllseg q_head 0 0 q_tail l )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (q_head <> 0) |]
.

Definition enqueue_partial_solve_wit_3_aux := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (q_head: Z) (q_tail: Z) (retval: Z) ,
  [| (q_head <> 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (dllseg q_head 0 0 q_tail l )
|--
  [| (q_head <> 0) |] 
  &&  [| (q_head <> 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  (dllseg q_head 0 0 q_tail l )
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
.

Definition enqueue_partial_solve_wit_3 := enqueue_partial_solve_wit_3_pure -> enqueue_partial_solve_wit_3_aux.

Definition enqueue_which_implies_wit_1 := 
forall (l: (@list Z)) (q: Z) ,
  (store_queue q l )
|--
  EX (q_head: Z)  (q_tail: Z) ,
  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (dllseg q_head 0 0 q_tail l )
.

Definition enqueue_which_implies_wit_2 := 
forall (l: (@list Z)) (q: Z) (q_head: Z) (q_tail: Z) ,
  [| (q_head <> 0) |]
  &&  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  (dllseg q_head 0 0 q_tail l )
|--
  EX (q_tail_prev: Z)  (q_tail_next: Z)  (l0: (@list Z))  (q_tail_data: Z) ,
  [| (q_tail <> 0) |] 
  &&  [| (l = (app (l0) ((cons (q_tail_data) (nil))))) |] 
  &&  [| (q_tail_next = 0) |]
  &&  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_tail)  # "list" ->ₛ "data")) # Int  |-> q_tail_data)
  **  ((&((q_tail)  # "list" ->ₛ "next")) # Ptr  |-> q_tail_next)
  **  ((&((q_tail)  # "list" ->ₛ "prev")) # Ptr  |-> q_tail_prev)
  **  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  (dllseg q_head q_tail 0 q_tail_prev l0 )
.

(*----- Function dequeue -----*)

Definition dequeue_safety_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_head_next: Z) (q_tail: Z) (q_head_prev: Z) (q_head: Z) ,
  [| (q_head_prev = 0) |]
  &&  ((( &( "x0" ) )) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> q_head)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  (dllseg q_head_next 0 q_head q_tail l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dequeue_safety_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_head_next: Z) (q_tail: Z) (q_head_prev: Z) (q_head: Z) ,
  [| (q_head_next = 0) |] 
  &&  [| (q_head_prev = 0) |]
  &&  ((( &( "x0" ) )) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> q_head)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  (dllseg q_head_next 0 q_head q_tail l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dequeue_safety_wit_3 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_head_next_2: Z) (q_tail: Z) (q_head_prev: Z) (q_head: Z) (q_head_next: Z) (q_head_data: Z) (l0: (@list Z)) ,
  [| (l = (cons (q_head_data) (l0))) |] 
  &&  [| (q_head_next_2 <> 0) |] 
  &&  [| (q_head_prev = 0) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next_2)
  **  ((&((q_head_next_2)  # "list" ->ₛ "data")) # Int  |-> q_head_data)
  **  ((&((q_head_next_2)  # "list" ->ₛ "prev")) # Ptr  |-> q_head)
  **  ((( &( "p" ) )) # Ptr  |-> q_head)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_head_next_2)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  (dllseg q_head_next 0 q_head_next_2 q_tail l0 )
  **  ((( &( "x0" ) )) # Int  |-> x)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dequeue_return_wit_1_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_head_next_2: Z) (q_tail: Z) (q_head_prev: Z) (q_head_next: Z) (q_head_data: Z) (l0: (@list Z)) ,
  [| (l = (cons (q_head_data) (l0))) |] 
  &&  [| (q_head_next_2 <> 0) |] 
  &&  [| (q_head_prev = 0) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next_2)
  **  ((&((q_head_next_2)  # "list" ->ₛ "data")) # Int  |-> q_head_data)
  **  ((&((q_head_next_2)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_head_next_2)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  (dllseg q_head_next 0 q_head_next_2 q_tail l0 )
|--
  [| (x = x) |]
  &&  (store_queue q_pre l )
.

Definition dequeue_return_wit_1_2 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_head_next: Z) (q_tail: Z) (q_head_prev: Z) (q_head: Z) ,
  [| (q_head_next = 0) |] 
  &&  [| (q_head_prev = 0) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> 0)
  **  (dllseg q_head_next 0 q_head q_tail l )
|--
  [| (x = x) |]
  &&  (store_queue q_pre l )
.

Definition dequeue_partial_solve_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) ,
  (store_queue q_pre (cons (x) (l)) )
|--
  (store_queue q_pre (cons (x) (l)) )
.

Definition dequeue_partial_solve_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_head_next: Z) (q_tail: Z) (q_head_prev: Z) (q_head: Z) ,
  [| (q_head_prev = 0) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  ((&((q_head)  # "list" ->ₛ "prev")) # Ptr  |-> q_head_prev)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  (dllseg q_head_next 0 q_head q_tail l )
|--
  [| (q_head_prev = 0) |]
  &&  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  ((&((q_head)  # "list" ->ₛ "prev")) # Ptr  |-> q_head_prev)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  (dllseg q_head_next 0 q_head q_tail l )
.

Definition dequeue_partial_solve_wit_3_pure := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (q_head_next: Z) (q_tail: Z) (q_head_prev: Z) (q_head: Z) ,
  [| (q_head_next <> 0) |] 
  &&  [| (q_head_prev = 0) |]
  &&  ((( &( "x0" ) )) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> q_head)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  (dllseg q_head_next 0 q_head q_tail l )
|--
  [| (q_head_next <> 0) |]
.

Definition dequeue_partial_solve_wit_3_aux := 
forall (q_pre: Z) (l: (@list Z)) (q_head_next: Z) (q_tail: Z) (q_head_prev: Z) (q_head: Z) ,
  [| (q_head_next <> 0) |] 
  &&  [| (q_head_prev = 0) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  (dllseg q_head_next 0 q_head q_tail l )
|--
  [| (q_head_next <> 0) |] 
  &&  [| (q_head_next <> 0) |] 
  &&  [| (q_head_prev = 0) |]
  &&  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> q_head_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  (dllseg q_head_next 0 q_head q_tail l )
.

Definition dequeue_partial_solve_wit_3 := dequeue_partial_solve_wit_3_pure -> dequeue_partial_solve_wit_3_aux.

Definition dequeue_which_implies_wit_1 := 
forall (l: (@list Z)) (x: Z) (q: Z) ,
  (store_queue q (cons (x) (l)) )
|--
  EX (q_head_next: Z)  (q_tail: Z)  (q_head_prev: Z)  (q_head: Z) ,
  [| (q_head_prev = 0) |]
  &&  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  ((&((q_head)  # "list" ->ₛ "prev")) # Ptr  |-> q_head_prev)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  (dllseg q_head_next 0 q_head q_tail l )
.

Definition dequeue_which_implies_wit_2 := 
forall (l: (@list Z)) (q: Z) (q_head: Z) (q_tail: Z) (p: Z) ,
  [| (q_head <> 0) |]
  &&  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  (dllseg q_head 0 p q_tail l )
|--
  EX (q_head_next: Z)  (q_head_data: Z)  (l0: (@list Z)) ,
  [| (l = (cons (q_head_data) (l0))) |]
  &&  ((&((q)  # "queue" ->ₛ "head")) # Ptr  |-> q_head)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> q_head_data)
  **  ((&((q_head)  # "list" ->ₛ "prev")) # Ptr  |-> p)
  **  ((&((q)  # "queue" ->ₛ "tail")) # Ptr  |-> q_tail)
  **  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_head_next)
  **  (dllseg q_head_next 0 q_head q_tail l0 )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include dll_queue_Strategy_Correct.

Axiom proof_of_enqueue_safety_wit_1 : enqueue_safety_wit_1.
Axiom proof_of_enqueue_safety_wit_2 : enqueue_safety_wit_2.
Axiom proof_of_enqueue_safety_wit_3 : enqueue_safety_wit_3.
Axiom proof_of_enqueue_safety_wit_4 : enqueue_safety_wit_4.
Axiom proof_of_enqueue_return_wit_1_1 : enqueue_return_wit_1_1.
Axiom proof_of_enqueue_return_wit_1_2 : enqueue_return_wit_1_2.
Axiom proof_of_enqueue_partial_solve_wit_1 : enqueue_partial_solve_wit_1.
Axiom proof_of_enqueue_partial_solve_wit_2 : enqueue_partial_solve_wit_2.
Axiom proof_of_enqueue_partial_solve_wit_3_pure : enqueue_partial_solve_wit_3_pure.
Axiom proof_of_enqueue_partial_solve_wit_3 : enqueue_partial_solve_wit_3.
Axiom proof_of_enqueue_which_implies_wit_1 : enqueue_which_implies_wit_1.
Axiom proof_of_enqueue_which_implies_wit_2 : enqueue_which_implies_wit_2.
Axiom proof_of_dequeue_safety_wit_1 : dequeue_safety_wit_1.
Axiom proof_of_dequeue_safety_wit_2 : dequeue_safety_wit_2.
Axiom proof_of_dequeue_safety_wit_3 : dequeue_safety_wit_3.
Axiom proof_of_dequeue_return_wit_1_1 : dequeue_return_wit_1_1.
Axiom proof_of_dequeue_return_wit_1_2 : dequeue_return_wit_1_2.
Axiom proof_of_dequeue_partial_solve_wit_1 : dequeue_partial_solve_wit_1.
Axiom proof_of_dequeue_partial_solve_wit_2 : dequeue_partial_solve_wit_2.
Axiom proof_of_dequeue_partial_solve_wit_3_pure : dequeue_partial_solve_wit_3_pure.
Axiom proof_of_dequeue_partial_solve_wit_3 : dequeue_partial_solve_wit_3.
Axiom proof_of_dequeue_which_implies_wit_1 : dequeue_which_implies_wit_1.
Axiom proof_of_dequeue_which_implies_wit_2 : dequeue_which_implies_wit_2.

End VC_Correct.
