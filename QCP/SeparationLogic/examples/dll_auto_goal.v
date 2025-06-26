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
Require Import dll_shape_lib.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import dll_shape_strategy_goal.
Require Import dll_shape_strategy_proof.

(*----- Function dll_copy -----*)

Definition dll_copy_safety_wit_1 := 
forall (x_pre: Z) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (dlistrep x_pre 0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dll_copy_safety_wit_2 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev: Z) (p: Z) (t_prev: Z) (t_data: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep y_2 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (dllseg x_pre 0 p_prev p )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (dllseg y 0 0 t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dll_copy_entail_wit_1 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((retval)  # "dlist" ->ₛ "data")) # Int  |-> 0)
  **  ((&((retval)  # "dlist" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((retval)  # "dlist" ->ₛ "prev")) # Ptr  |-> retval_prev)
  **  (dlistrep x_pre 0 )
|--
  EX (p_prev: Z)  (t_prev: Z)  (t_data: Z)  (t_next: Z) ,
  [| (retval <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((retval)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval)  # "dlist" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((retval)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_pre 0 p_prev x_pre )
  **  (dlistrep x_pre p_prev )
  **  (dllseg retval 0 0 retval )
.

Definition dll_copy_entail_wit_2 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev_2: Z) (p: Z) (t_prev_2: Z) (t_data_2: Z) (t_next_2: Z) (t: Z) (x: Z) (y_2: Z) (retval_prev_2: Z) (retval_next_2: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_next_2 = 0) |] 
  &&  [| (retval_prev_2 = 0) |] 
  &&  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next_2 = 0) |] 
  &&  [| (t_data_2 = 0) |] 
  &&  [| (t_prev_2 = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((retval_2)  # "dlist" ->ₛ "data")) # Int  |-> 0)
  **  ((&((retval_2)  # "dlist" ->ₛ "next")) # Ptr  |-> retval_next_2)
  **  ((&((retval_2)  # "dlist" ->ₛ "prev")) # Ptr  |-> retval_prev_2)
  **  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep y_2 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> retval_2)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  (dllseg x_pre 0 p_prev_2 p )
  **  (dllseg y 0 0 t )
|--
  EX (p_prev: Z)  (t_prev: Z)  (t_data: Z)  (t_next: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((retval_2)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval_2)  # "dlist" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((retval_2)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_pre 0 p_prev y_2 )
  **  (dlistrep y_2 p_prev )
  **  (dllseg y 0 0 retval_2 )
.

Definition dll_copy_return_wit_1 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev: Z) (p: Z) (t_prev: Z) (t_data: Z) (t_next: Z) (t: Z) ,
  [| (p = 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_pre 0 p_prev p )
  **  (dlistrep p p_prev )
  **  (dllseg y 0 0 t )
|--
  (dlistrep y 0 )
  **  (dlistrep x_pre 0 )
.

Definition dll_copy_partial_solve_wit_1_pure := 
forall (x_pre: Z) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (dlistrep x_pre 0 )
|--
  [| (0 = 0) |]
.

Definition dll_copy_partial_solve_wit_1_aux := 
forall (x_pre: Z) ,
  (dlistrep x_pre 0 )
|--
  [| (0 = 0) |]
  &&  (dlistrep x_pre 0 )
.

Definition dll_copy_partial_solve_wit_1 := dll_copy_partial_solve_wit_1_pure -> dll_copy_partial_solve_wit_1_aux.

Definition dll_copy_partial_solve_wit_2 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y_2: Z) (p_prev: Z) (p: Z) (t_prev: Z) (t_data: Z) (t_next: Z) (t: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_pre 0 p_prev p )
  **  (dlistrep p p_prev )
  **  (dllseg y_2 0 0 t )
|--
  EX (y: Z)  (x: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep y p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_pre 0 p_prev p )
  **  (dllseg y_2 0 0 t )
.

Definition dll_copy_partial_solve_wit_3_pure := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev: Z) (p: Z) (t_prev: Z) (t_data: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep y_2 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (dllseg x_pre 0 p_prev p )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (dllseg y 0 0 t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 = 0) |]
.

Definition dll_copy_partial_solve_wit_3_aux := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev: Z) (p: Z) (t_prev: Z) (t_data: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep y_2 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg x_pre 0 p_prev p )
  **  (dllseg y 0 0 t )
|--
  [| (0 = 0) |] 
  &&  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep y_2 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg x_pre 0 p_prev p )
  **  (dllseg y 0 0 t )
.

Definition dll_copy_partial_solve_wit_3 := dll_copy_partial_solve_wit_3_pure -> dll_copy_partial_solve_wit_3_aux.

(*----- Function dll_free -----*)

Definition dll_free_entail_wit_1 := 
forall (x_pre: Z) ,
  (dlistrep x_pre 0 )
|--
  EX (prev: Z) ,
  (dlistrep x_pre prev )
.

Definition dll_free_entail_wit_2 := 
forall (x: Z) (y: Z) ,
  [| (x <> 0) |]
  &&  (dlistrep y x )
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  EX (prev: Z) ,
  (dlistrep y prev )
  **  ((( &( "y" ) )) # Ptr  |->_)
.

Definition dll_free_return_wit_1 := 
forall (x: Z) (prev: Z) ,
  [| (x = 0) |]
  &&  (dlistrep x prev )
|--
  TT && emp 
.

Definition dll_free_partial_solve_wit_1 := 
forall (x_2: Z) (prev: Z) ,
  [| (x_2 <> 0) |]
  &&  (dlistrep x_2 prev )
|--
  EX (y: Z)  (x: Z) ,
  [| (x_2 <> 0) |]
  &&  ((&((x_2)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y x_2 )
  **  ((&((x_2)  # "dlist" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x_2)  # "dlist" ->ₛ "data")) # Int  |-> x)
.

Definition dll_free_partial_solve_wit_2_pure := 
forall (x: Z) (prev: Z) (x_2: Z) (y: Z) ,
  [| (x <> 0) |]
  &&  ((&((x)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y x )
  **  ((&((x)  # "dlist" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x)  # "dlist" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  [| (0 = 0) |] 
  &&  [| (prev = 0) |] 
  &&  [| (prev = 0) |]
.

Definition dll_free_partial_solve_wit_2_aux := 
forall (x: Z) (prev: Z) (x_2: Z) (y: Z) ,
  [| (x <> 0) |]
  &&  ((&((x)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y x )
  **  ((&((x)  # "dlist" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x)  # "dlist" ->ₛ "data")) # Int  |-> x_2)
|--
  [| (0 = 0) |] 
  &&  [| (prev = 0) |] 
  &&  [| (prev = 0) |] 
  &&  [| (x <> 0) |]
  &&  ((&((x)  # "dlist" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((x)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x)  # "dlist" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep y x )
.

Definition dll_free_partial_solve_wit_2 := dll_free_partial_solve_wit_2_pure -> dll_free_partial_solve_wit_2_aux.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (p_pre: Z) ,
  ((( &( "v" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (dlistrep p_pre 0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_entail_wit_1 := 
forall (p_pre: Z) ,
  (dlistrep p_pre 0 )
|--
  (dlistrep 0 p_pre )
  **  (dlistrep p_pre 0 )
.

Definition reverse_entail_wit_2 := 
forall (w: Z) (v: Z) (x: Z) (y: Z) ,
  [| (v <> 0) |]
  &&  ((&((v)  # "dlist" ->ₛ "next")) # Ptr  |-> w)
  **  (dlistrep y v )
  **  ((&((v)  # "dlist" ->ₛ "prev")) # Ptr  |-> y)
  **  ((&((v)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep w v )
  **  ((( &( "t" ) )) # Ptr  |-> y)
|--
  (dlistrep v y )
  **  (dlistrep y v )
  **  ((( &( "t" ) )) # Ptr  |->_)
.

Definition reverse_return_wit_1 := 
forall (w: Z) (v: Z) ,
  [| (v = 0) |]
  &&  (dlistrep w v )
  **  (dlistrep v w )
|--
  (dlistrep w 0 )
.

Definition reverse_partial_solve_wit_1 := 
forall (w: Z) (v: Z) ,
  [| (v <> 0) |]
  &&  (dlistrep w v )
  **  (dlistrep v w )
|--
  EX (y: Z)  (x: Z) ,
  [| (v <> 0) |]
  &&  ((&((v)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y v )
  **  ((&((v)  # "dlist" ->ₛ "prev")) # Ptr  |-> w)
  **  ((&((v)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep w v )
.

(*----- Function append -----*)

Definition append_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (dlistrep x_pre 0 )
  **  (dlistrep y_pre 0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition append_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x: Z) (y: Z) ,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y x_pre )
  **  ((&((x_pre)  # "dlist" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep y_pre 0 )
|--
  EX (t_prev: Z)  (t_next: Z) ,
  [| (y = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep y_pre 0 )
  **  (dlistrep y x_pre )
  **  ((&((x_pre)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_pre 0 t_prev x_pre )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x)
.

Definition append_entail_wit_2 := 
forall (x_pre: Z) (x: Z) (x_2: Z) (t_prev_2: Z) (y: Z) (t_next_2: Z) (t: Z) (u: Z) (x_3: Z) (y_2: Z) ,
  [| (u <> 0) |] 
  &&  [| (u = t_next_2) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "dlist" ->ₛ "next")) # Ptr  |-> y_2)
  **  (dlistrep y_2 u )
  **  ((&((u)  # "dlist" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((u)  # "dlist" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (dlistrep y 0 )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg x_2 0 t_prev_2 t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x)
|--
  EX (t_prev: Z)  (t_next: Z) ,
  [| (y_2 = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep y 0 )
  **  (dlistrep y_2 u )
  **  ((&((u)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_2 0 t_prev u )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x)
.

Definition append_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre = 0) |]
  &&  (dlistrep x_pre 0 )
  **  (dlistrep y_pre 0 )
|--
  (dlistrep y_pre 0 )
.

Definition append_return_wit_2_1 := 
forall (x_pre: Z) (x_2: Z) (x: Z) (t_prev: Z) (y: Z) (t_next: Z) (t: Z) (u: Z) ,
  [| (y = 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y 0 )
  **  (dlistrep u t )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_2)
|--
  (dlistrep x 0 )
.

Definition append_return_wit_2_2 := 
forall (x_pre: Z) (x_2: Z) (x: Z) (t_prev: Z) (y: Z) (t_next: Z) (t: Z) (u: Z) (x_3: Z) (y_2: Z) ,
  [| (y <> 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y)  # "dlist" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep y_2 y )
  **  ((&((y)  # "dlist" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "dlist" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_2)
|--
  (dlistrep x 0 )
.

Definition append_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <> 0) |]
  &&  (dlistrep x_pre 0 )
  **  (dlistrep y_pre 0 )
|--
  EX (y: Z)  (x: Z) ,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y x_pre )
  **  ((&((x_pre)  # "dlist" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep y_pre 0 )
.

Definition append_partial_solve_wit_2 := 
forall (x_pre: Z) (x_2: Z) (x_3: Z) (t_prev: Z) (y_2: Z) (t_next: Z) (t: Z) (u: Z) ,
  [| (u <> 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep y_2 0 )
  **  (dlistrep u t )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_3 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_2)
|--
  EX (y: Z)  (x: Z) ,
  [| (u <> 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y u )
  **  ((&((u)  # "dlist" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((u)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep y_2 0 )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_3 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_2)
.

Definition append_partial_solve_wit_3 := 
forall (x_pre: Z) (x_2: Z) (x_3: Z) (t_prev: Z) (y_2: Z) (t_next: Z) (t: Z) (u: Z) ,
  [| (y_2 <> 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> y_2)
  **  (dlistrep y_2 0 )
  **  (dlistrep u t )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_3 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_2)
|--
  EX (y: Z)  (x: Z) ,
  [| (y_2 <> 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y_2)  # "dlist" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep y y_2 )
  **  ((&((y_2)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((y_2)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_3 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_2)
.

(*----- Function iter -----*)

Definition iter_entail_wit_1 := 
forall (l_pre: Z) ,
  (dlistrep l_pre 0 )
|--
  EX (p_prev: Z) ,
  (dllseg l_pre 0 p_prev l_pre )
  **  (dlistrep l_pre p_prev )
.

Definition iter_entail_wit_2 := 
forall (l_pre: Z) (p_prev_2: Z) (p: Z) (x: Z) (y: Z) ,
  [| (p <> 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dllseg l_pre 0 p_prev_2 p )
|--
  EX (p_prev: Z) ,
  (dllseg l_pre 0 p_prev y )
  **  (dlistrep y p_prev )
.

Definition iter_return_wit_1 := 
forall (l_pre: Z) (p_prev: Z) (p: Z) ,
  [| (p = 0) |]
  &&  (dllseg l_pre 0 p_prev p )
  **  (dlistrep p p_prev )
|--
  (dlistrep l_pre 0 )
.

Definition iter_partial_solve_wit_1 := 
forall (l_pre: Z) (p_prev: Z) (p: Z) ,
  [| (p <> 0) |]
  &&  (dllseg l_pre 0 p_prev p )
  **  (dlistrep p p_prev )
|--
  EX (y: Z)  (x: Z) ,
  [| (p <> 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x)
  **  (dllseg l_pre 0 p_prev p )
.

(*----- Function iter_back -----*)

Definition iter_back_safety_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (dllseg head_pre 0 l_prev l_pre )
  **  (dlistrep l_pre l_prev )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition iter_back_entail_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) (x: Z) ,
  [| (l_pre <> 0) |]
  &&  (dllseg head_pre 0 l_prev l_pre )
  **  (dlistrep l_pre l_prev )
|--
  EX (p_next: Z)  (p_prev: Z) ,
  [| (l_pre <> 0) |]
  &&  ((&((l_pre)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg head_pre 0 p_prev l_pre )
  **  ((&((l_pre)  # "dlist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep p_next l_pre )
  **  ((&((l_pre)  # "dlist" ->ₛ "data")) # Int  |-> x)
.

Definition iter_back_entail_wit_2 := 
forall (head_pre: Z) (l_pre: Z) (x: Z) (p_next_2: Z) (p_prev_2: Z) (p: Z) ,
  [| (p <> head_pre) |] 
  &&  [| (l_pre <> 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  (dllseg head_pre 0 p_prev_2 p )
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  (dlistrep p_next_2 p )
  **  ((&((l_pre)  # "dlist" ->ₛ "data")) # Int  |-> x)
|--
  EX (p_next: Z)  (p_prev: Z) ,
  [| (l_pre <> 0) |]
  &&  ((&((p_prev_2)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg head_pre 0 p_prev p_prev_2 )
  **  ((&((p_prev_2)  # "dlist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep p_next p_prev_2 )
  **  ((&((l_pre)  # "dlist" ->ₛ "data")) # Int  |-> x)
.

Definition iter_back_return_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) ,
  [| (l_pre = 0) |]
  &&  (dllseg head_pre 0 l_prev l_pre )
  **  (dlistrep l_pre l_prev )
|--
  (dlistrep head_pre 0 )
.

Definition iter_back_return_wit_2 := 
forall (head_pre: Z) (l_pre: Z) (x: Z) (p_next: Z) (p_prev: Z) (p: Z) ,
  [| (p = head_pre) |] 
  &&  [| (l_pre <> 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg head_pre 0 p_prev p )
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep p_next p )
  **  ((&((l_pre)  # "dlist" ->ₛ "data")) # Int  |-> x)
|--
  (dlistrep p 0 )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include dll_shape_Strategy_Correct.

Axiom proof_of_dll_copy_safety_wit_1 : dll_copy_safety_wit_1.
Axiom proof_of_dll_copy_safety_wit_2 : dll_copy_safety_wit_2.
Axiom proof_of_dll_copy_entail_wit_1 : dll_copy_entail_wit_1.
Axiom proof_of_dll_copy_entail_wit_2 : dll_copy_entail_wit_2.
Axiom proof_of_dll_copy_return_wit_1 : dll_copy_return_wit_1.
Axiom proof_of_dll_copy_partial_solve_wit_1_pure : dll_copy_partial_solve_wit_1_pure.
Axiom proof_of_dll_copy_partial_solve_wit_1 : dll_copy_partial_solve_wit_1.
Axiom proof_of_dll_copy_partial_solve_wit_2 : dll_copy_partial_solve_wit_2.
Axiom proof_of_dll_copy_partial_solve_wit_3_pure : dll_copy_partial_solve_wit_3_pure.
Axiom proof_of_dll_copy_partial_solve_wit_3 : dll_copy_partial_solve_wit_3.
Axiom proof_of_dll_free_entail_wit_1 : dll_free_entail_wit_1.
Axiom proof_of_dll_free_entail_wit_2 : dll_free_entail_wit_2.
Axiom proof_of_dll_free_return_wit_1 : dll_free_return_wit_1.
Axiom proof_of_dll_free_partial_solve_wit_1 : dll_free_partial_solve_wit_1.
Axiom proof_of_dll_free_partial_solve_wit_2_pure : dll_free_partial_solve_wit_2_pure.
Axiom proof_of_dll_free_partial_solve_wit_2 : dll_free_partial_solve_wit_2.
Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Axiom proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1.
Axiom proof_of_append_safety_wit_1 : append_safety_wit_1.
Axiom proof_of_append_entail_wit_1 : append_entail_wit_1.
Axiom proof_of_append_entail_wit_2 : append_entail_wit_2.
Axiom proof_of_append_return_wit_1 : append_return_wit_1.
Axiom proof_of_append_return_wit_2_1 : append_return_wit_2_1.
Axiom proof_of_append_return_wit_2_2 : append_return_wit_2_2.
Axiom proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1.
Axiom proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2.
Axiom proof_of_append_partial_solve_wit_3 : append_partial_solve_wit_3.
Axiom proof_of_iter_entail_wit_1 : iter_entail_wit_1.
Axiom proof_of_iter_entail_wit_2 : iter_entail_wit_2.
Axiom proof_of_iter_return_wit_1 : iter_return_wit_1.
Axiom proof_of_iter_partial_solve_wit_1 : iter_partial_solve_wit_1.
Axiom proof_of_iter_back_safety_wit_1 : iter_back_safety_wit_1.
Axiom proof_of_iter_back_entail_wit_1 : iter_back_entail_wit_1.
Axiom proof_of_iter_back_entail_wit_2 : iter_back_entail_wit_2.
Axiom proof_of_iter_back_return_wit_1 : iter_back_return_wit_1.
Axiom proof_of_iter_back_return_wit_2 : iter_back_return_wit_2.

End VC_Correct.
