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
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import dll_shape_strategy_goal.
From SimpleC.EE Require Import dll_shape_strategy_proof.

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
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev: Z) (p: Z) (t_prev: Z) (t_data: Z) (t_next: Z) (t: Z) (x_120: Z) (y_121: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
  **  (dlistrep y_121 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_121)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
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
  EX p_prev t_prev t_data t_next,
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
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev_2: Z) (p: Z) (t_prev_2: Z) (t_data_2: Z) (t_next_2: Z) (t: Z) (x_120: Z) (y_121: Z) (retval_prev_2: Z) (retval_next_2: Z) (retval_2: Z) ,
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
  **  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
  **  (dlistrep y_121 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_121)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> retval_2)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  (dllseg x_pre 0 p_prev_2 p )
  **  (dllseg y 0 0 t )
|--
  EX p_prev t_prev t_data t_next,
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
  **  (dllseg x_pre 0 p_prev y_121 )
  **  (dlistrep y_121 p_prev )
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
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev: Z) (p: Z) (t_prev: Z) (t_data: Z) (t_next: Z) (t: Z) ,
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
  **  (dllseg y 0 0 t )
|--
  EX y_121 x_120,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
  **  (dlistrep y_121 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_121)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_pre 0 p_prev p )
  **  (dllseg y 0 0 t )
.

Definition dll_copy_partial_solve_wit_3_pure := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev: Z) (p: Z) (t_prev: Z) (t_data: Z) (t_next: Z) (t: Z) (x_120: Z) (y_121: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
  **  (dlistrep y_121 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_121)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
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
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (p_prev: Z) (p: Z) (t_prev: Z) (t_data: Z) (t_next: Z) (t: Z) (x_120: Z) (y_121: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (t_prev = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
  **  (dlistrep y_121 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_121)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
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
  &&  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
  **  (dlistrep y_121 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_121)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "dlist" ->ₛ "data")) # Int  |-> x_120)
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
  EX prev,
  (dlistrep x_pre prev )
.

Definition dll_free_entail_wit_2 := 
forall (x: Z) (y_161: Z) ,
  [| (x <> 0) |]
  &&  (dlistrep y_161 x )
  **  ((( &( "y" ) )) # Ptr  |-> y_161)
|--
  EX prev,
  (dlistrep y_161 prev )
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
forall (x: Z) (prev: Z) ,
  [| (x <> 0) |]
  &&  (dlistrep x prev )
|--
  EX y_161 x_160,
  [| (x <> 0) |]
  &&  ((&((x)  # "dlist" ->ₛ "next")) # Ptr  |-> y_161)
  **  (dlistrep y_161 x )
  **  ((&((x)  # "dlist" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x)  # "dlist" ->ₛ "data")) # Int  |-> x_160)
.

Definition dll_free_partial_solve_wit_2_pure := 
forall (x: Z) (prev: Z) (x_160: Z) (y_161: Z) ,
  [| (x <> 0) |]
  &&  ((&((x)  # "dlist" ->ₛ "next")) # Ptr  |-> y_161)
  **  (dlistrep y_161 x )
  **  ((&((x)  # "dlist" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x)  # "dlist" ->ₛ "data")) # Int  |-> x_160)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  ((( &( "y" ) )) # Ptr  |-> y_161)
|--
  [| (0 = 0) |] 
  &&  [| (prev = 0) |] 
  &&  [| (prev = 0) |]
.

Definition dll_free_partial_solve_wit_2_aux := 
forall (x: Z) (prev: Z) (x_160: Z) (y_161: Z) ,
  [| (x <> 0) |]
  &&  ((&((x)  # "dlist" ->ₛ "next")) # Ptr  |-> y_161)
  **  (dlistrep y_161 x )
  **  ((&((x)  # "dlist" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x)  # "dlist" ->ₛ "data")) # Int  |-> x_160)
|--
  [| (0 = 0) |] 
  &&  [| (prev = 0) |] 
  &&  [| (prev = 0) |] 
  &&  [| (x <> 0) |]
  &&  ((&((x)  # "dlist" ->ₛ "data")) # Int  |-> x_160)
  **  ((&((x)  # "dlist" ->ₛ "next")) # Ptr  |-> y_161)
  **  ((&((x)  # "dlist" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep y_161 x )
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
forall (w: Z) (v: Z) (x_197: Z) (y_198: Z) ,
  [| (v <> 0) |]
  &&  ((&((v)  # "dlist" ->ₛ "next")) # Ptr  |-> w)
  **  (dlistrep y_198 v )
  **  ((&((v)  # "dlist" ->ₛ "prev")) # Ptr  |-> y_198)
  **  ((&((v)  # "dlist" ->ₛ "data")) # Int  |-> x_197)
  **  (dlistrep w v )
  **  ((( &( "t" ) )) # Ptr  |-> y_198)
|--
  (dlistrep v y_198 )
  **  (dlistrep y_198 v )
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
  EX y_198 x_197,
  [| (v <> 0) |]
  &&  ((&((v)  # "dlist" ->ₛ "next")) # Ptr  |-> y_198)
  **  (dlistrep y_198 v )
  **  ((&((v)  # "dlist" ->ₛ "prev")) # Ptr  |-> w)
  **  ((&((v)  # "dlist" ->ₛ "data")) # Int  |-> x_197)
  **  (dlistrep w v )
.

(*----- Function append -----*)

Definition append_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x_222: Z) (y_223: Z) ,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "dlist" ->ₛ "next")) # Ptr  |-> y_223)
  **  (dlistrep y_223 x_pre )
  **  ((&((x_pre)  # "dlist" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
  **  (dlistrep y_pre 0 )
|--
  EX t_prev t_next,
  [| (y_223 = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep y_pre 0 )
  **  (dlistrep y_223 x_pre )
  **  ((&((x_pre)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x_pre 0 t_prev x_pre )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
.

Definition append_entail_wit_2 := 
forall (x_pre: Z) (x_222: Z) (x: Z) (t_prev_2: Z) (y: Z) (t_next_2: Z) (t: Z) (u: Z) (x_258: Z) (y_259: Z) ,
  [| (u <> 0) |] 
  &&  [| (u = t_next_2) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "dlist" ->ₛ "next")) # Ptr  |-> y_259)
  **  (dlistrep y_259 u )
  **  ((&((u)  # "dlist" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((u)  # "dlist" ->ₛ "data")) # Int  |-> x_258)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (dlistrep y 0 )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg x 0 t_prev_2 t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
|--
  EX t_prev t_next,
  [| (y_259 = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep y 0 )
  **  (dlistrep y_259 u )
  **  ((&((u)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x 0 t_prev u )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
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
forall (x_pre: Z) (x_222: Z) (x: Z) (t_prev: Z) (y: Z) (t_next: Z) (t: Z) (u: Z) ,
  [| (y = 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y 0 )
  **  (dlistrep u t )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
|--
  (dlistrep x 0 )
.

Definition append_return_wit_2_2 := 
forall (x_pre: Z) (x_222: Z) (x: Z) (t_prev: Z) (y: Z) (t_next: Z) (t: Z) (u: Z) (x_267: Z) (y_268: Z) ,
  [| (y <> 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y)  # "dlist" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep y_268 y )
  **  ((&((y)  # "dlist" ->ₛ "next")) # Ptr  |-> y_268)
  **  ((&((y)  # "dlist" ->ₛ "data")) # Int  |-> x_267)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
|--
  (dlistrep x 0 )
.

Definition append_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <> 0) |]
  &&  (dlistrep x_pre 0 )
  **  (dlistrep y_pre 0 )
|--
  EX y_223 x_222,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "dlist" ->ₛ "next")) # Ptr  |-> y_223)
  **  (dlistrep y_223 x_pre )
  **  ((&((x_pre)  # "dlist" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
  **  (dlistrep y_pre 0 )
.

Definition append_partial_solve_wit_2 := 
forall (x_pre: Z) (x_222: Z) (x: Z) (t_prev: Z) (y: Z) (t_next: Z) (t: Z) (u: Z) ,
  [| (u <> 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep y 0 )
  **  (dlistrep u t )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
|--
  EX y_259 x_258,
  [| (u <> 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "dlist" ->ₛ "next")) # Ptr  |-> y_259)
  **  (dlistrep y_259 u )
  **  ((&((u)  # "dlist" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((u)  # "dlist" ->ₛ "data")) # Int  |-> x_258)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep y 0 )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
.

Definition append_partial_solve_wit_3 := 
forall (x_pre: Z) (x_222: Z) (x: Z) (t_prev: Z) (y: Z) (t_next: Z) (t: Z) (u: Z) ,
  [| (y <> 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep y 0 )
  **  (dlistrep u t )
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
|--
  EX y_268 x_267,
  [| (y <> 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y)  # "dlist" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep y_268 y )
  **  ((&((y)  # "dlist" ->ₛ "next")) # Ptr  |-> y_268)
  **  ((&((y)  # "dlist" ->ₛ "data")) # Int  |-> x_267)
  **  ((&((t)  # "dlist" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "dlist" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg x 0 t_prev t )
  **  ((&((x_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_222)
.

(*----- Function iter -----*)

Definition iter_entail_wit_1 := 
forall (l_pre: Z) ,
  (dlistrep l_pre 0 )
|--
  EX p_prev,
  (dllseg l_pre 0 p_prev l_pre )
  **  (dlistrep l_pre p_prev )
.

Definition iter_entail_wit_2 := 
forall (l_pre: Z) (p_prev_2: Z) (p: Z) (x_291: Z) (y_292: Z) ,
  [| (p <> 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_292)
  **  (dlistrep y_292 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x_291)
  **  (dllseg l_pre 0 p_prev_2 p )
|--
  EX p_prev,
  (dllseg l_pre 0 p_prev y_292 )
  **  (dlistrep y_292 p_prev )
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
  EX y_292 x_291,
  [| (p <> 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> y_292)
  **  (dlistrep y_292 p )
  **  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "dlist" ->ₛ "data")) # Int  |-> x_291)
  **  (dllseg l_pre 0 p_prev p )
.

(*----- Function iter_back -----*)

Definition iter_back_entail_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) (x_319: Z) ,
  [| (l_pre <> 0) |]
  &&  (dllseg head_pre 0 l_prev l_pre )
  **  (dlistrep l_pre l_prev )
|--
  EX p_next p_prev,
  [| (l_pre <> 0) |]
  &&  ((&((l_pre)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg head_pre 0 p_prev l_pre )
  **  ((&((l_pre)  # "dlist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep p_next l_pre )
  **  ((&((l_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_319)
.

Definition iter_back_entail_wit_2 := 
forall (head_pre: Z) (l_pre: Z) (x_319: Z) (p_next_2: Z) (p_prev_2: Z) (p: Z) ,
  [| (p <> head_pre) |] 
  &&  [| (l_pre <> 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  (dllseg head_pre 0 p_prev_2 p )
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  (dlistrep p_next_2 p )
  **  ((&((l_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_319)
|--
  EX p_next p_prev,
  [| (l_pre <> 0) |]
  &&  ((&((p_prev_2)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg head_pre 0 p_prev p_prev_2 )
  **  ((&((p_prev_2)  # "dlist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep p_next p_prev_2 )
  **  ((&((l_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_319)
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
forall (head_pre: Z) (l_pre: Z) (x_319: Z) (p_next: Z) (p_prev: Z) (p: Z) ,
  [| (p = head_pre) |] 
  &&  [| (l_pre <> 0) |]
  &&  ((&((p)  # "dlist" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg head_pre 0 p_prev p )
  **  ((&((p)  # "dlist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep p_next p )
  **  ((&((l_pre)  # "dlist" ->ₛ "data")) # Int  |-> x_319)
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
Axiom proof_of_iter_back_entail_wit_1 : iter_back_entail_wit_1.
Axiom proof_of_iter_back_entail_wit_2 : iter_back_entail_wit_2.
Axiom proof_of_iter_back_return_wit_1 : iter_back_return_wit_1.
Axiom proof_of_iter_back_return_wit_2 : iter_back_return_wit_2.

End VC_Correct.
