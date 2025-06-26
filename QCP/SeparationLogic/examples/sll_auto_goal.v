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
Require Import sll_shape_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import sll_shape_strategy_goal.
From SimpleC.EE Require Import sll_shape_strategy_proof.

(*----- Function sll_copy -----*)

Definition sll_copy_safety_wit_1 := 
forall (x_pre: Z) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (listrep x_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sll_copy_safety_wit_2 := 
forall (x_pre: Z) (retval_next: Z) (retval: Z) (y: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) (x_106: Z) (y_107: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  (listrep y_107 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_107)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (lseg x_pre p )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (lseg y t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sll_copy_entail_wit_1 := 
forall (x_pre: Z) (retval_next: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  (listrep x_pre )
|--
  EX t_data t_next,
  [| (retval <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (lseg x_pre x_pre )
  **  (listrep x_pre )
  **  (lseg retval retval )
.

Definition sll_copy_entail_wit_2 := 
forall (x_pre: Z) (retval_next: Z) (retval: Z) (y: Z) (p: Z) (t_data_2: Z) (t_next_2: Z) (t: Z) (x_106: Z) (y_107: Z) (retval_next_2: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_next_2 = 0) |] 
  &&  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next_2 = 0) |] 
  &&  [| (t_data_2 = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> 0)
  **  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> retval_next_2)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  (listrep y_107 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_107)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval_2)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  (lseg x_pre p )
  **  (lseg y t )
|--
  EX t_data t_next,
  [| (retval_2 <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (lseg x_pre y_107 )
  **  (listrep y_107 )
  **  (lseg y retval_2 )
.

Definition sll_copy_return_wit_1 := 
forall (x_pre: Z) (retval_next: Z) (retval: Z) (y: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) ,
  [| (p = 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (lseg x_pre p )
  **  (listrep p )
  **  (lseg y t )
|--
  (listrep y )
  **  (listrep x_pre )
.

Definition sll_copy_partial_solve_wit_1_pure := 
forall (x_pre: Z) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (listrep x_pre )
|--
  [| (0 = 0) |]
.

Definition sll_copy_partial_solve_wit_1_aux := 
forall (x_pre: Z) ,
  (listrep x_pre )
|--
  [| (0 = 0) |]
  &&  (listrep x_pre )
.

Definition sll_copy_partial_solve_wit_1 := sll_copy_partial_solve_wit_1_pure -> sll_copy_partial_solve_wit_1_aux.

Definition sll_copy_partial_solve_wit_2 := 
forall (x_pre: Z) (retval_next: Z) (retval: Z) (y: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (lseg x_pre p )
  **  (listrep p )
  **  (lseg y t )
|--
  EX y_107 x_106,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  (listrep y_107 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_107)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (lseg x_pre p )
  **  (lseg y t )
.

Definition sll_copy_partial_solve_wit_3_pure := 
forall (x_pre: Z) (retval_next: Z) (retval: Z) (y: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) (x_106: Z) (y_107: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  (listrep y_107 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_107)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (lseg x_pre p )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (lseg y t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 = 0) |]
.

Definition sll_copy_partial_solve_wit_3_aux := 
forall (x_pre: Z) (retval_next: Z) (retval: Z) (y: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) (x_106: Z) (y_107: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  (listrep y_107 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_107)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  (lseg x_pre p )
  **  (lseg y t )
|--
  [| (0 = 0) |] 
  &&  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  (listrep y_107 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_107)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x_106)
  **  (lseg x_pre p )
  **  (lseg y t )
.

Definition sll_copy_partial_solve_wit_3 := sll_copy_partial_solve_wit_3_pure -> sll_copy_partial_solve_wit_3_aux.

(*----- Function sll_free -----*)

Definition sll_free_entail_wit_1 := 
forall (x_pre: Z) ,
  (listrep x_pre )
|--
  (listrep x_pre )
.

Definition sll_free_entail_wit_2 := 
forall (x: Z) (y_141: Z) ,
  [| (x <> 0) |]
  &&  (listrep y_141 )
  **  ((( &( "y" ) )) # Ptr  |-> y_141)
|--
  (listrep y_141 )
  **  ((( &( "y" ) )) # Ptr  |->_)
.

Definition sll_free_return_wit_1 := 
forall (x: Z) ,
  [| (x = 0) |]
  &&  (listrep x )
|--
  TT && emp 
.

Definition sll_free_partial_solve_wit_1 := 
forall (x: Z) ,
  [| (x <> 0) |]
  &&  (listrep x )
|--
  EX y_141 x_140,
  [| (x <> 0) |]
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y_141)
  **  (listrep y_141 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_140)
.

Definition sll_free_partial_solve_wit_2 := 
forall (x: Z) (x_140: Z) (y_141: Z) ,
  [| (x <> 0) |]
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y_141)
  **  (listrep y_141 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_140)
|--
  [| (x <> 0) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_140)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y_141)
  **  (listrep y_141 )
.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (p_pre: Z) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (listrep p_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_entail_wit_1 := 
forall (p_pre: Z) ,
  (listrep p_pre )
|--
  (listrep 0 )
  **  (listrep p_pre )
.

Definition reverse_entail_wit_2 := 
forall (v: Z) (w: Z) (x_175: Z) (y_176: Z) ,
  [| (v <> 0) |]
  &&  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (listrep y_176 )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x_175)
  **  (listrep w )
|--
  (listrep v )
  **  (listrep y_176 )
.

Definition reverse_return_wit_1 := 
forall (v: Z) (w: Z) ,
  [| (v = 0) |]
  &&  (listrep w )
  **  (listrep v )
|--
  (listrep w )
.

Definition reverse_partial_solve_wit_1 := 
forall (v: Z) (w: Z) ,
  [| (v <> 0) |]
  &&  (listrep w )
  **  (listrep v )
|--
  EX y_176 x_175,
  [| (v <> 0) |]
  &&  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> y_176)
  **  (listrep y_176 )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x_175)
  **  (listrep w )
.

(*----- Function append -----*)

Definition append_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (listrep x_pre )
  **  (listrep y_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition append_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x_200: Z) (y_201: Z) ,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_201)
  **  (listrep y_201 )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_200)
  **  (listrep y_pre )
|--
  EX w,
  [| (x_pre <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_201)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y_pre )
  **  (listrep y_201 )
  **  (lseg x_pre x_pre )
.

Definition append_entail_wit_2 := 
forall (x_pre: Z) (x: Z) (y: Z) (w_2: Z) (u: Z) (t: Z) (x_228: Z) (y_229: Z) ,
  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_229)
  **  (listrep y_229 )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_228)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> w_2)
  **  (listrep y )
  **  (lseg x t )
|--
  EX w,
  [| (u <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_229)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y )
  **  (listrep y_229 )
  **  (lseg x u )
.

Definition append_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre = 0) |]
  &&  (listrep x_pre )
  **  (listrep y_pre )
|--
  (listrep y_pre )
.

Definition append_return_wit_2 := 
forall (x_pre: Z) (x: Z) (y: Z) (w: Z) (u: Z) (t: Z) ,
  [| (u = 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y )
  **  (listrep u )
  **  (lseg x t )
|--
  (listrep x )
.

Definition append_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <> 0) |]
  &&  (listrep x_pre )
  **  (listrep y_pre )
|--
  EX y_201 x_200,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_201)
  **  (listrep y_201 )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_200)
  **  (listrep y_pre )
.

Definition append_partial_solve_wit_2 := 
forall (x_pre: Z) (x: Z) (y: Z) (w: Z) (u: Z) (t: Z) ,
  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y )
  **  (listrep u )
  **  (lseg x t )
|--
  EX y_229 x_228,
  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_229)
  **  (listrep y_229 )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_228)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y )
  **  (lseg x t )
.

(*----- Function merge -----*)

Definition merge_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <> 0) |]
  &&  (listrep x_pre )
  **  (listrep y_pre )
|--
  [| (y_pre = y_pre) |] 
  &&  [| (x_pre <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (lseg x_pre x_pre )
  **  (listrep x_pre )
  **  (listrep y_pre )
.

Definition merge_entail_wit_2 := 
forall (x_pre: Z) (z: Z) (x: Z) (t: Z) (y: Z) (x_277: Z) (y_278: Z) (x_281: Z) (y_282: Z) ,
  [| (y_282 <> 0) |] 
  &&  [| (y <> 0) |] 
  &&  [| (y = t) |] 
  &&  [| (x <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y_282 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_281)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_282)
  **  (listrep y_278 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_277)
  **  (lseg z x )
|--
  [| (y_278 = y_278) |] 
  &&  [| (y_282 <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (lseg z y_282 )
  **  (listrep y_282 )
  **  (listrep y_278 )
.

Definition merge_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre = 0) |]
  &&  (listrep x_pre )
  **  (listrep y_pre )
|--
  (listrep y_pre )
.

Definition merge_return_wit_2 := 
forall (x_pre: Z) (z: Z) (x: Z) (t: Z) (y: Z) (x_277: Z) (y_278: Z) (x_281: Z) (y_282: Z) ,
  [| (y_282 = 0) |] 
  &&  [| (y <> 0) |] 
  &&  [| (y = t) |] 
  &&  [| (x <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y_282 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_281)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_278)
  **  (listrep y_278 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_277)
  **  (lseg z x )
|--
  (listrep z )
.

Definition merge_return_wit_3 := 
forall (x_pre: Z) (z: Z) (x: Z) (t: Z) (y: Z) ,
  [| (y = 0) |] 
  &&  [| (y = t) |] 
  &&  [| (x <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (lseg z x )
  **  (listrep x )
  **  (listrep y )
|--
  (listrep z )
.

Definition merge_partial_solve_wit_1 := 
forall (x_pre: Z) (z: Z) (x: Z) (t: Z) (y: Z) ,
  [| (y <> 0) |] 
  &&  [| (y = t) |] 
  &&  [| (x <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (lseg z x )
  **  (listrep x )
  **  (listrep y )
|--
  EX y_278 x_277,
  [| (y <> 0) |] 
  &&  [| (y = t) |] 
  &&  [| (x <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_278)
  **  (listrep y_278 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_277)
  **  (lseg z x )
  **  (listrep x )
.

Definition merge_partial_solve_wit_2 := 
forall (x_pre: Z) (z: Z) (x: Z) (t: Z) (y: Z) (x_277: Z) (y_278: Z) ,
  [| (y <> 0) |] 
  &&  [| (y = t) |] 
  &&  [| (x <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_278)
  **  (listrep y_278 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_277)
  **  (lseg z x )
  **  (listrep x )
|--
  EX y_282 x_281,
  [| (y <> 0) |] 
  &&  [| (y = t) |] 
  &&  [| (x <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y_282)
  **  (listrep y_282 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_281)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_278)
  **  (listrep y_278 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_277)
  **  (lseg z x )
.

(*----- Function multi_append -----*)

Definition multi_append_entail_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (x_321: Z) (y_322: Z) ,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_322)
  **  (listrep y_322 )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_321)
  **  (listrep y_pre )
  **  (listrep z_pre )
|--
  EX v,
  [| (x_pre <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_322)
  **  (listrep y_pre )
  **  (listrep z_pre )
  **  (listrep y_322 )
  **  (lseg x_pre x_pre )
.

Definition multi_append_entail_wit_2 := 
forall (x_pre: Z) (x: Z) (z: Z) (y: Z) (u: Z) (v_2: Z) (t: Z) (x_354: Z) (y_355: Z) (x_358: Z) (y_359: Z) ,
  [| (y <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_359)
  **  (listrep y_359 )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_358)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y_355 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_354)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep z )
  **  (lseg x t )
|--
  EX v,
  [| (u <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_359)
  **  (listrep y_355 )
  **  (listrep z )
  **  (listrep y_359 )
  **  (lseg x u )
.

Definition multi_append_return_wit_1 := 
forall (x_pre: Z) (retval: Z) ,
  [| (x_pre = 0) |]
  &&  (listrep retval )
|--
  (listrep retval )
.

Definition multi_append_return_wit_2 := 
forall (x_pre: Z) (x: Z) (y: Z) (u: Z) (v: Z) (t: Z) (retval: Z) ,
  [| (y = 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (listrep retval )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (lseg x t )
|--
  (listrep x )
.

Definition multi_append_return_wit_3 := 
forall (x_pre: Z) (x: Z) (u: Z) (v: Z) (t: Z) (retval: Z) ,
  [| (u = 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (listrep retval )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (lseg x t )
|--
  (listrep x )
.

Definition multi_append_partial_solve_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (x_pre = 0) |]
  &&  (listrep x_pre )
  **  (listrep y_pre )
  **  (listrep z_pre )
|--
  [| (x_pre = 0) |]
  &&  (listrep y_pre )
  **  (listrep z_pre )
.

Definition multi_append_partial_solve_wit_2 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <> 0) |]
  &&  (listrep x_pre )
  **  (listrep y_pre )
  **  (listrep z_pre )
|--
  EX y_322 x_321,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_322)
  **  (listrep y_322 )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_321)
  **  (listrep y_pre )
  **  (listrep z_pre )
.

Definition multi_append_partial_solve_wit_3 := 
forall (x_pre: Z) (x: Z) (z: Z) (y: Z) (u: Z) (v: Z) (t: Z) ,
  [| (y <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
|--
  EX y_355 x_354,
  [| (y <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_355)
  **  (listrep y_355 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_354)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
.

Definition multi_append_partial_solve_wit_4 := 
forall (x_pre: Z) (x: Z) (z: Z) (y: Z) (u: Z) (v: Z) (t: Z) (x_354: Z) (y_355: Z) ,
  [| (y <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y_355 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_354)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
|--
  EX y_359 x_358,
  [| (y <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_359)
  **  (listrep y_359 )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_358)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y_355 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_354)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep z )
  **  (lseg x t )
.

Definition multi_append_partial_solve_wit_5 := 
forall (x_pre: Z) (x: Z) (z: Z) (y: Z) (u: Z) (v: Z) (t: Z) ,
  [| (y = 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y )
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
|--
  [| (y = 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (listrep u )
  **  (listrep z )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (lseg x t )
.

Definition multi_append_partial_solve_wit_6 := 
forall (x_pre: Z) (x: Z) (z: Z) (y: Z) (u: Z) (v: Z) (t: Z) ,
  [| (u = 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y )
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
|--
  [| (u = 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (listrep y )
  **  (listrep z )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (lseg x t )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_shape_Strategy_Correct.

Axiom proof_of_sll_copy_safety_wit_1 : sll_copy_safety_wit_1.
Axiom proof_of_sll_copy_safety_wit_2 : sll_copy_safety_wit_2.
Axiom proof_of_sll_copy_entail_wit_1 : sll_copy_entail_wit_1.
Axiom proof_of_sll_copy_entail_wit_2 : sll_copy_entail_wit_2.
Axiom proof_of_sll_copy_return_wit_1 : sll_copy_return_wit_1.
Axiom proof_of_sll_copy_partial_solve_wit_1_pure : sll_copy_partial_solve_wit_1_pure.
Axiom proof_of_sll_copy_partial_solve_wit_1 : sll_copy_partial_solve_wit_1.
Axiom proof_of_sll_copy_partial_solve_wit_2 : sll_copy_partial_solve_wit_2.
Axiom proof_of_sll_copy_partial_solve_wit_3_pure : sll_copy_partial_solve_wit_3_pure.
Axiom proof_of_sll_copy_partial_solve_wit_3 : sll_copy_partial_solve_wit_3.
Axiom proof_of_sll_free_entail_wit_1 : sll_free_entail_wit_1.
Axiom proof_of_sll_free_entail_wit_2 : sll_free_entail_wit_2.
Axiom proof_of_sll_free_return_wit_1 : sll_free_return_wit_1.
Axiom proof_of_sll_free_partial_solve_wit_1 : sll_free_partial_solve_wit_1.
Axiom proof_of_sll_free_partial_solve_wit_2 : sll_free_partial_solve_wit_2.
Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Axiom proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1.
Axiom proof_of_append_safety_wit_1 : append_safety_wit_1.
Axiom proof_of_append_entail_wit_1 : append_entail_wit_1.
Axiom proof_of_append_entail_wit_2 : append_entail_wit_2.
Axiom proof_of_append_return_wit_1 : append_return_wit_1.
Axiom proof_of_append_return_wit_2 : append_return_wit_2.
Axiom proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1.
Axiom proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2.
Axiom proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Axiom proof_of_merge_entail_wit_2 : merge_entail_wit_2.
Axiom proof_of_merge_return_wit_1 : merge_return_wit_1.
Axiom proof_of_merge_return_wit_2 : merge_return_wit_2.
Axiom proof_of_merge_return_wit_3 : merge_return_wit_3.
Axiom proof_of_merge_partial_solve_wit_1 : merge_partial_solve_wit_1.
Axiom proof_of_merge_partial_solve_wit_2 : merge_partial_solve_wit_2.
Axiom proof_of_multi_append_entail_wit_1 : multi_append_entail_wit_1.
Axiom proof_of_multi_append_entail_wit_2 : multi_append_entail_wit_2.
Axiom proof_of_multi_append_return_wit_1 : multi_append_return_wit_1.
Axiom proof_of_multi_append_return_wit_2 : multi_append_return_wit_2.
Axiom proof_of_multi_append_return_wit_3 : multi_append_return_wit_3.
Axiom proof_of_multi_append_partial_solve_wit_1 : multi_append_partial_solve_wit_1.
Axiom proof_of_multi_append_partial_solve_wit_2 : multi_append_partial_solve_wit_2.
Axiom proof_of_multi_append_partial_solve_wit_3 : multi_append_partial_solve_wit_3.
Axiom proof_of_multi_append_partial_solve_wit_4 : multi_append_partial_solve_wit_4.
Axiom proof_of_multi_append_partial_solve_wit_5 : multi_append_partial_solve_wit_5.
Axiom proof_of_multi_append_partial_solve_wit_6 : multi_append_partial_solve_wit_6.

End VC_Correct.
