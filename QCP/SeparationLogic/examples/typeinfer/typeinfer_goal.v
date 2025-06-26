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
Require Import typeinfer_lib.
Import naive_C_Rules.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import typeinfer_strategy_goal.
Require Import typeinfer_strategy_proof.

(*----- Function atype_unify -----*)

Definition atype_unify_safety_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition atype_unify_return_wit_1_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1 tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify_return_wit_1_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel (TVar (n)) tr2 s_pre s_post_3 ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1 tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify_return_wit_2_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (tr = None) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1 tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify_return_wit_2_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1 tr2 s_pre s_post_3 ) |] 
  &&  [| (tr = None) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1 tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify_return_wit_3_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (t1_t <> 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1 tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify_return_wit_3_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1 tr2 s_pre s_post_3 ) |] 
  &&  [| (t1_t <> 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1 tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify_partial_solve_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) ,
  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify_partial_solve_wit_2_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (t1_t = 3) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (3 = 3) |]
.

Definition atype_unify_partial_solve_wit_2_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (t1_t = 3) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (3 = 3) |] 
  &&  [| (t1_t = 3) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type_aux t1_pre 3 tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify_partial_solve_wit_2 := atype_unify_partial_solve_wit_2_pure -> atype_unify_partial_solve_wit_2_aux.

Definition atype_unify_partial_solve_wit_3_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) ,
  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  ((( &( "tp" ) )) # Ptr  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |]
.

Definition atype_unify_partial_solve_wit_3_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) ,
  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t2_pre tr2 )
.

Definition atype_unify_partial_solve_wit_3 := atype_unify_partial_solve_wit_3_pure -> atype_unify_partial_solve_wit_3_aux.

Definition atype_unify_partial_solve_wit_4_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
|--
  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |]
.

Definition atype_unify_partial_solve_wit_4_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t2_pre tr2 )
|--
  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t2_pre tr2 )
.

Definition atype_unify_partial_solve_wit_4 := atype_unify_partial_solve_wit_4_pure -> atype_unify_partial_solve_wit_4_aux.

Definition atype_unify_partial_solve_wit_5_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr_2: (@option TypeTree)) (retval: Z) (tr: TypeTree) ,
  [| (tr_2 = (Some (tr))) |] 
  &&  [| (solution_at s_pre n tr ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (solution_at s_pre n tr ) |]
.

Definition atype_unify_partial_solve_wit_5_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) ,
  [| (tr = (Some (tr_2))) |] 
  &&  [| (solution_at s_pre n tr_2 ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t2_pre tr2 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (solution_at s_pre n tr_2 ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t2_pre tr2 )
.

Definition atype_unify_partial_solve_wit_5 := atype_unify_partial_solve_wit_5_pure -> atype_unify_partial_solve_wit_5_aux.

Definition atype_unify_partial_solve_wit_6_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval: Z) ,
  [| (repr_rel_node s_pre (TVar (n)) tr_repr ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  ((( &( "r" ) )) # Int  |->_)
  **  (store_type retval tr_repr )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
|--
  [| (repr_rel_node s_pre (TVar (n)) tr_repr ) |]
.

Definition atype_unify_partial_solve_wit_6_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) ,
  [| (repr_rel_node s_pre (TVar (n)) tr_repr ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t2_pre tr2 )
|--
  [| (repr_rel_node s_pre (TVar (n)) tr_repr ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type retval_2 tr_repr )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify_partial_solve_wit_6 := atype_unify_partial_solve_wit_6_pure -> atype_unify_partial_solve_wit_6_aux.

Definition atype_unify_partial_solve_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (s_post: sol) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type retval_2 tr_repr )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  [| (retval_3 <> 0) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify_partial_solve_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (s_post: sol) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (unify_rel (TVar (n)) tr2 s_pre s_post ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type retval_2 tr_repr )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  [| (retval_3 = 0) |] 
  &&  [| (unify_rel (TVar (n)) tr2 s_pre s_post ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify_partial_solve_wit_9_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
|--
  [| (0 = 0) |] 
  &&  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |]
.

Definition atype_unify_partial_solve_wit_9_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t2_pre tr2 )
|--
  [| (0 = 0) |] 
  &&  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n 0 tr )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify_partial_solve_wit_9 := atype_unify_partial_solve_wit_9_pure -> atype_unify_partial_solve_wit_9_aux.

Definition atype_unify_partial_solve_wit_10_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (tr = None) |] 
  &&  [| (repr_rel_node s_pre tr1 tr1 ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
|--
  [| (repr_rel_node s_pre tr1 tr1 ) |]
.

Definition atype_unify_partial_solve_wit_10_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (tr = None) |] 
  &&  [| (repr_rel_node s_pre tr1 tr1 ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  [| (repr_rel_node s_pre tr1 tr1 ) |] 
  &&  [| (tr = None) |] 
  &&  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify_partial_solve_wit_10 := atype_unify_partial_solve_wit_10_pure -> atype_unify_partial_solve_wit_10_aux.

Definition atype_unify_partial_solve_wit_11_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (t1_t <> 3) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (t1_t <> 3) |]
.

Definition atype_unify_partial_solve_wit_11_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (t1_t <> 3) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (t1_t <> 3) |] 
  &&  [| (t1_t <> 3) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify_partial_solve_wit_11 := atype_unify_partial_solve_wit_11_pure -> atype_unify_partial_solve_wit_11_aux.

Definition atype_unify_partial_solve_wit_12_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (repr_rel_node s_pre tr1 tr1 ) |] 
  &&  [| (t1_t <> 3) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
|--
  [| (repr_rel_node s_pre tr1 tr1 ) |]
.

Definition atype_unify_partial_solve_wit_12_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (repr_rel_node s_pre tr1 tr1 ) |] 
  &&  [| (t1_t <> 3) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (repr_rel_node s_pre tr1 tr1 ) |] 
  &&  [| (t1_t <> 3) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify_partial_solve_wit_12 := atype_unify_partial_solve_wit_12_pure -> atype_unify_partial_solve_wit_12_aux.

Definition atype_unify_which_implies_wit_1 := 
forall (tr1: TypeTree) (t1: Z) ,
  (store_type t1 tr1 )
|--
  EX t1_t,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
.

Definition atype_unify_which_implies_wit_2 := 
forall (tr1: TypeTree) (t1: Z) (t1_t: Z) ,
  [| (t1_t = 3) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
|--
  EX n,
  [| (t1_t = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify_which_implies_wit_3 := 
forall (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (t1: Z) (tp: Z) ,
  [| (tp <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |]
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  EX tr,
  [| (tr_opt = (Some (tr))) |] 
  &&  [| (solution_at s_pre n tr ) |]
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify_which_implies_wit_4 := 
forall (tr1: TypeTree) (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t1: Z) (t1_t: Z) ,
  [| (tp = 0) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  [| (tr_opt = None) |] 
  &&  [| (repr_rel_node s_pre tr1 tr1 ) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1 tr1 )
.

Definition atype_unify_which_implies_wit_5 := 
forall (tr1: TypeTree) (s_pre: sol) (t1: Z) (t1_t: Z) ,
  [| (t1_t <> 3) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (repr_rel_node s_pre tr1 tr1 ) |]
  &&  (store_type t1 tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

(*----- Function atype_unify1 -----*)

Definition atype_unify1_safety_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) ,
  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition atype_unify1_return_wit_1_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify1_return_wit_1_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev (TVar (n)) s_pre s_post_3 ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify1_return_wit_2_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (tr = None) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify1_return_wit_2_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2 s_pre s_post_3 ) |] 
  &&  [| (tr = None) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify1_return_wit_3_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (t2_t <> 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify1_return_wit_3_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2 s_pre s_post_3 ) |] 
  &&  [| (t2_t <> 3) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2 s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify1_partial_solve_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) ,
  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_2_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) ,
  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  [| (3 = 3) |]
.

Definition atype_unify1_partial_solve_wit_2_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) ,
  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  [| (3 = 3) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type_aux t2_pre 3 tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_2 := atype_unify1_partial_solve_wit_2_pure -> atype_unify1_partial_solve_wit_2_aux.

Definition atype_unify1_partial_solve_wit_3_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) ,
  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((( &( "tp" ) )) # Ptr  |->_)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |]
.

Definition atype_unify1_partial_solve_wit_3_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) ,
  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_3 := atype_unify1_partial_solve_wit_3_pure -> atype_unify1_partial_solve_wit_3_aux.

Definition atype_unify1_partial_solve_wit_4_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |]
.

Definition atype_unify1_partial_solve_wit_4_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t1_pre tr1 )
|--
  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_4 := atype_unify1_partial_solve_wit_4_pure -> atype_unify1_partial_solve_wit_4_aux.

Definition atype_unify1_partial_solve_wit_5_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr_2: (@option TypeTree)) (retval: Z) (tr: TypeTree) ,
  [| (tr_2 = (Some (tr))) |] 
  &&  [| (solution_at s_pre n tr ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (solution_at s_pre n tr ) |]
.

Definition atype_unify1_partial_solve_wit_5_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) ,
  [| (tr = (Some (tr_2))) |] 
  &&  [| (solution_at s_pre n tr_2 ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t1_pre tr1 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (solution_at s_pre n tr_2 ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_5 := atype_unify1_partial_solve_wit_5_pure -> atype_unify1_partial_solve_wit_5_aux.

Definition atype_unify1_partial_solve_wit_6_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval: Z) ,
  [| (repr_rel_node s_pre (TVar (n)) tr_repr ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((( &( "r" ) )) # Int  |->_)
  **  (store_type retval tr_repr )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre (TVar (n)) tr_repr ) |]
.

Definition atype_unify1_partial_solve_wit_6_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) ,
  [| (repr_rel_node s_pre (TVar (n)) tr_repr ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t1_pre tr1 )
|--
  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre (TVar (n)) tr_repr ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type retval_2 tr_repr )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify1_partial_solve_wit_6 := atype_unify1_partial_solve_wit_6_pure -> atype_unify1_partial_solve_wit_6_aux.

Definition atype_unify1_partial_solve_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (s_post: sol) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type retval_2 tr_repr )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  [| (retval_3 <> 0) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify1_partial_solve_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (s_post: sol) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (unify_rel tr1_prev (TVar (n)) s_pre s_post ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type retval_2 tr_repr )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  [| (retval_3 = 0) |] 
  &&  [| (unify_rel tr1_prev (TVar (n)) s_pre s_post ) |] 
  &&  [| (tr = (Some (tr_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify1_partial_solve_wit_9_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  [| (0 = 0) |] 
  &&  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |]
.

Definition atype_unify1_partial_solve_wit_9_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t1_pre tr1 )
|--
  [| (0 = 0) |] 
  &&  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n 0 tr )
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_9 := atype_unify1_partial_solve_wit_9_pure -> atype_unify1_partial_solve_wit_9_aux.

Definition atype_unify1_partial_solve_wit_10_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (tr = None) |] 
  &&  [| (repr_rel_node s_pre tr2 tr2 ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2 tr2 ) |]
.

Definition atype_unify1_partial_solve_wit_10_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) ,
  [| (tr = None) |] 
  &&  [| (repr_rel_node s_pre tr2 tr2 ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
  **  (store_type t1_pre tr1 )
|--
  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2 tr2 ) |] 
  &&  [| (tr = None) |] 
  &&  [| (retval = 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify1_partial_solve_wit_10 := atype_unify1_partial_solve_wit_10_pure -> atype_unify1_partial_solve_wit_10_aux.

Definition atype_unify1_partial_solve_wit_11_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) ,
  [| (t2_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  [| (t2_t <> 3) |]
.

Definition atype_unify1_partial_solve_wit_11_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) ,
  [| (t2_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  [| (t2_t <> 3) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_11 := atype_unify1_partial_solve_wit_11_pure -> atype_unify1_partial_solve_wit_11_aux.

Definition atype_unify1_partial_solve_wit_12_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) ,
  [| (repr_rel_node s_pre tr2 tr2 ) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2 tr2 ) |]
.

Definition atype_unify1_partial_solve_wit_12_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) ,
  [| (repr_rel_node s_pre tr2 tr2 ) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2 tr2 ) |] 
  &&  [| (t2_t <> 3) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify1_partial_solve_wit_12 := atype_unify1_partial_solve_wit_12_pure -> atype_unify1_partial_solve_wit_12_aux.

Definition atype_unify1_which_implies_wit_1 := 
forall (tr2: TypeTree) (t2: Z) ,
  (store_type t2 tr2 )
|--
  EX t2_t,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
.

Definition atype_unify1_which_implies_wit_2 := 
forall (tr2: TypeTree) (t2: Z) (t2_t: Z) ,
  [| (t2_t = 3) |]
  &&  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX n,
  [| (t2_t = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |]
  &&  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify1_which_implies_wit_3 := 
forall (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (t2: Z) (tp: Z) ,
  [| (tp <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |]
  &&  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  EX tr,
  [| (tr_opt = (Some (tr))) |] 
  &&  [| (solution_at s_pre n tr ) |]
  &&  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify1_which_implies_wit_4 := 
forall (tr2: TypeTree) (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t2: Z) (t2_t: Z) ,
  [| (tp = 0) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |]
  &&  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  [| (tr_opt = None) |] 
  &&  [| (repr_rel_node s_pre tr2 tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2 tr2 )
.

Definition atype_unify1_which_implies_wit_5 := 
forall (tr2: TypeTree) (s_pre: sol) (t2: Z) (t2_t: Z) ,
  [| (t2_t <> 3) |]
  &&  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (repr_rel_node s_pre tr2 tr2 ) |]
  &&  (store_type t2 tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

(*----- Function atype_unify2 -----*)

Definition atype_unify2_safety_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition atype_unify2_safety_wit_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  [| False |]
.

Definition atype_unify2_safety_wit_3 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  [| False |]
.

Definition atype_unify2_safety_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition atype_unify2_safety_wit_5 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (s_post: sol) ,
  [| ((sol_update (s_pre) (n) (tr2)) = s_post) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t2_pre tr2 )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atype_unify2_safety_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition atype_unify2_safety_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| False |]
.

Definition atype_unify2_safety_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| False |]
.

Definition atype_unify2_safety_wit_9 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition atype_unify2_safety_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (s_post: sol) ,
  [| ((sol_update (s_pre) (n) (tr1)) = s_post) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atype_unify2_safety_wit_11 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t <> t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition atype_unify2_safety_wit_12 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition atype_unify2_safety_wit_13 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atype_unify2_safety_wit_14 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| False |]
.

Definition atype_unify2_safety_wit_15 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_from tr2_from s_pre s_post ) |] 
  &&  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atype_unify2_safety_wit_16 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_from tr2_from s_pre s_post ) |] 
  &&  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| False |]
.

Definition atype_unify2_safety_wit_17 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition atype_unify2_safety_wit_18 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atype_unify2_safety_wit_19 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| False |]
.

Definition atype_unify2_safety_wit_20 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_tfn tr2_tfn s_pre s_post ) |] 
  &&  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atype_unify2_safety_wit_21 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_tfn tr2_tfn s_pre s_post ) |] 
  &&  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| False |]
.

Definition atype_unify2_safety_wit_22 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) ,
  [| (n = m) |] 
  &&  [| (t1_t = 0) |] 
  &&  [| (t1_t = 0) |] 
  &&  [| (tr1 = (TAtom (n))) |] 
  &&  [| (tr2 = (TAtom (m))) |] 
  &&  [| (t1_t <> 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition atype_unify2_safety_wit_23 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) ,
  [| (n <> m) |] 
  &&  [| (t1_t = 0) |] 
  &&  [| (t1_t = 0) |] 
  &&  [| (tr1 = (TAtom (n))) |] 
  &&  [| (tr2 = (TAtom (m))) |] 
  &&  [| (t1_t <> 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition atype_unify2_entail_wit_1_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_1_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_2_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_2_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_3_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_3_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_4_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_4_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_return_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (EX s_post,
  [| (1 = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (1 <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (s_post_3: sol) ,
  [| ((sol_update (s_pre) (n) (tr2)) = s_post_3) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (EX s_post,
  [| (0 = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (0 <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_3 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (EX s_post,
  [| (1 = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (1 <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (s_post_3: sol) ,
  [| ((sol_update (s_pre) (n) (tr1)) = s_post_3) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (EX s_post,
  [| (0 = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (0 <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_5 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t <> t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  (EX s_post,
  [| (2 = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (2 <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_7_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_4: sol) (retval_2: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (unify_rel tr1_from tr2_from s_pre s_post_4 ) |] 
  &&  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_7_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_4: sol) (retval_2: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_to tr2_to s_post_4 s_post_3 ) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (unify_rel tr1_from tr2_from s_pre s_post_4 ) |] 
  &&  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_9_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_4: sol) (retval_2: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (unify_rel tr1_tfn tr2_tfn s_pre s_post_4 ) |] 
  &&  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_9_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_4: sol) (retval_2: Z) (s_post_3: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_rand tr2_rand s_post_4 s_post_3 ) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (unify_rel tr1_tfn tr2_tfn s_pre s_post_4 ) |] 
  &&  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (EX s_post,
  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (retval <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) ,
  [| (n = m) |] 
  &&  [| (t1_t = 0) |] 
  &&  [| (t1_t = 0) |] 
  &&  [| (tr1 = (TAtom (n))) |] 
  &&  [| (tr2 = (TAtom (m))) |] 
  &&  [| (t1_t <> 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  (EX s_post,
  [| (0 = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (0 <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_return_wit_11 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) ,
  [| (n <> m) |] 
  &&  [| (t1_t = 0) |] 
  &&  [| (t1_t = 0) |] 
  &&  [| (tr1 = (TAtom (n))) |] 
  &&  [| (tr2 = (TAtom (m))) |] 
  &&  [| (t1_t <> 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  (EX s_post,
  [| (2 = 0) |] 
  &&  [| (unify_rel tr1_prev tr2_prev s_pre s_post ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
  ||
  (EX s_post_2,
  [| (2 <> 0) |]
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 ))
.

Definition atype_unify2_partial_solve_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) ,
  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_partial_solve_wit_2_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (3 = 3) |]
.

Definition atype_unify2_partial_solve_wit_2_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (3 = 3) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type_aux t1_pre 3 tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_partial_solve_wit_2 := atype_unify2_partial_solve_wit_2_pure -> atype_unify2_partial_solve_wit_2_aux.

Definition atype_unify2_partial_solve_wit_3_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) ,
  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "occur" ) )) # Int  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |]
.

Definition atype_unify2_partial_solve_wit_3_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) ,
  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_3 := atype_unify2_partial_solve_wit_3_pure -> atype_unify2_partial_solve_wit_3_aux.

Definition atype_unify2_partial_solve_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_5_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval_2: Z) (retval: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_type retval tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |]
.

Definition atype_unify2_partial_solve_wit_5_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (retval_2: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  (store_type retval_2 tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr2 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |] 
  &&  [| (t1_t = 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type retval_2 tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_5 := atype_unify2_partial_solve_wit_5_pure -> atype_unify2_partial_solve_wit_5_aux.

Definition atype_unify2_partial_solve_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) ,
  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_7_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (3 = 3) |]
.

Definition atype_unify2_partial_solve_wit_7_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (3 = 3) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type_aux t2_pre 3 tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_7 := atype_unify2_partial_solve_wit_7_pure -> atype_unify2_partial_solve_wit_7_aux.

Definition atype_unify2_partial_solve_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) ,
  [| (3 = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_9_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) ,
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "occur" ) )) # Int  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |]
.

Definition atype_unify2_partial_solve_wit_9_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) ,
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_9 := atype_unify2_partial_solve_wit_9_pure -> atype_unify2_partial_solve_wit_9_aux.

Definition atype_unify2_partial_solve_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_11_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval_2: Z) (retval: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_type retval tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |]
.

Definition atype_unify2_partial_solve_wit_11_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (retval_2: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type t1_pre tr1 )
  **  (store_type retval_2 tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (not_occur_final s_pre n tr1 ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |] 
  &&  [| (t2_t = 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_type retval_2 tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_11 := atype_unify2_partial_solve_wit_11_pure -> atype_unify2_partial_solve_wit_11_aux.

Definition atype_unify2_partial_solve_wit_12_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (1 = 1) |] 
  &&  [| (1 = t2_t) |]
.

Definition atype_unify2_partial_solve_wit_12_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (1 = 1) |] 
  &&  [| (1 = t2_t) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t1_pre 1 tr1 )
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_12 := atype_unify2_partial_solve_wit_12_pure -> atype_unify2_partial_solve_wit_12_aux.

Definition atype_unify2_partial_solve_wit_13 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) ,
  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (1 = 1) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  (store_type t1_from tr1_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  (store_type t2_from tr2_from )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_partial_solve_wit_14 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_from tr2_from s_pre s_post ) |] 
  &&  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_from tr2_from s_pre s_post ) |] 
  &&  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t2_t = 1) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_partial_solve_wit_15_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (2 = 2) |] 
  &&  [| (2 = t2_t) |]
.

Definition atype_unify2_partial_solve_wit_15_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (2 = 2) |] 
  &&  [| (2 = t2_t) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t1_pre 2 tr1 )
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_15 := atype_unify2_partial_solve_wit_15_pure -> atype_unify2_partial_solve_wit_15_aux.

Definition atype_unify2_partial_solve_wit_16 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) ,
  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (2 = 2) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  (store_type t1_tfn tr1_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_partial_solve_wit_17 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_tfn tr2_tfn s_pre s_post ) |] 
  &&  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (unify_rel tr1_tfn tr2_tfn s_pre s_post ) |] 
  &&  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t2_t = 2) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_partial_solve_wit_18_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t <> 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (t1_t = t1_t) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t <> 2) |]
.

Definition atype_unify2_partial_solve_wit_18_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) ,
  [| (t1_t <> 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  [| (t1_t = t1_t) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t <> 2) |] 
  &&  [| (t1_t <> 2) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t = t2_t) |] 
  &&  [| (t2_t <> 3) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (repr_rel_node s_pre tr1_prev tr1 ) |] 
  &&  [| (repr_rel_node s_pre tr2_prev tr2 ) |]
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t2_pre t1_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_18 := atype_unify2_partial_solve_wit_18_pure -> atype_unify2_partial_solve_wit_18_aux.

Definition atype_unify2_which_implies_wit_1 := 
forall (tr1: TypeTree) (t1: Z) ,
  (store_type t1 tr1 )
|--
  EX t1_t,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
.

Definition atype_unify2_which_implies_wit_2 := 
forall (tr1: TypeTree) (t1: Z) (t1_t: Z) ,
  [| (t1_t = 3) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
|--
  EX n,
  [| (t1_t = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr1 = (TVar (n))) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_which_implies_wit_3 := 
forall (tr2: TypeTree) (t2: Z) ,
  (store_type t2 tr2 )
|--
  EX t2_t,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
.

Definition atype_unify2_which_implies_wit_4 := 
forall (tr2: TypeTree) (t2: Z) (t2_t: Z) ,
  [| (t2_t = 3) |]
  &&  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX n,
  [| (t2_t = 3) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (tr2 = (TVar (n))) |]
  &&  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_which_implies_wit_5 := 
forall (tr1: TypeTree) (t1: Z) (t1_t: Z) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
|--
  (store_type t1 tr1 )
.

Definition atype_unify2_which_implies_wit_6 := 
forall (tr2: TypeTree) (tr1: TypeTree) (t1: Z) (t1_t: Z) (t2: Z) (t2_t: Z) ,
  [| (t1_t = 1) |] 
  &&  [| (t1_t = t2_t) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t1 t1_t tr1 )
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX tr2_to t2_to tr2_from t2_from tr1_to t1_to tr1_from t1_from,
  [| (tr1 = (TArrow (tr1_from) (tr1_to))) |] 
  &&  [| (tr2 = (TArrow (tr2_from) (tr2_to))) |] 
  &&  [| (t1_t = 1) |] 
  &&  [| (t2_t = 1) |]
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  (store_type t1_from tr1_from )
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  (store_type t2_from tr2_from )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_which_implies_wit_7 := 
forall (tr2: TypeTree) (tr1: TypeTree) (t1: Z) (t1_t: Z) (t2: Z) (t2_t: Z) ,
  [| (t1_t = 2) |] 
  &&  [| (t1_t = t2_t) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t1 t1_t tr1 )
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX tr2_rand t2_rand tr2_tfn t2_tfn tr1_rand t1_rand tr1_tfn t1_tfn,
  [| (tr1 = (TApply (tr1_tfn) (tr1_rand))) |] 
  &&  [| (tr2 = (TApply (tr2_tfn) (tr2_rand))) |] 
  &&  [| (t1_t = 2) |] 
  &&  [| (t2_t = 2) |]
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  (store_type t1_tfn tr1_tfn )
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_which_implies_wit_8 := 
forall (tr2: TypeTree) (tr1: TypeTree) (t1: Z) (t1_t: Z) (t2: Z) (t2_t: Z) ,
  [| (t1_t = t2_t) |] 
  &&  [| (t1_t <> 3) |] 
  &&  [| (t1_t <> 1) |] 
  &&  [| (t1_t <> 2) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX m n,
  [| (t1_t = 0) |] 
  &&  [| (t2_t = 0) |] 
  &&  [| (tr1 = (TAtom (n))) |] 
  &&  [| (tr2 = (TAtom (m))) |]
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include typeinfer_Strategy_Correct.

Axiom proof_of_atype_unify_safety_wit_1 : atype_unify_safety_wit_1.
Axiom proof_of_atype_unify_return_wit_1_1 : atype_unify_return_wit_1_1.
Axiom proof_of_atype_unify_return_wit_1_2 : atype_unify_return_wit_1_2.
Axiom proof_of_atype_unify_return_wit_2_1 : atype_unify_return_wit_2_1.
Axiom proof_of_atype_unify_return_wit_2_2 : atype_unify_return_wit_2_2.
Axiom proof_of_atype_unify_return_wit_3_1 : atype_unify_return_wit_3_1.
Axiom proof_of_atype_unify_return_wit_3_2 : atype_unify_return_wit_3_2.
Axiom proof_of_atype_unify_partial_solve_wit_1 : atype_unify_partial_solve_wit_1.
Axiom proof_of_atype_unify_partial_solve_wit_2_pure : atype_unify_partial_solve_wit_2_pure.
Axiom proof_of_atype_unify_partial_solve_wit_2 : atype_unify_partial_solve_wit_2.
Axiom proof_of_atype_unify_partial_solve_wit_3_pure : atype_unify_partial_solve_wit_3_pure.
Axiom proof_of_atype_unify_partial_solve_wit_3 : atype_unify_partial_solve_wit_3.
Axiom proof_of_atype_unify_partial_solve_wit_4_pure : atype_unify_partial_solve_wit_4_pure.
Axiom proof_of_atype_unify_partial_solve_wit_4 : atype_unify_partial_solve_wit_4.
Axiom proof_of_atype_unify_partial_solve_wit_5_pure : atype_unify_partial_solve_wit_5_pure.
Axiom proof_of_atype_unify_partial_solve_wit_5 : atype_unify_partial_solve_wit_5.
Axiom proof_of_atype_unify_partial_solve_wit_6_pure : atype_unify_partial_solve_wit_6_pure.
Axiom proof_of_atype_unify_partial_solve_wit_6 : atype_unify_partial_solve_wit_6.
Axiom proof_of_atype_unify_partial_solve_wit_7 : atype_unify_partial_solve_wit_7.
Axiom proof_of_atype_unify_partial_solve_wit_8 : atype_unify_partial_solve_wit_8.
Axiom proof_of_atype_unify_partial_solve_wit_9_pure : atype_unify_partial_solve_wit_9_pure.
Axiom proof_of_atype_unify_partial_solve_wit_9 : atype_unify_partial_solve_wit_9.
Axiom proof_of_atype_unify_partial_solve_wit_10_pure : atype_unify_partial_solve_wit_10_pure.
Axiom proof_of_atype_unify_partial_solve_wit_10 : atype_unify_partial_solve_wit_10.
Axiom proof_of_atype_unify_partial_solve_wit_11_pure : atype_unify_partial_solve_wit_11_pure.
Axiom proof_of_atype_unify_partial_solve_wit_11 : atype_unify_partial_solve_wit_11.
Axiom proof_of_atype_unify_partial_solve_wit_12_pure : atype_unify_partial_solve_wit_12_pure.
Axiom proof_of_atype_unify_partial_solve_wit_12 : atype_unify_partial_solve_wit_12.
Axiom proof_of_atype_unify_which_implies_wit_1 : atype_unify_which_implies_wit_1.
Axiom proof_of_atype_unify_which_implies_wit_2 : atype_unify_which_implies_wit_2.
Axiom proof_of_atype_unify_which_implies_wit_3 : atype_unify_which_implies_wit_3.
Axiom proof_of_atype_unify_which_implies_wit_4 : atype_unify_which_implies_wit_4.
Axiom proof_of_atype_unify_which_implies_wit_5 : atype_unify_which_implies_wit_5.
Axiom proof_of_atype_unify1_safety_wit_1 : atype_unify1_safety_wit_1.
Axiom proof_of_atype_unify1_return_wit_1_1 : atype_unify1_return_wit_1_1.
Axiom proof_of_atype_unify1_return_wit_1_2 : atype_unify1_return_wit_1_2.
Axiom proof_of_atype_unify1_return_wit_2_1 : atype_unify1_return_wit_2_1.
Axiom proof_of_atype_unify1_return_wit_2_2 : atype_unify1_return_wit_2_2.
Axiom proof_of_atype_unify1_return_wit_3_1 : atype_unify1_return_wit_3_1.
Axiom proof_of_atype_unify1_return_wit_3_2 : atype_unify1_return_wit_3_2.
Axiom proof_of_atype_unify1_partial_solve_wit_1 : atype_unify1_partial_solve_wit_1.
Axiom proof_of_atype_unify1_partial_solve_wit_2_pure : atype_unify1_partial_solve_wit_2_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_2 : atype_unify1_partial_solve_wit_2.
Axiom proof_of_atype_unify1_partial_solve_wit_3_pure : atype_unify1_partial_solve_wit_3_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_3 : atype_unify1_partial_solve_wit_3.
Axiom proof_of_atype_unify1_partial_solve_wit_4_pure : atype_unify1_partial_solve_wit_4_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_4 : atype_unify1_partial_solve_wit_4.
Axiom proof_of_atype_unify1_partial_solve_wit_5_pure : atype_unify1_partial_solve_wit_5_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_5 : atype_unify1_partial_solve_wit_5.
Axiom proof_of_atype_unify1_partial_solve_wit_6_pure : atype_unify1_partial_solve_wit_6_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_6 : atype_unify1_partial_solve_wit_6.
Axiom proof_of_atype_unify1_partial_solve_wit_7 : atype_unify1_partial_solve_wit_7.
Axiom proof_of_atype_unify1_partial_solve_wit_8 : atype_unify1_partial_solve_wit_8.
Axiom proof_of_atype_unify1_partial_solve_wit_9_pure : atype_unify1_partial_solve_wit_9_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_9 : atype_unify1_partial_solve_wit_9.
Axiom proof_of_atype_unify1_partial_solve_wit_10_pure : atype_unify1_partial_solve_wit_10_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_10 : atype_unify1_partial_solve_wit_10.
Axiom proof_of_atype_unify1_partial_solve_wit_11_pure : atype_unify1_partial_solve_wit_11_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_11 : atype_unify1_partial_solve_wit_11.
Axiom proof_of_atype_unify1_partial_solve_wit_12_pure : atype_unify1_partial_solve_wit_12_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_12 : atype_unify1_partial_solve_wit_12.
Axiom proof_of_atype_unify1_which_implies_wit_1 : atype_unify1_which_implies_wit_1.
Axiom proof_of_atype_unify1_which_implies_wit_2 : atype_unify1_which_implies_wit_2.
Axiom proof_of_atype_unify1_which_implies_wit_3 : atype_unify1_which_implies_wit_3.
Axiom proof_of_atype_unify1_which_implies_wit_4 : atype_unify1_which_implies_wit_4.
Axiom proof_of_atype_unify1_which_implies_wit_5 : atype_unify1_which_implies_wit_5.
Axiom proof_of_atype_unify2_safety_wit_1 : atype_unify2_safety_wit_1.
Axiom proof_of_atype_unify2_safety_wit_2 : atype_unify2_safety_wit_2.
Axiom proof_of_atype_unify2_safety_wit_3 : atype_unify2_safety_wit_3.
Axiom proof_of_atype_unify2_safety_wit_4 : atype_unify2_safety_wit_4.
Axiom proof_of_atype_unify2_safety_wit_5 : atype_unify2_safety_wit_5.
Axiom proof_of_atype_unify2_safety_wit_6 : atype_unify2_safety_wit_6.
Axiom proof_of_atype_unify2_safety_wit_7 : atype_unify2_safety_wit_7.
Axiom proof_of_atype_unify2_safety_wit_8 : atype_unify2_safety_wit_8.
Axiom proof_of_atype_unify2_safety_wit_9 : atype_unify2_safety_wit_9.
Axiom proof_of_atype_unify2_safety_wit_10 : atype_unify2_safety_wit_10.
Axiom proof_of_atype_unify2_safety_wit_11 : atype_unify2_safety_wit_11.
Axiom proof_of_atype_unify2_safety_wit_12 : atype_unify2_safety_wit_12.
Axiom proof_of_atype_unify2_safety_wit_13 : atype_unify2_safety_wit_13.
Axiom proof_of_atype_unify2_safety_wit_14 : atype_unify2_safety_wit_14.
Axiom proof_of_atype_unify2_safety_wit_15 : atype_unify2_safety_wit_15.
Axiom proof_of_atype_unify2_safety_wit_16 : atype_unify2_safety_wit_16.
Axiom proof_of_atype_unify2_safety_wit_17 : atype_unify2_safety_wit_17.
Axiom proof_of_atype_unify2_safety_wit_18 : atype_unify2_safety_wit_18.
Axiom proof_of_atype_unify2_safety_wit_19 : atype_unify2_safety_wit_19.
Axiom proof_of_atype_unify2_safety_wit_20 : atype_unify2_safety_wit_20.
Axiom proof_of_atype_unify2_safety_wit_21 : atype_unify2_safety_wit_21.
Axiom proof_of_atype_unify2_safety_wit_22 : atype_unify2_safety_wit_22.
Axiom proof_of_atype_unify2_safety_wit_23 : atype_unify2_safety_wit_23.
Axiom proof_of_atype_unify2_entail_wit_1_1 : atype_unify2_entail_wit_1_1.
Axiom proof_of_atype_unify2_entail_wit_1_2 : atype_unify2_entail_wit_1_2.
Axiom proof_of_atype_unify2_entail_wit_2_1 : atype_unify2_entail_wit_2_1.
Axiom proof_of_atype_unify2_entail_wit_2_2 : atype_unify2_entail_wit_2_2.
Axiom proof_of_atype_unify2_entail_wit_3_1 : atype_unify2_entail_wit_3_1.
Axiom proof_of_atype_unify2_entail_wit_3_2 : atype_unify2_entail_wit_3_2.
Axiom proof_of_atype_unify2_entail_wit_4_1 : atype_unify2_entail_wit_4_1.
Axiom proof_of_atype_unify2_entail_wit_4_2 : atype_unify2_entail_wit_4_2.
Axiom proof_of_atype_unify2_return_wit_1 : atype_unify2_return_wit_1.
Axiom proof_of_atype_unify2_return_wit_2 : atype_unify2_return_wit_2.
Axiom proof_of_atype_unify2_return_wit_3 : atype_unify2_return_wit_3.
Axiom proof_of_atype_unify2_return_wit_4 : atype_unify2_return_wit_4.
Axiom proof_of_atype_unify2_return_wit_5 : atype_unify2_return_wit_5.
Axiom proof_of_atype_unify2_return_wit_6 : atype_unify2_return_wit_6.
Axiom proof_of_atype_unify2_return_wit_7_1 : atype_unify2_return_wit_7_1.
Axiom proof_of_atype_unify2_return_wit_7_2 : atype_unify2_return_wit_7_2.
Axiom proof_of_atype_unify2_return_wit_8 : atype_unify2_return_wit_8.
Axiom proof_of_atype_unify2_return_wit_9_1 : atype_unify2_return_wit_9_1.
Axiom proof_of_atype_unify2_return_wit_9_2 : atype_unify2_return_wit_9_2.
Axiom proof_of_atype_unify2_return_wit_10 : atype_unify2_return_wit_10.
Axiom proof_of_atype_unify2_return_wit_11 : atype_unify2_return_wit_11.
Axiom proof_of_atype_unify2_partial_solve_wit_1 : atype_unify2_partial_solve_wit_1.
Axiom proof_of_atype_unify2_partial_solve_wit_2_pure : atype_unify2_partial_solve_wit_2_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_2 : atype_unify2_partial_solve_wit_2.
Axiom proof_of_atype_unify2_partial_solve_wit_3_pure : atype_unify2_partial_solve_wit_3_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_3 : atype_unify2_partial_solve_wit_3.
Axiom proof_of_atype_unify2_partial_solve_wit_4 : atype_unify2_partial_solve_wit_4.
Axiom proof_of_atype_unify2_partial_solve_wit_5_pure : atype_unify2_partial_solve_wit_5_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_5 : atype_unify2_partial_solve_wit_5.
Axiom proof_of_atype_unify2_partial_solve_wit_6 : atype_unify2_partial_solve_wit_6.
Axiom proof_of_atype_unify2_partial_solve_wit_7_pure : atype_unify2_partial_solve_wit_7_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_7 : atype_unify2_partial_solve_wit_7.
Axiom proof_of_atype_unify2_partial_solve_wit_8 : atype_unify2_partial_solve_wit_8.
Axiom proof_of_atype_unify2_partial_solve_wit_9_pure : atype_unify2_partial_solve_wit_9_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_9 : atype_unify2_partial_solve_wit_9.
Axiom proof_of_atype_unify2_partial_solve_wit_10 : atype_unify2_partial_solve_wit_10.
Axiom proof_of_atype_unify2_partial_solve_wit_11_pure : atype_unify2_partial_solve_wit_11_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_11 : atype_unify2_partial_solve_wit_11.
Axiom proof_of_atype_unify2_partial_solve_wit_12_pure : atype_unify2_partial_solve_wit_12_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_12 : atype_unify2_partial_solve_wit_12.
Axiom proof_of_atype_unify2_partial_solve_wit_13 : atype_unify2_partial_solve_wit_13.
Axiom proof_of_atype_unify2_partial_solve_wit_14 : atype_unify2_partial_solve_wit_14.
Axiom proof_of_atype_unify2_partial_solve_wit_15_pure : atype_unify2_partial_solve_wit_15_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_15 : atype_unify2_partial_solve_wit_15.
Axiom proof_of_atype_unify2_partial_solve_wit_16 : atype_unify2_partial_solve_wit_16.
Axiom proof_of_atype_unify2_partial_solve_wit_17 : atype_unify2_partial_solve_wit_17.
Axiom proof_of_atype_unify2_partial_solve_wit_18_pure : atype_unify2_partial_solve_wit_18_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_18 : atype_unify2_partial_solve_wit_18.
Axiom proof_of_atype_unify2_which_implies_wit_1 : atype_unify2_which_implies_wit_1.
Axiom proof_of_atype_unify2_which_implies_wit_2 : atype_unify2_which_implies_wit_2.
Axiom proof_of_atype_unify2_which_implies_wit_3 : atype_unify2_which_implies_wit_3.
Axiom proof_of_atype_unify2_which_implies_wit_4 : atype_unify2_which_implies_wit_4.
Axiom proof_of_atype_unify2_which_implies_wit_5 : atype_unify2_which_implies_wit_5.
Axiom proof_of_atype_unify2_which_implies_wit_6 : atype_unify2_which_implies_wit_6.
Axiom proof_of_atype_unify2_which_implies_wit_7 : atype_unify2_which_implies_wit_7.
Axiom proof_of_atype_unify2_which_implies_wit_8 : atype_unify2_which_implies_wit_8.

End VC_Correct.
