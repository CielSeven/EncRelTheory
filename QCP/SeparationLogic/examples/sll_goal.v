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
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import sll_strategy_goal.
Require Import sll_strategy_proof.

(*----- Function length -----*)

Definition length_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition length_safety_wit_2 := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) ,
  [| (l2 = (cons (p_data) (l3))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (n = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (sllseg p_pre p l1 )
|--
  [| ((n + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n + 1 )) |]
.

Definition length_entail_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll p_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (0 = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg p_pre p_pre l1 )
  **  (sll p_pre l2 )
.

Definition length_entail_wit_2 := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) ,
  [| (l2_2 = (cons (p_data) (l3))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (n = (Zlength (l1_2))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg p_pre p l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| ((n + 1 ) = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg p_pre p_next l1 )
  **  (sll p_next l2 )
.

Definition length_return_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (n = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  [| (n = (Zlength (l))) |]
  &&  (sll p_pre l )
.

Definition length_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (n = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  [| (p <> 0) |]
.

Definition length_partial_solve_wit_1_aux := 
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (n = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg p_pre p l1 )
  **  (sll p l2 )
|--
  [| (p <> 0) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (n = (Zlength (l1))) |] 
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sll p l2 )
  **  (sllseg p_pre p l1 )
.

Definition length_partial_solve_wit_1 := length_partial_solve_wit_1_pure -> length_partial_solve_wit_1_aux.

Definition length_which_implies_wit_1 := 
forall (l2: (@list Z)) (p: Z) ,
  [| (p <> 0) |]
  &&  (sll p l2 )
|--
  EX (p_next: Z)  (p_data: Z)  (l3: (@list Z)) ,
  [| (l2 = (cons (p_data) (l3))) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_entail_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  (sll p_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll 0 l1 )
  **  (sll p_pre l2 )
.

Definition reverse_entail_wit_2 := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_next: Z) (v_data: Z) (l2_new: (@list Z)) ,
  [| (l2_2 = (cons (v_data) (l2_new))) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1_2))) (l2_2))) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll v_next l2_new )
  **  (sll w l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v l1 )
  **  (sll v_next l2 )
.

Definition reverse_return_wit_1 := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v = 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w l1 )
  **  (sll v l2 )
|--
  (sll w (rev (l)) )
.

Definition reverse_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  ((( &( "w" ) )) # Ptr  |-> w)
  **  (sll w l1 )
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  (sll v l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (v <> 0) |]
.

Definition reverse_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w l1 )
  **  (sll v l2 )
|--
  [| (v <> 0) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v l2 )
  **  (sll w l1 )
.

Definition reverse_partial_solve_wit_1 := reverse_partial_solve_wit_1_pure -> reverse_partial_solve_wit_1_aux.

Definition reverse_which_implies_wit_1 := 
forall (l2: (@list Z)) (v: Z) ,
  [| (v <> 0) |]
  &&  (sll v l2 )
|--
  EX (v_next: Z)  (v_data: Z)  (l2_new: (@list Z)) ,
  [| (l2 = (cons (v_data) (l2_new))) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> v_next)
  **  (sll v_next l2_new )
.

(*----- Function reverse_alter_style1 -----*)

Definition reverse_alter_style1_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_alter_style1_entail_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  (sll p_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll 0 l1 )
  **  (sll p_pre l2 )
.

Definition reverse_alter_style1_entail_wit_2 := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (vn: Z) (x: Z) (xs: (@list Z)) ,
  [| (l2_2 = (cons (x) (xs))) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1_2))) (l2_2))) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll vn xs )
  **  (sll w l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v l1 )
  **  (sll vn l2 )
.

Definition reverse_alter_style1_return_wit_1 := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v = 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w l1 )
  **  (sll v l2 )
|--
  (sll w (rev (l)) )
.

Definition reverse_alter_style1_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  ((( &( "w" ) )) # Ptr  |-> w)
  **  (sll w l1 )
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  (sll v l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (v <> 0) |]
.

Definition reverse_alter_style1_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (v: Z) (w: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w l1 )
  **  (sll v l2 )
|--
  [| (v <> 0) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v l2 )
  **  (sll w l1 )
.

Definition reverse_alter_style1_partial_solve_wit_1 := reverse_alter_style1_partial_solve_wit_1_pure -> reverse_alter_style1_partial_solve_wit_1_aux.

Definition reverse_alter_style1_which_implies_wit_1 := 
forall (l2: (@list Z)) (v: Z) ,
  [| (v <> 0) |]
  &&  (sll v l2 )
|--
  EX (vn: Z)  (x: Z)  (xs: (@list Z)) ,
  [| (l2 = (cons (x) (xs))) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> vn)
  **  (sll vn xs )
.

(*----- Function reverse_alter_style2 -----*)

Definition reverse_alter_style2_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_alter_style2_entail_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  (sll p_pre l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll 0 l1 )
  **  (sll p_pre l2 )
.

Definition reverse_alter_style2_entail_wit_2 := 
forall (l: (@list Z)) (v_inv: Z) (w_inv: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (v_inv_next: Z) (x: Z) (xs: (@list Z)) ,
  [| (l2_2 = (cons (x) (xs))) |] 
  &&  [| (v_inv <> 0) |] 
  &&  [| (l = (app ((rev (l1_2))) (l2_2))) |]
  &&  ((&((v_inv)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v_inv)  # "list" ->ₛ "next")) # Ptr  |-> w_inv)
  **  (sll v_inv_next xs )
  **  (sll w_inv l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v_inv l1 )
  **  (sll v_inv_next l2 )
.

Definition reverse_alter_style2_return_wit_1 := 
forall (l: (@list Z)) (v_inv: Z) (w_inv: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v_inv = 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w_inv l1 )
  **  (sll v_inv l2 )
|--
  (sll w_inv (rev (l)) )
.

Definition reverse_alter_style2_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (v_inv: Z) (w_inv: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v_inv <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  ((( &( "w" ) )) # Ptr  |-> w_inv)
  **  ((( &( "v" ) )) # Ptr  |-> v_inv)
  **  (sll w_inv l1 )
  **  (sll v_inv l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (v_inv <> 0) |]
.

Definition reverse_alter_style2_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (v_inv: Z) (w_inv: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (v_inv <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w_inv l1 )
  **  (sll v_inv l2 )
|--
  [| (v_inv <> 0) |] 
  &&  [| (v_inv <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v_inv l2 )
  **  (sll w_inv l1 )
.

Definition reverse_alter_style2_partial_solve_wit_1 := reverse_alter_style2_partial_solve_wit_1_pure -> reverse_alter_style2_partial_solve_wit_1_aux.

Definition reverse_alter_style2_which_implies_wit_1 := 
forall (l2: (@list Z)) (v_inv: Z) ,
  [| (v_inv <> 0) |]
  &&  (sll v_inv l2 )
|--
  EX (v_inv_next: Z)  (x: Z)  (xs: (@list Z)) ,
  [| (l2 = (cons (x) (xs))) |]
  &&  ((&((v_inv)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((v_inv)  # "list" ->ₛ "next")) # Ptr  |-> v_inv_next)
  **  (sll v_inv_next xs )
.

(*----- Function reverse_alter_style3 -----*)

Definition reverse_alter_style3_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  ((( &( "v" ) )) # Ptr  |->_)
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll p_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_alter_style3_entail_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) ,
  (sll p_pre l )
|--
  (sll 0 nil )
  **  (sll p_pre l )
.

Definition reverse_alter_style3_entail_wit_2 := 
forall (p_pre: Z) (l: (@list Z)) ,
  (sll 0 nil )
  **  (sll p_pre l )
|--
  [| (0 = 0) |] 
  &&  [| (p_pre = p_pre) |]
  &&  (sll 0 nil )
  **  (sll p_pre l )
.

Definition reverse_alter_style3_entail_wit_3 := 
forall (p_pre: Z) (l: (@list Z)) (w: Z) (v: Z) ,
  [| (w = 0) |] 
  &&  [| (v = p_pre) |]
  &&  (sll w nil )
  **  (sll v l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w l1 )
  **  (sll v l2 )
.

Definition reverse_alter_style3_entail_wit_4 := 
forall (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (w: Z) (v: Z) (v_next: Z) (v_data: Z) (l2_new: (@list Z)) ,
  [| (l2_2 = (cons (v_data) (l2_new))) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1_2))) (l2_2))) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll v_next l2_new )
  **  (sll w l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v l1 )
  **  (sll v_next l2 )
.

Definition reverse_alter_style3_return_wit_1 := 
forall (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (w: Z) (v: Z) ,
  [| (v = 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w l1 )
  **  (sll v l2 )
|--
  (sll w (rev (l)) )
.

Definition reverse_alter_style3_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (w: Z) (v: Z) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  (sll w l1 )
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  (sll v l2 )
|--
  [| (v <> 0) |]
.

Definition reverse_alter_style3_partial_solve_wit_1_aux := 
forall (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (w: Z) (v: Z) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll w l1 )
  **  (sll v l2 )
|--
  [| (v <> 0) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll v l2 )
  **  (sll w l1 )
.

Definition reverse_alter_style3_partial_solve_wit_1 := reverse_alter_style3_partial_solve_wit_1_pure -> reverse_alter_style3_partial_solve_wit_1_aux.

Definition reverse_alter_style3_which_implies_wit_1 := 
forall (l2: (@list Z)) (v: Z) ,
  [| (v <> 0) |]
  &&  (sll v l2 )
|--
  EX (v_next: Z)  (v_data: Z)  (l2_new: (@list Z)) ,
  [| (l2 = (cons (v_data) (l2_new))) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Int  |-> v_data)
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> v_next)
  **  (sll v_next l2_new )
.

(*----- Function append -----*)

Definition append_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition append_safety_wit_2 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) ,
  [| ((app (l1a) ((cons (t_data) (l1b)))) = l1) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = u) |] 
  &&  [| (l1 = (cons (x_data) (l1n))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition append_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_next: Z) (x_data: Z) (l1n: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1n))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1n )
  **  (sll y_pre l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (t_data: Z)  (l1b: (@list Z)) ,
  [| ((app (l1a) ((cons (t_data) (l1b)))) = l1) |] 
  &&  [| (x_pre <> 0) |] 
  &&  [| (t_next = x_next) |] 
  &&  [| (l1 = (cons (x_data) (l1n))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x_pre x_pre l1a )
  **  (sll x_next l1b )
  **  (sll y_pre l2 )
.

Definition append_entail_wit_2 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next_2: Z) (l1a_2: (@list Z)) (t_data_2: Z) (t: Z) (l1b_2: (@list Z)) (u_next: Z) (u_data: Z) (l1b_new: (@list Z)) ,
  [| (l1b_2 = (cons (u_data) (l1b_new))) |] 
  &&  [| (u <> 0) |] 
  &&  [| ((app (l1a_2) ((cons (t_data_2) (l1b_2)))) = l1) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next_2 = u) |] 
  &&  [| (l1 = (cons (x_data) (l1n))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> u_data)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> u_next)
  **  (sll u_next l1b_new )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x t l1a_2 )
  **  (sll y l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (t_data: Z)  (l1b: (@list Z)) ,
  [| ((app (l1a) ((cons (t_data) (l1b)))) = l1) |] 
  &&  [| (u <> 0) |] 
  &&  [| (t_next = u_next) |] 
  &&  [| (l1 = (cons (x_data) (l1n))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x u l1a )
  **  (sll u_next l1b )
  **  (sll y l2 )
.

Definition append_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (x_pre = 0) |]
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  (sll y_pre (app (l1) (l2)) )
.

Definition append_return_wit_2 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) ,
  [| (u = 0) |] 
  &&  [| ((app (l1a) ((cons (t_data) (l1b)))) = l1) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = u) |] 
  &&  [| (l1 = (cons (x_data) (l1n))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  (sll y l2 )
|--
  (sll x (app (l1) (l2)) )
.

Definition append_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (x_pre <> 0) |]
  &&  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  [| (x_pre <> 0) |]
.

Definition append_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (x_pre <> 0) |]
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  [| (x_pre <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
.

Definition append_partial_solve_wit_1 := append_partial_solve_wit_1_pure -> append_partial_solve_wit_1_aux.

Definition append_partial_solve_wit_2_pure := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) ,
  [| (u <> 0) |] 
  &&  [| ((app (l1a) ((cons (t_data) (l1b)))) = l1) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = u) |] 
  &&  [| (l1 = (cons (x_data) (l1n))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  [| (u <> 0) |]
.

Definition append_partial_solve_wit_2_aux := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (x_data: Z) (l1n: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (l1a: (@list Z)) (t_data: Z) (t: Z) (l1b: (@list Z)) ,
  [| (u <> 0) |] 
  &&  [| ((app (l1a) ((cons (t_data) (l1b)))) = l1) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = u) |] 
  &&  [| (l1 = (cons (x_data) (l1n))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x t l1a )
  **  (sll u l1b )
  **  (sll y l2 )
|--
  [| (u <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| ((app (l1a) ((cons (t_data) (l1b)))) = l1) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = u) |] 
  &&  [| (l1 = (cons (x_data) (l1n))) |] 
  &&  [| (x_pre <> 0) |]
  &&  (sll u l1b )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x t l1a )
  **  (sll y l2 )
.

Definition append_partial_solve_wit_2 := append_partial_solve_wit_2_pure -> append_partial_solve_wit_2_aux.

Definition append_which_implies_wit_1 := 
forall (l1: (@list Z)) (x: Z) ,
  [| (x <> 0) |]
  &&  (sll x l1 )
|--
  EX (x_next: Z)  (x_data: Z)  (l1n: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1n))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1n )
.

Definition append_which_implies_wit_2 := 
forall (l1b: (@list Z)) (u: Z) ,
  [| (u <> 0) |]
  &&  (sll u l1b )
|--
  EX (u_next: Z)  (u_data: Z)  (l1b_new: (@list Z)) ,
  [| (l1b = (cons (u_data) (l1b_new))) |]
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> u_data)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> u_next)
  **  (sll u_next l1b_new )
.

(*----- Function append_long -----*)

Definition append_long_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition append_long_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) ,
  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1b )
  **  ((( &( "u" ) )) # Ptr  |-> xn)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sll y_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition append_long_safety_wit_3 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) ,
  [| ((app (l1a) ((cons (b) (l1c)))) = l1) |] 
  &&  [| (t_next = u) |] 
  &&  [| (t <> 0) |] 
  &&  [| (xn <> 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition append_long_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) ,
  [| (xn <> 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1b )
  **  (sll y_pre l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (b: Z)  (l1c: (@list Z)) ,
  [| ((app (l1a) ((cons (b) (l1c)))) = l1) |] 
  &&  [| (t_next = xn) |] 
  &&  [| (x_pre <> 0) |] 
  &&  [| (xn <> 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x_pre x_pre l1a )
  **  (sll xn l1c )
  **  (sll y_pre l2 )
.

Definition append_long_entail_wit_2 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next_2: Z) (t: Z) (l1a_2: (@list Z)) (b_2: Z) (l1c_2: (@list Z)) (un: Z) (c: Z) (l1d: (@list Z)) ,
  [| (l1c_2 = (cons (c) (l1d))) |] 
  &&  [| (u <> 0) |] 
  &&  [| ((app (l1a_2) ((cons (b_2) (l1c_2)))) = l1) |] 
  &&  [| (t_next_2 = u) |] 
  &&  [| (t <> 0) |] 
  &&  [| (xn <> 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> c)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> un)
  **  (sll un l1d )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  (sllseg x t l1a_2 )
  **  (sll y l2 )
|--
  EX (t_next: Z)  (l1a: (@list Z))  (b: Z)  (l1c: (@list Z)) ,
  [| ((app (l1a) ((cons (b) (l1c)))) = l1) |] 
  &&  [| (t_next = un) |] 
  &&  [| (u <> 0) |] 
  &&  [| (xn <> 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x u l1a )
  **  (sll un l1c )
  **  (sll y l2 )
.

Definition append_long_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (x_pre = 0) |]
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  (sll y_pre (app (l1) (l2)) )
.

Definition append_long_return_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) ,
  [| (xn = 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (sll xn l1b )
  **  (sll y_pre l2 )
|--
  (sll x_pre (app (l1) (l2)) )
.

Definition append_long_return_wit_3 := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) ,
  [| (u = 0) |] 
  &&  [| ((app (l1a) ((cons (b) (l1c)))) = l1) |] 
  &&  [| (t_next = u) |] 
  &&  [| (t <> 0) |] 
  &&  [| (xn <> 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  (sll y l2 )
|--
  (sll x (app (l1) (l2)) )
.

Definition append_long_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (x_pre <> 0) |]
  &&  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  [| (x_pre <> 0) |]
.

Definition append_long_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (x_pre <> 0) |]
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  [| (x_pre <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
.

Definition append_long_partial_solve_wit_1 := append_long_partial_solve_wit_1_pure -> append_long_partial_solve_wit_1_aux.

Definition append_long_partial_solve_wit_2_pure := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) ,
  [| (u <> 0) |] 
  &&  [| ((app (l1a) ((cons (b) (l1c)))) = l1) |] 
  &&  [| (t_next = u) |] 
  &&  [| (t <> 0) |] 
  &&  [| (xn <> 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  [| (u <> 0) |]
.

Definition append_long_partial_solve_wit_2_aux := 
forall (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (xn: Z) (a: Z) (l1b: (@list Z)) (y: Z) (x: Z) (u: Z) (t_next: Z) (t: Z) (l1a: (@list Z)) (b: Z) (l1c: (@list Z)) ,
  [| (u <> 0) |] 
  &&  [| ((app (l1a) ((cons (b) (l1c)))) = l1) |] 
  &&  [| (t_next = u) |] 
  &&  [| (t <> 0) |] 
  &&  [| (xn <> 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x t l1a )
  **  (sll u l1c )
  **  (sll y l2 )
|--
  [| (u <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| ((app (l1a) ((cons (b) (l1c)))) = l1) |] 
  &&  [| (t_next = u) |] 
  &&  [| (t <> 0) |] 
  &&  [| (xn <> 0) |] 
  &&  [| (l1 = (cons (a) (l1b))) |] 
  &&  [| (x_pre <> 0) |]
  &&  (sll u l1c )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> b)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (sllseg x t l1a )
  **  (sll y l2 )
.

Definition append_long_partial_solve_wit_2 := append_long_partial_solve_wit_2_pure -> append_long_partial_solve_wit_2_aux.

Definition append_long_which_implies_wit_1 := 
forall (l1: (@list Z)) (x: Z) ,
  [| (x <> 0) |]
  &&  (sll x l1 )
|--
  EX (xn: Z)  (a: Z)  (l1b: (@list Z)) ,
  [| (l1 = (cons (a) (l1b))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> xn)
  **  (sll xn l1b )
.

Definition append_long_which_implies_wit_2 := 
forall (l1cd: (@list Z)) (u: Z) ,
  [| (u <> 0) |]
  &&  (sll u l1cd )
|--
  EX (un: Z)  (c: Z)  (l1d: (@list Z)) ,
  [| (l1cd = (cons (c) (l1d))) |]
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> c)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> un)
  **  (sll un l1d )
.

(*----- Function append_2p -----*)

Definition append_2p_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  (sll x_pre l1 )
  **  (sll y_pre l2 )
|--
  EX (l1a: (@list Z))  (l1b: (@list Z)) ,
  [| ((app (l1a) (l1b)) = l1) |]
  &&  (sllbseg ( &( "x" ) ) ( &( "x" ) ) l1a )
  **  (sll x_pre l1b )
  **  (sll y_pre l2 )
.

Definition append_2p_entail_wit_2 := 
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v_2: Z) (pt: Z) (l1a_2: (@list Z)) (l1b_2: (@list Z)) ,
  [| (pt_v_2 <> 0) |] 
  &&  [| ((app (l1a_2) (l1b_2)) = l1) |]
  &&  (sllbseg ( &( "x" ) ) pt l1a_2 )
  **  ((pt) # Ptr  |-> pt_v_2)
  **  (sll pt_v_2 l1b_2 )
  **  (sll y l2 )
|--
  EX (pt_v: Z)  (l1a: (@list Z))  (l1b: (@list Z)) ,
  [| ((app (l1a) (l1b)) = l1) |]
  &&  (sllbseg ( &( "x" ) ) &((pt_v_2)  # "list" ->ₛ "next") l1a )
  **  ((&((pt_v_2)  # "list" ->ₛ "next")) # Ptr  |-> pt_v)
  **  (sll pt_v l1b )
  **  (sll y l2 )
.

Definition append_2p_return_wit_1 := 
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v: Z) (l1a: (@list Z)) (l1b: (@list Z)) (pres_v: Z) ,
  [| (pt_v = 0) |] 
  &&  [| ((app (l1a) (l1b)) = l1) |]
  &&  (sllseg pres_v y l1a )
  **  (sll pt_v l1b )
  **  (sll y l2 )
|--
  (sll pres_v (app (l1) (l2)) )
.

Definition append_2p_partial_solve_wit_1_pure := 
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v: Z) (pt: Z) (l1a: (@list Z)) (l1b: (@list Z)) ,
  [| (pt_v = 0) |] 
  &&  [| ((app (l1a) (l1b)) = l1) |]
  &&  ((( &( "pres" ) )) # Ptr  |-> ( &( "x" ) ))
  **  ((( &( "pt" ) )) # Ptr  |-> pt)
  **  (sllbseg ( &( "x" ) ) pt l1a )
  **  ((pt) # Ptr  |-> y)
  **  (sll pt_v l1b )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  [| (y = y) |]
.

Definition append_2p_partial_solve_wit_1_aux := 
forall (l2: (@list Z)) (l1: (@list Z)) (y: Z) (pt_v: Z) (pt: Z) (l1a: (@list Z)) (l1b: (@list Z)) ,
  [| (pt_v = 0) |] 
  &&  [| ((app (l1a) (l1b)) = l1) |]
  &&  (sllbseg ( &( "x" ) ) pt l1a )
  **  ((pt) # Ptr  |-> y)
  **  (sll pt_v l1b )
  **  (sll y l2 )
|--
  [| (y = y) |] 
  &&  [| (pt_v = 0) |] 
  &&  [| ((app (l1a) (l1b)) = l1) |]
  &&  ((pt) # Ptr  |-> y)
  **  (sllbseg ( &( "x" ) ) pt l1a )
  **  (sll pt_v l1b )
  **  (sll y l2 )
.

Definition append_2p_partial_solve_wit_1 := append_2p_partial_solve_wit_1_pure -> append_2p_partial_solve_wit_1_aux.

Definition append_2p_which_implies_wit_1 := 
forall (l1a: (@list Z)) (pt: Z) (pt_v: Z) (y: Z) (pres: Z) ,
  [| (pt_v = y) |]
  &&  ((pt) # Ptr  |-> pt_v)
  **  (sllbseg pres pt l1a )
|--
  EX (pres_v: Z) ,
  ((pres) # Ptr  |-> pres_v)
  **  (sllseg pres_v y l1a )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_length_safety_wit_1 : length_safety_wit_1.
Axiom proof_of_length_safety_wit_2 : length_safety_wit_2.
Axiom proof_of_length_entail_wit_1 : length_entail_wit_1.
Axiom proof_of_length_entail_wit_2 : length_entail_wit_2.
Axiom proof_of_length_return_wit_1 : length_return_wit_1.
Axiom proof_of_length_partial_solve_wit_1_pure : length_partial_solve_wit_1_pure.
Axiom proof_of_length_partial_solve_wit_1 : length_partial_solve_wit_1.
Axiom proof_of_length_which_implies_wit_1 : length_which_implies_wit_1.
Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Axiom proof_of_reverse_partial_solve_wit_1_pure : reverse_partial_solve_wit_1_pure.
Axiom proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1.
Axiom proof_of_reverse_which_implies_wit_1 : reverse_which_implies_wit_1.
Axiom proof_of_reverse_alter_style1_safety_wit_1 : reverse_alter_style1_safety_wit_1.
Axiom proof_of_reverse_alter_style1_entail_wit_1 : reverse_alter_style1_entail_wit_1.
Axiom proof_of_reverse_alter_style1_entail_wit_2 : reverse_alter_style1_entail_wit_2.
Axiom proof_of_reverse_alter_style1_return_wit_1 : reverse_alter_style1_return_wit_1.
Axiom proof_of_reverse_alter_style1_partial_solve_wit_1_pure : reverse_alter_style1_partial_solve_wit_1_pure.
Axiom proof_of_reverse_alter_style1_partial_solve_wit_1 : reverse_alter_style1_partial_solve_wit_1.
Axiom proof_of_reverse_alter_style1_which_implies_wit_1 : reverse_alter_style1_which_implies_wit_1.
Axiom proof_of_reverse_alter_style2_safety_wit_1 : reverse_alter_style2_safety_wit_1.
Axiom proof_of_reverse_alter_style2_entail_wit_1 : reverse_alter_style2_entail_wit_1.
Axiom proof_of_reverse_alter_style2_entail_wit_2 : reverse_alter_style2_entail_wit_2.
Axiom proof_of_reverse_alter_style2_return_wit_1 : reverse_alter_style2_return_wit_1.
Axiom proof_of_reverse_alter_style2_partial_solve_wit_1_pure : reverse_alter_style2_partial_solve_wit_1_pure.
Axiom proof_of_reverse_alter_style2_partial_solve_wit_1 : reverse_alter_style2_partial_solve_wit_1.
Axiom proof_of_reverse_alter_style2_which_implies_wit_1 : reverse_alter_style2_which_implies_wit_1.
Axiom proof_of_reverse_alter_style3_safety_wit_1 : reverse_alter_style3_safety_wit_1.
Axiom proof_of_reverse_alter_style3_entail_wit_1 : reverse_alter_style3_entail_wit_1.
Axiom proof_of_reverse_alter_style3_entail_wit_2 : reverse_alter_style3_entail_wit_2.
Axiom proof_of_reverse_alter_style3_entail_wit_3 : reverse_alter_style3_entail_wit_3.
Axiom proof_of_reverse_alter_style3_entail_wit_4 : reverse_alter_style3_entail_wit_4.
Axiom proof_of_reverse_alter_style3_return_wit_1 : reverse_alter_style3_return_wit_1.
Axiom proof_of_reverse_alter_style3_partial_solve_wit_1_pure : reverse_alter_style3_partial_solve_wit_1_pure.
Axiom proof_of_reverse_alter_style3_partial_solve_wit_1 : reverse_alter_style3_partial_solve_wit_1.
Axiom proof_of_reverse_alter_style3_which_implies_wit_1 : reverse_alter_style3_which_implies_wit_1.
Axiom proof_of_append_safety_wit_1 : append_safety_wit_1.
Axiom proof_of_append_safety_wit_2 : append_safety_wit_2.
Axiom proof_of_append_entail_wit_1 : append_entail_wit_1.
Axiom proof_of_append_entail_wit_2 : append_entail_wit_2.
Axiom proof_of_append_return_wit_1 : append_return_wit_1.
Axiom proof_of_append_return_wit_2 : append_return_wit_2.
Axiom proof_of_append_partial_solve_wit_1_pure : append_partial_solve_wit_1_pure.
Axiom proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1.
Axiom proof_of_append_partial_solve_wit_2_pure : append_partial_solve_wit_2_pure.
Axiom proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2.
Axiom proof_of_append_which_implies_wit_1 : append_which_implies_wit_1.
Axiom proof_of_append_which_implies_wit_2 : append_which_implies_wit_2.
Axiom proof_of_append_long_safety_wit_1 : append_long_safety_wit_1.
Axiom proof_of_append_long_safety_wit_2 : append_long_safety_wit_2.
Axiom proof_of_append_long_safety_wit_3 : append_long_safety_wit_3.
Axiom proof_of_append_long_entail_wit_1 : append_long_entail_wit_1.
Axiom proof_of_append_long_entail_wit_2 : append_long_entail_wit_2.
Axiom proof_of_append_long_return_wit_1 : append_long_return_wit_1.
Axiom proof_of_append_long_return_wit_2 : append_long_return_wit_2.
Axiom proof_of_append_long_return_wit_3 : append_long_return_wit_3.
Axiom proof_of_append_long_partial_solve_wit_1_pure : append_long_partial_solve_wit_1_pure.
Axiom proof_of_append_long_partial_solve_wit_1 : append_long_partial_solve_wit_1.
Axiom proof_of_append_long_partial_solve_wit_2_pure : append_long_partial_solve_wit_2_pure.
Axiom proof_of_append_long_partial_solve_wit_2 : append_long_partial_solve_wit_2.
Axiom proof_of_append_long_which_implies_wit_1 : append_long_which_implies_wit_1.
Axiom proof_of_append_long_which_implies_wit_2 : append_long_which_implies_wit_2.
Axiom proof_of_append_2p_entail_wit_1 : append_2p_entail_wit_1.
Axiom proof_of_append_2p_entail_wit_2 : append_2p_entail_wit_2.
Axiom proof_of_append_2p_return_wit_1 : append_2p_return_wit_1.
Axiom proof_of_append_2p_partial_solve_wit_1_pure : append_2p_partial_solve_wit_1_pure.
Axiom proof_of_append_2p_partial_solve_wit_1 : append_2p_partial_solve_wit_1.
Axiom proof_of_append_2p_which_implies_wit_1 : append_2p_which_implies_wit_1.

End VC_Correct.
