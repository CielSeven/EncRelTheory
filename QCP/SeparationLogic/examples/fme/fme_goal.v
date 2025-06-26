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
Require Import fme_lib.
Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
Require Import fme_strategy_goal.
Require Import fme_strategy_proof.

(*----- Function gcd -----*)

Definition gcd_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (0 < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition gcd_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (b_pre <> 0) |] 
  &&  [| (0 < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((a_pre <> (INT_MIN)) \/ (b_pre <> (-1))) |] 
  &&  [| (b_pre <> 0) |]
.

Definition gcd_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) ,
  [| (retval = (Zgcd (b_pre) ((a_pre % ( b_pre ) )))) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (0 < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
|--
  [| (retval = (Zgcd (a_pre) (b_pre))) |]
  &&  emp
.

Definition gcd_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (b_pre = 0) |] 
  &&  [| (0 < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
|--
  [| (a_pre = (Zgcd (a_pre) (b_pre))) |]
  &&  emp
.

Definition gcd_partial_solve_wit_1_pure := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (b_pre <> 0) |] 
  &&  [| (0 < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| ((a_pre % ( b_pre ) ) <= INT_MAX) |] 
  &&  [| (0 <= (a_pre % ( b_pre ) )) |]
.

Definition gcd_partial_solve_wit_1_aux := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (b_pre <> 0) |] 
  &&  [| (0 < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |] 
  &&  [| ((a_pre % ( b_pre ) ) <= INT_MAX) |] 
  &&  [| (0 <= (a_pre % ( b_pre ) )) |] 
  &&  [| (b_pre <> 0) |] 
  &&  [| (0 < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
.

Definition gcd_partial_solve_wit_1 := gcd_partial_solve_wit_1_pure -> gcd_partial_solve_wit_1_aux.

(*----- Function check_add_safe -----*)

Definition check_add_safe_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_add_safe_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre > 0) |] 
  &&  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((INT_MAX - x_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (INT_MAX - x_pre )) |]
.

Definition check_add_safe_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre > 0) |] 
  &&  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (INT_MAX <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= INT_MAX) |]
.

Definition check_add_safe_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <= 0) |] 
  &&  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (((-INT_MAX) - x_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((-INT_MAX) - x_pre )) |]
.

Definition check_add_safe_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <= 0) |] 
  &&  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (INT_MAX <> (INT_MIN)) |]
.

Definition check_add_safe_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <= 0) |] 
  &&  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (INT_MAX <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= INT_MAX) |]
.

Definition check_add_safe_return_wit_1_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre > (INT_MAX - x_pre )) |] 
  &&  [| (x_pre > 0) |] 
  &&  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  ([| (0 = 0) |]
  &&  emp)
  ||
  ([| (0 = 1) |] 
  &&  [| ((-INT_MAX) <= (x_pre + y_pre )) |] 
  &&  [| ((x_pre + y_pre ) <= INT_MAX) |]
  &&  emp)
.

Definition check_add_safe_return_wit_1_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre <= (INT_MAX - x_pre )) |] 
  &&  [| (x_pre > 0) |] 
  &&  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  ([| (1 = 0) |]
  &&  emp)
  ||
  ([| (1 = 1) |] 
  &&  [| ((-INT_MAX) <= (x_pre + y_pre )) |] 
  &&  [| ((x_pre + y_pre ) <= INT_MAX) |]
  &&  emp)
.

Definition check_add_safe_return_wit_2_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre < ((-INT_MAX) - x_pre )) |] 
  &&  [| (x_pre <= 0) |] 
  &&  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  ([| (0 = 0) |]
  &&  emp)
  ||
  ([| (0 = 1) |] 
  &&  [| ((-INT_MAX) <= (x_pre + y_pre )) |] 
  &&  [| ((x_pre + y_pre ) <= INT_MAX) |]
  &&  emp)
.

Definition check_add_safe_return_wit_2_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre >= ((-INT_MAX) - x_pre )) |] 
  &&  [| (x_pre <= 0) |] 
  &&  [| ((-INT_MAX) <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  ([| (1 = 0) |]
  &&  emp)
  ||
  ([| (1 = 1) |] 
  &&  [| ((-INT_MAX) <= (x_pre + y_pre )) |] 
  &&  [| ((x_pre + y_pre ) <= INT_MAX) |]
  &&  emp)
.

(*----- Function NilInequList -----*)

Definition NilInequList_safety_wit_1 := 
  TT && emp 
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition NilInequList_return_wit_1 := 
  TT && emp 
|--
  [| (0 = 0) |]
  &&  emp
.

(*----- Function ConsInequList -----*)

Definition ConsInequList_return_wit_1 := 
forall (l_pre: Z) (c_pre: Z) (l0: (@list Constraint)) (c0: Constraint) (n: Z) (retval: Z) ,
  [| (retval <> 0) |]
  &&  ((&((retval)  # "InequList" ->ₛ "coef")) # Ptr  |-> c_pre)
  **  ((&((retval)  # "InequList" ->ₛ "next")) # Ptr  |-> l_pre)
  **  (coef_array c_pre n c0 )
  **  (InequList l_pre n l0 )
|--
  (InequList retval n (cons (c0) (l0)) )
.

Definition ConsInequList_partial_solve_wit_1 := 
forall (l_pre: Z) (c_pre: Z) (l0: (@list Constraint)) (c0: Constraint) (n: Z) ,
  (coef_array c_pre n c0 )
  **  (InequList l_pre n l0 )
|--
  (coef_array c_pre n c0 )
  **  (InequList l_pre n l0 )
.

(*----- Function free_InequList -----*)

Definition free_InequList_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (InequList p_pre n l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition free_InequList_safety_wit_2 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition free_InequList_safety_wit_3 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition free_InequList_safety_wit_4 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (h = 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition free_InequList_return_wit_1 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) ,
  [| (p_pre = 0) |]
  &&  (InequList p_pre n l )
|--
  TT && emp 
.

Definition free_InequList_return_wit_2_1 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y <> 0) |] 
  &&  [| (h = 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  (coef_array h n x )
|--
  TT && emp 
.

Definition free_InequList_return_wit_2_2 := 
forall (p_pre: Z) (l: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y <> 0) |] 
  &&  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  emp
|--
  TT && emp 
.

Definition free_InequList_return_wit_2_3 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y = 0) |] 
  &&  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  (InequList y n l0 )
|--
  TT && emp 
.

Definition free_InequList_return_wit_2_4 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y = 0) |] 
  &&  [| (h = 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  (InequList y n l0 )
  **  (coef_array h n x )
|--
  TT && emp 
.

Definition free_InequList_partial_solve_wit_1 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) ,
  [| (p_pre <> 0) |]
  &&  (InequList p_pre n l )
|--
  EX (h: Z)  (y: Z)  (l0: (@list Constraint))  (x: Constraint) ,
  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
.

Definition free_InequList_partial_solve_wit_2 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
|--
  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  (coef_array h n x )
  **  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
.

Definition free_InequList_partial_solve_wit_3 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y <> 0) |] 
  &&  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
|--
  [| (y <> 0) |] 
  &&  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
.

Definition free_InequList_partial_solve_wit_4 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y <> 0) |] 
  &&  [| (h = 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
|--
  [| (y <> 0) |] 
  &&  [| (h = 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
.

Definition free_InequList_partial_solve_wit_5 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y <> 0) |] 
  &&  [| (h = 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
|--
  [| (y <> 0) |] 
  &&  [| (h = 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
.

Definition free_InequList_partial_solve_wit_6 := 
forall (p_pre: Z) (l: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y <> 0) |] 
  &&  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
|--
  [| (y <> 0) |] 
  &&  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
.

Definition free_InequList_partial_solve_wit_7 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y = 0) |] 
  &&  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
|--
  [| (y = 0) |] 
  &&  [| (h <> 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n l0 )
.

Definition free_InequList_partial_solve_wit_8 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) ,
  [| (y = 0) |] 
  &&  [| (h = 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (coef_array h n x )
|--
  [| (y = 0) |] 
  &&  [| (h = 0) |] 
  &&  [| (l = (cons (x) (l0))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n l0 )
  **  (coef_array h n x )
.

(*----- Function eliminate -----*)

Definition eliminate_safety_wit_1 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (InequList cur n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eliminate_safety_wit_2 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) ,
  [| (l2 = (cons (x) (l3))) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  (coef_array cur_coef n x )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n re )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eliminate_safety_wit_3 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) ,
  [| ((coef_Znth (num_pre) (x) (0)) <> 0) |] 
  &&  [| (l2 = (cons (x) (l3))) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  (coef_array cur_coef n x )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n re )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eliminate_entail_wit_1 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "remain" ) )) # Ptr  |-> retval_3)
  **  ((( &( "lower" ) )) # Ptr  |-> retval_2)
  **  ((( &( "upper" ) )) # Ptr  |-> retval)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "upper" ) )) # Ptr  |-> 0)
  **  ((( &( "lower" ) )) # Ptr  |-> 0)
  **  ((( &( "remain" ) )) # Ptr  |-> 0)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
.

Definition eliminate_entail_wit_2 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (bp: BP)  (l1: (@list Constraint))  (l2: (@list Constraint)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList 0 n up )
  **  (InequList 0 n lo )
  **  (InequList 0 n re )
  **  (InequList r_pre n l2 )
.

Definition eliminate_entail_wit_3_1 := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp_2: BP) (l1_2: (@list Constraint)) (l2_2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) ,
  [| ((coef_Znth (num_pre) (x) (0)) = 0) |] 
  &&  [| (l2_2 = (cons (x) (l3))) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1_2 bp_2 ) |] 
  &&  [| (form_BP up_2 lo_2 re_2 bp_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> remain)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up_2 )
  **  (InequList lower n lo_2 )
  **  (InequList remain n re_2 )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (bp: BP)  (l1: (@list Constraint))  (l2: (@list Constraint)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList cur n re )
  **  (InequList cur_next n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
.

Definition eliminate_entail_wit_3_2 := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp_2: BP) (l1_2: (@list Constraint)) (l2_2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) ,
  [| ((coef_Znth (num_pre) (x) (0)) <= 0) |] 
  &&  [| ((coef_Znth (num_pre) (x) (0)) <> 0) |] 
  &&  [| (l2_2 = (cons (x) (l3))) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1_2 bp_2 ) |] 
  &&  [| (form_BP up_2 lo_2 re_2 bp_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> lower)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up_2 )
  **  (InequList lower n lo_2 )
  **  (InequList remain n re_2 )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (bp: BP)  (l1: (@list Constraint))  (l2: (@list Constraint)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList cur n lo )
  **  (InequList remain n re )
  **  (InequList cur_next n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
.

Definition eliminate_entail_wit_3_3 := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp_2: BP) (l1_2: (@list Constraint)) (l2_2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) ,
  [| ((coef_Znth (num_pre) (x) (0)) > 0) |] 
  &&  [| ((coef_Znth (num_pre) (x) (0)) <> 0) |] 
  &&  [| (l2_2 = (cons (x) (l3))) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1_2 bp_2 ) |] 
  &&  [| (form_BP up_2 lo_2 re_2 bp_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> upper)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up_2 )
  **  (InequList lower n lo_2 )
  **  (InequList remain n re_2 )
  **  ((( &( "cur_next" ) )) # Ptr  |-> cur_next)
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (bp: BP)  (l1: (@list Constraint))  (l2: (@list Constraint)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList cur n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
  **  (InequList cur_next n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
.

Definition eliminate_return_wit_1 := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) ,
  [| (cur = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up_2 lo_2 re_2 bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> remain)
  **  (InequList upper n up_2 )
  **  (InequList lower n lo_2 )
  **  (InequList remain n re_2 )
  **  (InequList cur n l2 )
|--
  EX (BP0_remain: Z)  (BP0_lower: Z)  (BP0_upper: Z)  (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (b: BP) ,
  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos num_pre up ) |] 
  &&  [| (InequList_nth_neg num_pre lo ) |] 
  &&  [| (LP_abs_in_int_range n up ) |] 
  &&  [| (LP_abs_in_int_range n lo ) |] 
  &&  [| (LP_abs_in_int_range n re ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper n up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower n lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain n re )
.

Definition eliminate_partial_solve_wit_1 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) ,
  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
.

Definition eliminate_partial_solve_wit_2 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
.

Definition eliminate_partial_solve_wit_3 := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
|--
  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n l )
.

Definition eliminate_partial_solve_wit_4_pure := 
forall (num_pre: Z) (r_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) ,
  [| (cur <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (InequList cur n l2 )
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  [| (cur <> 0) |]
.

Definition eliminate_partial_solve_wit_4_aux := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) ,
  [| (cur <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
  **  (InequList cur n l2 )
|--
  [| (cur <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  (InequList cur n l2 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
.

Definition eliminate_partial_solve_wit_4 := eliminate_partial_solve_wit_4_pure -> eliminate_partial_solve_wit_4_aux.

Definition eliminate_partial_solve_wit_5 := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) ,
  [| (l2 = (cons (x) (l3))) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
|--
  [| (l2 = (cons (x) (l3))) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  (((cur_coef + (num_pre * sizeof(INT) ) )) # Int  |-> (coef_Znth (num_pre) (x) (0)))
  **  (coef_array_missing_i_rec cur_coef num_pre 0 n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
.

Definition eliminate_partial_solve_wit_6 := 
forall (num_pre: Z) (l: (@list Constraint)) (n: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (bp: BP) (l1: (@list Constraint)) (l2: (@list Constraint)) (cur_next: Z) (cur_coef: Z) (x: Constraint) (l3: (@list Constraint)) ,
  [| ((coef_Znth (num_pre) (x) (0)) <> 0) |] 
  &&  [| (l2 = (cons (x) (l3))) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
|--
  [| ((coef_Znth (num_pre) (x) (0)) <> 0) |] 
  &&  [| (l2 = (cons (x) (l3))) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (eliminate_xn (Zto_nat ((num_pre - 1 ))) l1 bp ) |] 
  &&  [| (form_BP up lo re bp ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (1 <= num_pre) |] 
  &&  [| (num_pre < n) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range n l ) |]
  &&  (((cur_coef + (num_pre * sizeof(INT) ) )) # Int  |-> (coef_Znth (num_pre) (x) (0)))
  **  (coef_array_missing_i_rec cur_coef num_pre 0 n x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n up )
  **  (InequList lower n lo )
  **  (InequList remain n re )
.

Definition eliminate_which_implies_wit_1 := 
forall (n: Z) (l2: (@list Constraint)) (cur: Z) ,
  [| (cur <> 0) |]
  &&  (InequList cur n l2 )
|--
  EX (cur_next: Z)  (cur_coef: Z)  (x: Constraint)  (l3: (@list Constraint)) ,
  [| (l2 = (cons (x) (l3))) |]
  &&  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> cur_coef)
  **  (coef_array cur_coef n x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> cur_next)
  **  (InequList cur_next n l3 )
.

(*----- Function generate_new_constr -----*)

Definition generate_new_constr_safety_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) ,
  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |->_)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| ((coef_Znth (cur_num_pre) (c2) (0)) <> (INT_MIN)) |]
.

Definition generate_new_constr_safety_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "m1" ) )) # Int  |->_)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (((-(coef_Znth (cur_num_pre) (c2) (0))) <> (INT_MIN)) \/ (retval <> (-1))) |] 
  &&  [| (retval <> 0) |]
.

Definition generate_new_constr_safety_wit_3 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "m2" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (((coef_Znth (cur_num_pre) (c1) (0)) <> (INT_MIN)) \/ (retval <> (-1))) |] 
  &&  [| (retval <> 0) |]
.

Definition generate_new_constr_safety_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |->_)
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| ((INT_MAX <> (INT_MIN)) \/ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> (-1))) |] 
  &&  [| (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> 0) |]
.

Definition generate_new_constr_safety_wit_5 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |->_)
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (INT_MAX <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= INT_MAX) |]
.

Definition generate_new_constr_safety_wit_6 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (((-INT_MAX) <> (INT_MIN)) \/ (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> (-1))) |] 
  &&  [| (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) <> 0) |]
.

Definition generate_new_constr_safety_wit_7 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (INT_MAX <> (INT_MIN)) |]
.

Definition generate_new_constr_safety_wit_8 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |->_)
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (INT_MAX <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= INT_MAX) |]
.

Definition generate_new_constr_safety_wit_9 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| ((INT_MAX <> (INT_MIN)) \/ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> (-1))) |] 
  &&  [| (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> 0) |]
.

Definition generate_new_constr_safety_wit_10 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |->_)
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (INT_MAX <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= INT_MAX) |]
.

Definition generate_new_constr_safety_wit_11 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (((-INT_MAX) <> (INT_MIN)) \/ (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> (-1))) |] 
  &&  [| (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) <> 0) |]
.

Definition generate_new_constr_safety_wit_12 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (INT_MAX <> (INT_MIN)) |]
.

Definition generate_new_constr_safety_wit_13 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "lb2" ) )) # Int  |->_)
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (INT_MAX <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= INT_MAX) |]
.

Definition generate_new_constr_safety_wit_14 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lb2" ) )) # Int  |-> ((-INT_MAX) ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constr_safety_wit_15 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "lb2" ) )) # Int  |-> ((-INT_MAX) ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "lb1" ) )) # Int  |-> ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "ub2" ) )) # Int  |-> (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ))
  **  ((( &( "ub1" ) )) # Int  |-> (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ))
  **  ((( &( "m2" ) )) # Int  |-> ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ))
  **  ((( &( "m1" ) )) # Int  |-> ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ))
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constr_safety_wit_16 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c1) (0)) < lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constr_safety_wit_17 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c1) (0)) > ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constr_safety_wit_18 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c2) (0)) < lb2) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constr_safety_wit_19 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c2) (0)) > ub2) |] 
  &&  [| ((coef_Znth (i) (c2) (0)) >= lb2) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constr_safety_wit_20 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c2) (0)) <= ub2) |] 
  &&  [| ((coef_Znth (i) (c2) (0)) >= lb2) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition generate_new_constr_safety_wit_21 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (num_pre + 1 )) |]
.

Definition generate_new_constr_safety_wit_22 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition generate_new_constr_safety_wit_23 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval_2: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval_2 = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array retval (num_pre + 1 ) l )
  **  ((( &( "res" ) )) # Ptr  |-> retval)
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "g" ) )) # Int  |-> retval_2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constr_safety_wit_24 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (m2_2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (m2: Z) (m1_2: Z) ,
  [| (i <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i m1_2 m2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i_2 > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2_2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2_2 )) |] 
  &&  [| (in_int_range i_2 m1 c1 ) |] 
  &&  [| (in_int_range i_2 m2_2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "m1" ) )) # Int  |-> m1_2)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| ((m2 * (coef_Znth (i) (c2) (0)) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (m2 * (coef_Znth (i) (c2) (0)) )) |]
.

Definition generate_new_constr_safety_wit_25 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (m2: Z) (m1_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (m2_2: Z) (m1: Z) ,
  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i m1 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i_2 > num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1_2 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1_2 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i_2 m1_2 c1 ) |] 
  &&  [| (in_int_range i_2 m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2_2 * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| ((m1 * (coef_Znth (i) (c1) (0)) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (m1 * (coef_Znth (i) (c1) (0)) )) |]
.

Definition generate_new_constr_safety_wit_26 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval_2: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_3: Z) (res: Z) (c3: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval_2 = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1_2 * (coef_Znth (i_2) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2_2 * (coef_Znth (i_2) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1_2)
  **  ((( &( "m2" ) )) # Int  |-> m2_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "g" ) )) # Int  |-> retval_2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| False |]
.

Definition generate_new_constr_safety_wit_27 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval_2: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_3: Z) (res: Z) (c3: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((-INT_MAX) <= ((m2_2 * (coef_Znth (i_2) (c2) (0)) ) + (m1_2 * (coef_Znth (i_2) (c1) (0)) ) )) |] 
  &&  [| (((m2_2 * (coef_Znth (i_2) (c2) (0)) ) + (m1_2 * (coef_Znth (i_2) (c1) (0)) ) ) <= INT_MAX) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval_2 = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1_2 * (coef_Znth (i_2) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2_2 * (coef_Znth (i_2) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1_2)
  **  ((( &( "m2" ) )) # Int  |-> m2_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "g" ) )) # Int  |-> retval_2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| False |]
.

Definition generate_new_constr_safety_wit_28 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1_2 * (coef_Znth (i_2) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2_2 * (coef_Znth (i_2) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1_2)
  **  ((( &( "m2" ) )) # Int  |-> m2_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constr_safety_wit_29 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval_2: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (m2_2: Z) (m1_2: Z) (l: Constraint) (retval_3: Z) (res: Z) (c3: Constraint) (i: Z) (m2: Z) (m1: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((-INT_MAX) <= ((m2 * (coef_Znth (i) (c2) (0)) ) + (m1 * (coef_Znth (i) (c1) (0)) ) )) |] 
  &&  [| (((m2 * (coef_Znth (i) (c2) (0)) ) + (m1 * (coef_Znth (i) (c1) (0)) ) ) <= INT_MAX) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i m1 m2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i_2 > num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1_2 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1_2 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2_2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2_2 )) |] 
  &&  [| (in_int_range i_2 m1_2 c1 ) |] 
  &&  [| (in_int_range i_2 m2_2 c2 ) |] 
  &&  [| (retval_2 = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1 * (coef_Znth (i) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2 * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "g" ) )) # Int  |-> retval_2)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| (((m2 * (coef_Znth (i) (c2) (0)) ) + (m1 * (coef_Znth (i) (c1) (0)) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((m2 * (coef_Znth (i) (c2) (0)) ) + (m1 * (coef_Znth (i) (c1) (0)) ) )) |]
.

Definition generate_new_constr_safety_wit_30 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (m2_2: Z) (m1_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_3 = 1) |] 
  &&  [| ((-INT_MAX) <= ((m2_2 * (coef_Znth (i) (c2) (0)) ) + (m1_2 * (coef_Znth (i) (c1) (0)) ) )) |] 
  &&  [| (((m2_2 * (coef_Znth (i) (c2) (0)) ) + (m1_2 * (coef_Znth (i) (c1) (0)) ) ) <= INT_MAX) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i_2 > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i_2 m1 c1 ) |] 
  &&  [| (in_int_range i_2 m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((res + (i * sizeof(INT) ) )) # Int  |-> ((m2_2 * (coef_Znth (i) (c2) (0)) ) + (m1_2 * (coef_Znth (i) (c1) (0)) ) ))
  **  (coef_array_missing_i_rec res i 0 (num_pre + 1 ) c3 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "m1" ) )) # Int  |-> m1_2)
  **  ((( &( "m2" ) )) # Int  |-> m2_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition generate_new_constr_entail_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) ,
  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  [| (((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) > 0) |] 
  &&  [| (((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) > 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (num_pre + 1 )) |] 
  &&  [| ((INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ) = (INT_MAX ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) )) |] 
  &&  [| (((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) ) = ((-INT_MAX) ÷ ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) )) |] 
  &&  [| ((INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ) = (INT_MAX ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) )) |] 
  &&  [| (((-INT_MAX) ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) ) = ((-INT_MAX) ÷ ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) )) |] 
  &&  [| (in_int_range 0 ((-(coef_Znth (cur_num_pre) (c2) (0))) ÷ retval ) c1 ) |] 
  &&  [| (in_int_range 0 ((coef_Znth (cur_num_pre) (c1) (0)) ÷ retval ) c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_entail_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c2) (0)) <= ub2) |] 
  &&  [| ((coef_Znth (i) (c2) (0)) >= lb2) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range (i + 1 ) m1 c1 ) |] 
  &&  [| (in_int_range (i + 1 ) m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_entail_wit_3 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array retval_2 (num_pre + 1 ) l )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  EX (c3: Constraint) ,
  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) 0 m1 m2 c1 c2 c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array retval_2 (num_pre + 1 ) c3 )
.

Definition generate_new_constr_entail_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3_2: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_3 = 1) |] 
  &&  [| ((-INT_MAX) <= ((m2_2 * (coef_Znth (i_2) (c2) (0)) ) + (m1_2 * (coef_Znth (i_2) (c1) (0)) ) )) |] 
  &&  [| (((m2_2 * (coef_Znth (i_2) (c2) (0)) ) + (m1_2 * (coef_Znth (i_2) (c1) (0)) ) ) <= INT_MAX) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3_2 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3_2 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((res + (i_2 * sizeof(INT) ) )) # Int  |-> ((m2_2 * (coef_Znth (i_2) (c2) (0)) ) + (m1_2 * (coef_Znth (i_2) (c1) (0)) ) ))
  **  (coef_array_missing_i_rec res i_2 0 (num_pre + 1 ) c3_2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  EX (c3: Constraint) ,
  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) (i_2 + 1 ) m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_return_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3_2: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3_2 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3_2 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  (EX (c3: Constraint) ,
  [| (0 <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) c1 c2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array 0 (num_pre + 1 ) c3 ))
  ||
  ([| (0 = 0) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 ))
.

Definition generate_new_constr_return_wit_2_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c1) (0)) > ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  (EX (c3: Constraint) ,
  [| (0 <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) c1 c2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array 0 (num_pre + 1 ) c3 ))
  ||
  ([| (0 = 0) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 ))
.

Definition generate_new_constr_return_wit_2_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c1) (0)) < lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  (EX (c3: Constraint) ,
  [| (0 <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) c1 c2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array 0 (num_pre + 1 ) c3 ))
  ||
  ([| (0 = 0) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 ))
.

Definition generate_new_constr_return_wit_3_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c2) (0)) > ub2) |] 
  &&  [| ((coef_Znth (i) (c2) (0)) >= lb2) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  (EX (c3: Constraint) ,
  [| (0 <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) c1 c2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array 0 (num_pre + 1 ) c3 ))
  ||
  ([| (0 = 0) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 ))
.

Definition generate_new_constr_return_wit_3_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c2) (0)) < lb2) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  (EX (c3: Constraint) ,
  [| (0 <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) c1 c2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array 0 (num_pre + 1 ) c3 ))
  ||
  ([| (0 = 0) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 ))
.

Definition generate_new_constr_return_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (m2_2: Z) (m1_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3_2: Constraint) (i: Z) (m2: Z) (m1: Z) ,
  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i m1 m2 c1 c2 c3_2 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3_2 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i_2 > num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1_2 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1_2 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2_2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2_2 )) |] 
  &&  [| (in_int_range i_2 m1_2 c1 ) |] 
  &&  [| (in_int_range i_2 m2_2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3_2 )
|--
  (EX (c3: Constraint) ,
  [| (res <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) c1 c2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 ))
  ||
  ([| (res = 0) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 ))
.

Definition generate_new_constr_partial_solve_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) ,
  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((r1_pre + (cur_num_pre * sizeof(INT) ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  (coef_array_missing_i_rec r1_pre cur_num_pre 0 (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) ,
  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((r2_pre + (cur_num_pre * sizeof(INT) ) )) # Int  |-> (coef_Znth (cur_num_pre) (c2) (0)))
  **  (coef_array_missing_i_rec r2_pre cur_num_pre 0 (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
.

Definition generate_new_constr_partial_solve_wit_3_pure := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) ,
  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  ((( &( "g" ) )) # Int  |->_)
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
|--
  [| (0 < (coef_Znth (cur_num_pre) (c1) (0))) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| (0 <= (-(coef_Znth (cur_num_pre) (c2) (0)))) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
.

Definition generate_new_constr_partial_solve_wit_3_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) ,
  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  [| (0 < (coef_Znth (cur_num_pre) (c1) (0))) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| (0 <= (-(coef_Znth (cur_num_pre) (c2) (0)))) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
.

Definition generate_new_constr_partial_solve_wit_3 := generate_new_constr_partial_solve_wit_3_pure -> generate_new_constr_partial_solve_wit_3_aux.

Definition generate_new_constr_partial_solve_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((r1_pre + (i * sizeof(INT) ) )) # Int  |-> (coef_Znth (i) (c1) (0)))
  **  (coef_array_missing_i_rec r1_pre i 0 (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_5 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((r1_pre + (i * sizeof(INT) ) )) # Int  |-> (coef_Znth (i) (c1) (0)))
  **  (coef_array_missing_i_rec r1_pre i 0 (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_6 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((r2_pre + (i * sizeof(INT) ) )) # Int  |-> (coef_Znth (i) (c2) (0)))
  **  (coef_array_missing_i_rec r2_pre i 0 (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
.

Definition generate_new_constr_partial_solve_wit_7 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| ((coef_Znth (i) (c2) (0)) >= lb2) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
|--
  [| ((coef_Znth (i) (c2) (0)) >= lb2) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) <= ub1) |] 
  &&  [| ((coef_Znth (i) (c1) (0)) >= lb1) |] 
  &&  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((r2_pre + (i * sizeof(INT) ) )) # Int  |-> (coef_Znth (i) (c2) (0)))
  **  (coef_array_missing_i_rec r2_pre i 0 (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
.

Definition generate_new_constr_partial_solve_wit_8 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) ,
  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
|--
  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_9 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) ,
  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((r2_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (coef_Znth (i_2) (c2) (0)))
  **  (coef_array_missing_i_rec r2_pre i_2 0 (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_10 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) ,
  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((r1_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (coef_Znth (i_2) (c1) (0)))
  **  (coef_array_missing_i_rec r1_pre i_2 0 (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_11_pure := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i_2: Z) (m2_2: Z) (m1_2: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i: Z) (m2: Z) (m1: Z) ,
  [| (i <= num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i m1 m2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i_2 > num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1_2 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1_2 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2_2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2_2 )) |] 
  &&  [| (in_int_range i_2 m1_2 c1 ) |] 
  &&  [| (in_int_range i_2 m2_2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  ((( &( "y" ) )) # Int  |-> (m1 * (coef_Znth (i) (c1) (0)) ))
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  ((( &( "x" ) )) # Int  |-> (m2 * (coef_Znth (i) (c2) (0)) ))
  **  ((( &( "m1" ) )) # Int  |-> m1)
  **  ((( &( "m2" ) )) # Int  |-> m2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (coef_array res (num_pre + 1 ) c3 )
  **  ((( &( "ub1" ) )) # Int  |-> ub1)
  **  ((( &( "lb1" ) )) # Int  |-> lb1)
  **  ((( &( "ub2" ) )) # Int  |-> ub2)
  **  ((( &( "lb2" ) )) # Int  |-> lb2)
  **  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> (-(coef_Znth (cur_num_pre) (c2) (0))))
  **  ((( &( "an" ) )) # Int  |-> (coef_Znth (cur_num_pre) (c1) (0)))
|--
  [| ((m1 * (coef_Znth (i) (c1) (0)) ) <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= (m1 * (coef_Znth (i) (c1) (0)) )) |] 
  &&  [| ((m2 * (coef_Znth (i) (c2) (0)) ) <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= (m2 * (coef_Znth (i) (c2) (0)) )) |]
.

Definition generate_new_constr_partial_solve_wit_11_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) ,
  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  [| ((m1_2 * (coef_Znth (i_2) (c1) (0)) ) <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= (m1_2 * (coef_Znth (i_2) (c1) (0)) )) |] 
  &&  [| ((m2_2 * (coef_Znth (i_2) (c2) (0)) ) <= INT_MAX) |] 
  &&  [| ((-INT_MAX) <= (m2_2 * (coef_Znth (i_2) (c2) (0)) )) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_11 := generate_new_constr_partial_solve_wit_11_pure -> generate_new_constr_partial_solve_wit_11_aux.

Definition generate_new_constr_partial_solve_wit_12 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array res (num_pre + 1 ) c3 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

Definition generate_new_constr_partial_solve_wit_13 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2: Constraint) (c1: Constraint) (retval: Z) (lb2: Z) (ub2: Z) (lb1: Z) (ub1: Z) (i: Z) (m2: Z) (m1: Z) (l: Constraint) (retval_2: Z) (res: Z) (c3: Constraint) (i_2: Z) (m2_2: Z) (m1_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_3 = 1) |] 
  &&  [| ((-INT_MAX) <= ((m2_2 * (coef_Znth (i_2) (c2) (0)) ) + (m1_2 * (coef_Znth (i_2) (c1) (0)) ) )) |] 
  &&  [| (((m2_2 * (coef_Znth (i_2) (c2) (0)) ) + (m1_2 * (coef_Znth (i_2) (c1) (0)) ) ) <= INT_MAX) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
  **  (coef_array res (num_pre + 1 ) c3 )
|--
  [| (retval_3 <> 0) |] 
  &&  [| (retval_3 = 1) |] 
  &&  [| ((-INT_MAX) <= ((m2_2 * (coef_Znth (i_2) (c2) (0)) ) + (m1_2 * (coef_Znth (i_2) (c1) (0)) ) )) |] 
  &&  [| (((m2_2 * (coef_Znth (i_2) (c2) (0)) ) + (m1_2 * (coef_Znth (i_2) (c1) (0)) ) ) <= INT_MAX) |] 
  &&  [| (i_2 <= num_pre) |] 
  &&  [| (m1_2 > 0) |] 
  &&  [| (m2_2 > 0) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= (num_pre + 1 )) |] 
  &&  [| (in_int_range (num_pre + 1 ) m1_2 c1 ) |] 
  &&  [| (in_int_range (num_pre + 1 ) m2_2 c2 ) |] 
  &&  [| (generate_new_constraint_partial (Zto_nat ((cur_num_pre - 1 ))) i_2 m1_2 m2_2 c1 c2 c3 ) |] 
  &&  [| (res <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) l ) |] 
  &&  [| (i > num_pre) |] 
  &&  [| (m1 > 0) |] 
  &&  [| (m2 > 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (num_pre + 1 )) |] 
  &&  [| (ub1 = (INT_MAX ÷ m1 )) |] 
  &&  [| (lb1 = ((-INT_MAX) ÷ m1 )) |] 
  &&  [| (ub2 = (INT_MAX ÷ m2 )) |] 
  &&  [| (lb2 = ((-INT_MAX) ÷ m2 )) |] 
  &&  [| (in_int_range i m1 c1 ) |] 
  &&  [| (in_int_range i m2 c2 ) |] 
  &&  [| (retval = (Zgcd ((coef_Znth (cur_num_pre) (c1) (0))) ((-(coef_Znth (cur_num_pre) (c2) (0)))))) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) > 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (c2) (0)) < 0) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (c2) (0))) <= INT_MAX) |]
  &&  (((res + (i_2 * sizeof(INT) ) )) # Int  |->_)
  **  (coef_array_missing_i_rec res i_2 0 (num_pre + 1 ) c3 )
  **  (coef_array r1_pre (num_pre + 1 ) c1 )
  **  (coef_array r2_pre (num_pre + 1 ) c2 )
.

(*----- Function generate_new_constraint_list -----*)

Definition generate_new_constraint_list_safety_wit_1 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) ,
  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constraint_list_safety_wit_2 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (p1: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11: (@list Constraint)) (x1: Constraint) (l12: (@list Constraint)) ,
  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) ((cons (x1) (l12))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11 x1 l21 l22 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (l12_2 = (cons (x) (l13))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) (l12_2))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11_2 l2 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  (InequList_seg r1_pre p1 n l11 )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x1 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12 )
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constraint_list_safety_wit_3 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constraint_list_safety_wit_4 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  [| False |]
.

Definition generate_new_constraint_list_safety_wit_5 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) x1 x_2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (coef_array retval (num_pre + 1 ) c3 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constraint_list_safety_wit_6 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) x1 x_2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (coef_array retval (num_pre + 1 ) c3 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  [| False |]
.

Definition generate_new_constraint_list_safety_wit_7 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_new_constraint_list_entail_wit_1 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) ,
  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 )
  **  (InequList init_pre n l_init )
|--
  EX (l3: (@list Constraint))  (l4: (@list Constraint))  (l11: (@list Constraint))  (l12: (@list Constraint)) ,
  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre r1_pre n l11 )
  **  (InequList r1_pre n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList init_pre n l3 )
.

Definition generate_new_constraint_list_entail_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (p1_next_2: Z) (p1_coef_2: Z) (x: Constraint) (l13: (@list Constraint)) ,
  [| (l12_2 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) (l12_2))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11_2 l2 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre p1 n l11_2 )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  (coef_array p1_coef_2 n x )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next_2)
  **  (InequList p1_next_2 n l13 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3_2 )
|--
  EX (p1_next: Z)  (p1_coef: Z)  (l3: (@list Constraint))  (l4: (@list Constraint))  (l21: (@list Constraint))  (l22: (@list Constraint))  (l11: (@list Constraint))  (x1: Constraint)  (l12: (@list Constraint)) ,
  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) ((cons (x1) (l12))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11 x1 l21 l22 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (l12_2 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) (l12_2))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11_2 l2 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre p1 n l11 )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x1 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12 )
  **  (InequList_seg r2_pre r2_pre n l21 )
  **  (InequList r2_pre n l22 )
  **  (InequList res n l3 )
.

Definition generate_new_constraint_list_entail_wit_3 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (p2: Z) (p1_next_2: Z) (p1_coef_2: Z) (l3_3: (@list Constraint)) (l4_3: (@list Constraint)) (p1_2: Z) (l21_2: (@list Constraint)) (l22_2: (@list Constraint)) (l11_3: (@list Constraint)) (x1_2: Constraint) (l12_3: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval_2: Z) (retval: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) x1_2 x_2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (l22_2 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_3) ((cons (x1_2) (l12_3))))) |] 
  &&  [| (l2 = (app (l21_2) (l22_2))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_3 x1_2 l21_2 l22_2 l4_3 ) |] 
  &&  [| (l3_3 = (app (l4_3) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_3 ) |] 
  &&  [| (l12_2 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) (l12_2))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11_2 l2 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList retval n (cons (c3) (l3_3)) )
  **  (coef_array p1_coef_2 (num_pre + 1 ) x1_2 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (InequList_seg r2_pre p2 n l21_2 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  (InequList_seg r1_pre p1_2 n l11_3 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef_2)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next_2)
  **  (InequList p1_next_2 n l12_3 )
|--
  EX (p1_next: Z)  (p1_coef: Z)  (l3: (@list Constraint))  (l4: (@list Constraint))  (l21: (@list Constraint))  (l22: (@list Constraint))  (l11: (@list Constraint))  (x1: Constraint)  (l12: (@list Constraint)) ,
  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) ((cons (x1) (l12))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11 x1 l21 l22 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (l12_2 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) (l12_2))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11_2 l2 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre p1_2 n l11 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12 )
  **  (InequList_seg r2_pre p2_next n l21 )
  **  (InequList p2_next n l22 )
  **  (InequList retval n l3 )
.

Definition generate_new_constraint_list_entail_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1_2: Z) (l3_3: (@list Constraint)) (l4_3: (@list Constraint)) (l11_3: (@list Constraint)) (l12_3: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) ,
  [| (p2 = 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12_3 = (cons (x) (l13))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_3) (l12_3))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11_3 l2 l4_3 ) |] 
  &&  [| (l3_3 = (app (l4_3) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre p1 n l11_2 )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x1 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  (InequList res n l3_2 )
|--
  EX (l3: (@list Constraint))  (l4: (@list Constraint))  (l11: (@list Constraint))  (l12: (@list Constraint)) ,
  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre p1_next n l11 )
  **  (InequList p1_next n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3 )
.

Definition generate_new_constraint_list_return_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_3: (@list Constraint)) (l4_3: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_3 ) |] 
  &&  [| (l3_3 = (app (l4_3) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_3 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
|--
  ([| (0 = 0) |]
  &&  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 ))
  ||
  (EX (l3: (@list Constraint))  (l4: (@list Constraint)) ,
  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l1 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |]
  &&  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 )
  **  (InequList 0 n l3 ))
.

Definition generate_new_constraint_list_return_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) ,
  [| (p1 = 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3_2 )
|--
  ([| (res = 0) |]
  &&  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 ))
  ||
  (EX (l3: (@list Constraint))  (l4: (@list Constraint)) ,
  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l1 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |]
  &&  (InequList r1_pre n l1 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3 ))
.

Definition generate_new_constraint_list_partial_solve_wit_1_pure := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) ,
  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3 )
|--
  [| (p1 <> 0) |]
.

Definition generate_new_constraint_list_partial_solve_wit_1_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (res: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) ,
  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3 )
|--
  [| (p1 <> 0) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre p1 n l11 )
  **  (InequList p1 n l12 )
  **  (InequList r2_pre n l2 )
  **  (InequList res n l3 )
.

Definition generate_new_constraint_list_partial_solve_wit_1 := generate_new_constraint_list_partial_solve_wit_1_pure -> generate_new_constraint_list_partial_solve_wit_1_aux.

Definition generate_new_constraint_list_partial_solve_wit_2_pure := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1_2: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (p1: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11: (@list Constraint)) (x1: Constraint) (l12: (@list Constraint)) ,
  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) ((cons (x1) (l12))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11 x1 l21 l22 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (l12_2 = (cons (x) (l13))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) (l12_2))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11_2 l2 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  (InequList_seg r1_pre p1 n l11 )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x1 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12 )
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3 )
|--
  [| (p2 <> 0) |]
.

Definition generate_new_constraint_list_partial_solve_wit_2_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) ,
  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  (InequList res n l3_2 )
|--
  [| (p2 <> 0) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r2_pre p2 n l21 )
  **  (InequList p2 n l22 )
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
.

Definition generate_new_constraint_list_partial_solve_wit_2 := generate_new_constraint_list_partial_solve_wit_2_pure -> generate_new_constraint_list_partial_solve_wit_2_aux.

Definition generate_new_constraint_list_partial_solve_wit_3_pure := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x_2: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x: Constraint) (l23: (@list Constraint)) ,
  [| (l22 = (cons (x) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x_2) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n l3_2 )
|--
  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (x) (0))) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (x) (0)) < 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (x1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (x1) (0)) > 0) |]
.

Definition generate_new_constraint_list_partial_solve_wit_3_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) ,
  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (coef_array p2_coef n x_2 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x1 )
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
|--
  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < (num_pre + 1 )) |] 
  &&  [| ((num_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((-(coef_Znth (cur_num_pre) (x_2) (0))) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (x_2) (0)) < 0) |] 
  &&  [| ((coef_Znth (cur_num_pre) (x1) (0)) <= INT_MAX) |] 
  &&  [| ((coef_Znth (cur_num_pre) (x1) (0)) > 0) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
.

Definition generate_new_constraint_list_partial_solve_wit_3 := generate_new_constraint_list_partial_solve_wit_3_pure -> generate_new_constraint_list_partial_solve_wit_3_aux.

Definition generate_new_constraint_list_partial_solve_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (InequList res n l3_2 )
  **  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
.

Definition generate_new_constraint_list_partial_solve_wit_5 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init: (@list Constraint)) (l2: (@list Constraint)) (l1: (@list Constraint)) (n: Z) (p1: Z) (l3: (@list Constraint)) (l4: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (x: Constraint) (l13: (@list Constraint)) (res: Z) (p2: Z) (p1_next: Z) (p1_coef: Z) (l3_2: (@list Constraint)) (l4_2: (@list Constraint)) (p1_2: Z) (l21: (@list Constraint)) (l22: (@list Constraint)) (l11_2: (@list Constraint)) (x1: Constraint) (l12_2: (@list Constraint)) (p2_next: Z) (p2_coef: Z) (x_2: Constraint) (l23: (@list Constraint)) (c3: Constraint) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) x1 x_2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (coef_array retval (num_pre + 1 ) c3 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
  **  (InequList res n l3_2 )
|--
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (generate_new_constraint (Zto_nat ((cur_num_pre - 1 ))) x1 x_2 c3 ) |] 
  &&  [| (abs_in_int_range (num_pre + 1 ) c3 ) |] 
  &&  [| (l22 = (cons (x_2) (l23))) |] 
  &&  [| (p2 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11_2) ((cons (x1) (l12_2))))) |] 
  &&  [| (l2 = (app (l21) (l22))) |] 
  &&  [| (p1_2 <> 0) |] 
  &&  [| (generate_new_constraints_partial (Zto_nat ((cur_num_pre - 1 ))) l11_2 x1 l21 l22 l4_2 ) |] 
  &&  [| (l3_2 = (app (l4_2) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3_2 ) |] 
  &&  [| (l12 = (cons (x) (l13))) |] 
  &&  [| (p1 <> 0) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (l1 = (app (l11) (l12))) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cur_num_pre - 1 ))) l11 l2 l4 ) |] 
  &&  [| (l3 = (app (l4) (l_init))) |] 
  &&  [| (LP_abs_in_int_range n l3 ) |] 
  &&  [| (n = (num_pre + 1 )) |] 
  &&  [| (0 <= cur_num_pre) |] 
  &&  [| (cur_num_pre < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cur_num_pre l1 ) |] 
  &&  [| (InequList_nth_neg cur_num_pre l2 ) |] 
  &&  [| (LP_abs_in_int_range n l1 ) |] 
  &&  [| (LP_abs_in_int_range n l2 ) |] 
  &&  [| (LP_abs_in_int_range n l_init ) |]
  &&  (coef_array retval n c3 )
  **  (InequList res n l3_2 )
  **  (coef_array p1_coef (num_pre + 1 ) x1 )
  **  (coef_array p2_coef (num_pre + 1 ) x_2 )
  **  (InequList_seg r2_pre p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
  **  (InequList_seg r1_pre p1_2 n l11_2 )
  **  ((&((p1_2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p1_2)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l12_2 )
.

Definition generate_new_constraint_list_which_implies_wit_1 := 
forall (n: Z) (l12: (@list Constraint)) (l11: (@list Constraint)) (p1: Z) (r1: Z) ,
  [| (p1 <> 0) |]
  &&  (InequList_seg r1 p1 n l11 )
  **  (InequList p1 n l12 )
|--
  EX (p1_next: Z)  (p1_coef: Z)  (x: Constraint)  (l13: (@list Constraint)) ,
  [| (l12 = (cons (x) (l13))) |]
  &&  (InequList_seg r1 p1 n l11 )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  (coef_array p1_coef n x )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n l13 )
.

Definition generate_new_constraint_list_which_implies_wit_2 := 
forall (n: Z) (l22: (@list Constraint)) (l21: (@list Constraint)) (p2: Z) (r2: Z) ,
  [| (p2 <> 0) |]
  &&  (InequList_seg r2 p2 n l21 )
  **  (InequList p2 n l22 )
|--
  EX (p2_next: Z)  (p2_coef: Z)  (x: Constraint)  (l23: (@list Constraint)) ,
  [| (l22 = (cons (x) (l23))) |]
  &&  (InequList_seg r2 p2 n l21 )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (coef_array p2_coef n x )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n l23 )
.

(*----- Function real_shadow -----*)

Definition real_shadow_safety_wit_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) ,
  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l2 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition real_shadow_safety_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper_2: Z) (BP0_lower_2: Z) (BP0_remain_2: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper_2: Z) (BP0_lower_2: Z) (BP0_remain_2: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_remain = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_5 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> 0)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_6 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper_2: Z) (BP0_lower_2: Z) (BP0_remain_2: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_upper <> 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_7 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper_2: Z) (BP0_lower_2: Z) (BP0_remain_2: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_remain <> 0) |] 
  &&  [| (BP0_upper <> 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| False |]
.

Definition real_shadow_safety_wit_8 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper_2: Z) (BP0_lower_2: Z) (BP0_remain_2: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_remain = 0) |] 
  &&  [| (BP0_upper <> 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_9 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper_2: Z) (BP0_lower_2: Z) (BP0_remain_2: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_remain <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_10 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper_2: Z) (BP0_lower_2: Z) (BP0_remain_2: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_remain = 0) |] 
  &&  [| (BP0_remain <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| False |]
.

Definition real_shadow_safety_wit_11 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_12 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> 0)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_13 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_14 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_15 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| False |]
.

Definition real_shadow_safety_wit_16 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_17 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_safety_wit_18 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| False |]
.

Definition real_shadow_safety_wit_19 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition real_shadow_safety_wit_20 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition real_shadow_safety_wit_21 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition real_shadow_safety_wit_22 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition real_shadow_safety_wit_23 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| ((cnt - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cnt - 1 )) |]
.

Definition real_shadow_safety_wit_24 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  [| ((cnt - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cnt - 1 )) |]
.

Definition real_shadow_safety_wit_25 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) ,
  [| (cnt < 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> r)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition real_shadow_entail_wit_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) ,
  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList p1 (n_pre + 1 ) l1 )
|--
  EX (l2: (@list Constraint)) ,
  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList p1 (n_pre + 1 ) l2 )
.

Definition real_shadow_entail_wit_2_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2_2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2_2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  EX (l2: (@list Constraint)) ,
  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= (cnt - 1 )) |] 
  &&  [| ((cnt - 1 ) <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList retval (n_pre + 1 ) l2 )
.

Definition real_shadow_entail_wit_2_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2_2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2_2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  EX (l2: (@list Constraint)) ,
  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= (cnt - 1 )) |] 
  &&  [| ((cnt - 1 ) <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList retval (n_pre + 1 ) l2 )
.

Definition real_shadow_return_wit_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2_2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2_2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> 0)
|--
  ([| (0 = 1) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX (p2: Z)  (l2: (@list Constraint)) ,
  [| (0 = 0) |] 
  &&  [| (LP_implies l1 l2 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
.

Definition real_shadow_return_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2_2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2_2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> 0)
|--
  ([| (0 = 1) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX (p2: Z)  (l2: (@list Constraint)) ,
  [| (0 = 0) |] 
  &&  [| (LP_implies l1 l2 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
.

Definition real_shadow_return_wit_3_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2_2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2_2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  ([| (1 = 1) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX (p2: Z)  (l2: (@list Constraint)) ,
  [| (1 = 0) |] 
  &&  [| (LP_implies l1 l2 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
.

Definition real_shadow_return_wit_3_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2_2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2_2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  ([| (1 = 1) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX (p2: Z)  (l2: (@list Constraint)) ,
  [| (1 = 0) |] 
  &&  [| (LP_implies l1 l2 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
.

Definition real_shadow_return_wit_3_3 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2_2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2_2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  ([| (1 = 1) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX (p2: Z)  (l2: (@list Constraint)) ,
  [| (1 = 0) |] 
  &&  [| (LP_implies l1 l2 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
.

Definition real_shadow_return_wit_3_4 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2_2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2_2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2_2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  ([| (1 = 1) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX (p2: Z)  (l2: (@list Constraint)) ,
  [| (1 = 0) |] 
  &&  [| (LP_implies l1 l2 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
.

Definition real_shadow_return_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2_2: (@list Constraint)) (cnt: Z) ,
  [| (cnt < 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2_2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2_2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l2_2 )
|--
  ([| (0 = 1) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX (p2: Z)  (l2: (@list Constraint)) ,
  [| (0 = 0) |] 
  &&  [| (LP_implies l1 l2 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
.

Definition real_shadow_partial_solve_wit_1_pure := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) ,
  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l2 )
|--
  [| (1 <= cnt) |] 
  &&  [| (cnt < (n_pre + 1 )) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |]
.

Definition real_shadow_partial_solve_wit_1_aux := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) ,
  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((pr_pre) # Ptr  |-> p1)
  **  (InequList r (n_pre + 1 ) l2 )
|--
  [| (1 <= cnt) |] 
  &&  [| (cnt < (n_pre + 1 )) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r (n_pre + 1 ) l2 )
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_1 := real_shadow_partial_solve_wit_1_pure -> real_shadow_partial_solve_wit_1_aux.

Definition real_shadow_partial_solve_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_4_pure := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper_2: Z) (BP0_lower_2: Z) (BP0_remain_2: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_lower <> 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (BP0_upper <> 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| ((n_pre + 1 ) = (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt < (n_pre + 1 )) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |]
.

Definition real_shadow_partial_solve_wit_4_aux := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| ((n_pre + 1 ) = (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt < (n_pre + 1 )) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_4 := real_shadow_partial_solve_wit_4_pure -> real_shadow_partial_solve_wit_4_aux.

Definition real_shadow_partial_solve_wit_5_pure := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper_2: Z) (BP0_lower_2: Z) (BP0_remain_2: Z) (r: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_remain <> 0) |] 
  &&  [| (BP0_remain <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper_2 = 0) |] 
  &&  [| (BP0_lower_2 = 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  [| ((n_pre + 1 ) = (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt < (n_pre + 1 )) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |]
.

Definition real_shadow_partial_solve_wit_5_aux := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) ,
  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| ((n_pre + 1 ) = (n_pre + 1 )) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| (cnt < (n_pre + 1 )) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList BP0_remain_2 (n_pre + 1 ) re )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_5 := real_shadow_partial_solve_wit_5_pure -> real_shadow_partial_solve_wit_5_aux.

Definition real_shadow_partial_solve_wit_6 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_7 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (retval = 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_8 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_9 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (retval = 0) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_upper_2 (n_pre + 1 ) up )
  **  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_10 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (retval = 0) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_11 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_lower_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (BP0_upper_2 <> 0) |] 
  &&  [| (BP0_remain_2 = 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_12 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (retval = 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Definition real_shadow_partial_solve_wit_13 := 
forall (n_pre: Z) (pr_pre: Z) (l1: (@list Constraint)) (p1: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (l2: (@list Constraint)) (cnt: Z) (BP0_remain_2: Z) (BP0_lower_2: Z) (BP0_upper_2: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l3: (@list Constraint)) (l4: (@list Constraint)) (retval: Z) ,
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
|--
  [| (generate_new_constraints (Zto_nat ((cnt - 1 ))) up lo l4 ) |] 
  &&  [| (l3 = (app (l4) (re))) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l3 ) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (BP0_remain_2 <> 0) |] 
  &&  [| (eliminate_xn (Zto_nat ((cnt - 1 ))) l2 b ) |] 
  &&  [| (form_BP up lo re b ) |] 
  &&  [| (InequList_nth_pos cnt up ) |] 
  &&  [| (InequList_nth_neg cnt lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) up ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) lo ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) re ) |] 
  &&  [| (cnt >= 2) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (1 <= cnt) |] 
  &&  [| (cnt <= n_pre) |] 
  &&  [| (LP_implies l1 l2 ) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l2 ) |] 
  &&  [| (BP0 <> 0) |] 
  &&  [| (pr_pre <> 0) |] 
  &&  [| (n_pre >= 1) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (n_pre <= (INT_MAX - 1 )) |] 
  &&  [| (BP0_upper = 0) |] 
  &&  [| (BP0_lower = 0) |] 
  &&  [| (BP0_remain = 0) |] 
  &&  [| (LP_abs_in_int_range (n_pre + 1 ) l1 ) |]
  &&  (InequList BP0_lower_2 (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include fme_Strategy_Correct.

Axiom proof_of_gcd_safety_wit_1 : gcd_safety_wit_1.
Axiom proof_of_gcd_safety_wit_2 : gcd_safety_wit_2.
Axiom proof_of_gcd_return_wit_1 : gcd_return_wit_1.
Axiom proof_of_gcd_return_wit_2 : gcd_return_wit_2.
Axiom proof_of_gcd_partial_solve_wit_1_pure : gcd_partial_solve_wit_1_pure.
Axiom proof_of_gcd_partial_solve_wit_1 : gcd_partial_solve_wit_1.
Axiom proof_of_check_add_safe_safety_wit_1 : check_add_safe_safety_wit_1.
Axiom proof_of_check_add_safe_safety_wit_2 : check_add_safe_safety_wit_2.
Axiom proof_of_check_add_safe_safety_wit_3 : check_add_safe_safety_wit_3.
Axiom proof_of_check_add_safe_safety_wit_4 : check_add_safe_safety_wit_4.
Axiom proof_of_check_add_safe_safety_wit_5 : check_add_safe_safety_wit_5.
Axiom proof_of_check_add_safe_safety_wit_6 : check_add_safe_safety_wit_6.
Axiom proof_of_check_add_safe_return_wit_1_1 : check_add_safe_return_wit_1_1.
Axiom proof_of_check_add_safe_return_wit_1_2 : check_add_safe_return_wit_1_2.
Axiom proof_of_check_add_safe_return_wit_2_1 : check_add_safe_return_wit_2_1.
Axiom proof_of_check_add_safe_return_wit_2_2 : check_add_safe_return_wit_2_2.
Axiom proof_of_NilInequList_safety_wit_1 : NilInequList_safety_wit_1.
Axiom proof_of_NilInequList_return_wit_1 : NilInequList_return_wit_1.
Axiom proof_of_ConsInequList_return_wit_1 : ConsInequList_return_wit_1.
Axiom proof_of_ConsInequList_partial_solve_wit_1 : ConsInequList_partial_solve_wit_1.
Axiom proof_of_free_InequList_safety_wit_1 : free_InequList_safety_wit_1.
Axiom proof_of_free_InequList_safety_wit_2 : free_InequList_safety_wit_2.
Axiom proof_of_free_InequList_safety_wit_3 : free_InequList_safety_wit_3.
Axiom proof_of_free_InequList_safety_wit_4 : free_InequList_safety_wit_4.
Axiom proof_of_free_InequList_return_wit_1 : free_InequList_return_wit_1.
Axiom proof_of_free_InequList_return_wit_2_1 : free_InequList_return_wit_2_1.
Axiom proof_of_free_InequList_return_wit_2_2 : free_InequList_return_wit_2_2.
Axiom proof_of_free_InequList_return_wit_2_3 : free_InequList_return_wit_2_3.
Axiom proof_of_free_InequList_return_wit_2_4 : free_InequList_return_wit_2_4.
Axiom proof_of_free_InequList_partial_solve_wit_1 : free_InequList_partial_solve_wit_1.
Axiom proof_of_free_InequList_partial_solve_wit_2 : free_InequList_partial_solve_wit_2.
Axiom proof_of_free_InequList_partial_solve_wit_3 : free_InequList_partial_solve_wit_3.
Axiom proof_of_free_InequList_partial_solve_wit_4 : free_InequList_partial_solve_wit_4.
Axiom proof_of_free_InequList_partial_solve_wit_5 : free_InequList_partial_solve_wit_5.
Axiom proof_of_free_InequList_partial_solve_wit_6 : free_InequList_partial_solve_wit_6.
Axiom proof_of_free_InequList_partial_solve_wit_7 : free_InequList_partial_solve_wit_7.
Axiom proof_of_free_InequList_partial_solve_wit_8 : free_InequList_partial_solve_wit_8.
Axiom proof_of_eliminate_safety_wit_1 : eliminate_safety_wit_1.
Axiom proof_of_eliminate_safety_wit_2 : eliminate_safety_wit_2.
Axiom proof_of_eliminate_safety_wit_3 : eliminate_safety_wit_3.
Axiom proof_of_eliminate_entail_wit_1 : eliminate_entail_wit_1.
Axiom proof_of_eliminate_entail_wit_2 : eliminate_entail_wit_2.
Axiom proof_of_eliminate_entail_wit_3_1 : eliminate_entail_wit_3_1.
Axiom proof_of_eliminate_entail_wit_3_2 : eliminate_entail_wit_3_2.
Axiom proof_of_eliminate_entail_wit_3_3 : eliminate_entail_wit_3_3.
Axiom proof_of_eliminate_return_wit_1 : eliminate_return_wit_1.
Axiom proof_of_eliminate_partial_solve_wit_1 : eliminate_partial_solve_wit_1.
Axiom proof_of_eliminate_partial_solve_wit_2 : eliminate_partial_solve_wit_2.
Axiom proof_of_eliminate_partial_solve_wit_3 : eliminate_partial_solve_wit_3.
Axiom proof_of_eliminate_partial_solve_wit_4_pure : eliminate_partial_solve_wit_4_pure.
Axiom proof_of_eliminate_partial_solve_wit_4 : eliminate_partial_solve_wit_4.
Axiom proof_of_eliminate_partial_solve_wit_5 : eliminate_partial_solve_wit_5.
Axiom proof_of_eliminate_partial_solve_wit_6 : eliminate_partial_solve_wit_6.
Axiom proof_of_eliminate_which_implies_wit_1 : eliminate_which_implies_wit_1.
Axiom proof_of_generate_new_constr_safety_wit_1 : generate_new_constr_safety_wit_1.
Axiom proof_of_generate_new_constr_safety_wit_2 : generate_new_constr_safety_wit_2.
Axiom proof_of_generate_new_constr_safety_wit_3 : generate_new_constr_safety_wit_3.
Axiom proof_of_generate_new_constr_safety_wit_4 : generate_new_constr_safety_wit_4.
Axiom proof_of_generate_new_constr_safety_wit_5 : generate_new_constr_safety_wit_5.
Axiom proof_of_generate_new_constr_safety_wit_6 : generate_new_constr_safety_wit_6.
Axiom proof_of_generate_new_constr_safety_wit_7 : generate_new_constr_safety_wit_7.
Axiom proof_of_generate_new_constr_safety_wit_8 : generate_new_constr_safety_wit_8.
Axiom proof_of_generate_new_constr_safety_wit_9 : generate_new_constr_safety_wit_9.
Axiom proof_of_generate_new_constr_safety_wit_10 : generate_new_constr_safety_wit_10.
Axiom proof_of_generate_new_constr_safety_wit_11 : generate_new_constr_safety_wit_11.
Axiom proof_of_generate_new_constr_safety_wit_12 : generate_new_constr_safety_wit_12.
Axiom proof_of_generate_new_constr_safety_wit_13 : generate_new_constr_safety_wit_13.
Axiom proof_of_generate_new_constr_safety_wit_14 : generate_new_constr_safety_wit_14.
Axiom proof_of_generate_new_constr_safety_wit_15 : generate_new_constr_safety_wit_15.
Axiom proof_of_generate_new_constr_safety_wit_16 : generate_new_constr_safety_wit_16.
Axiom proof_of_generate_new_constr_safety_wit_17 : generate_new_constr_safety_wit_17.
Axiom proof_of_generate_new_constr_safety_wit_18 : generate_new_constr_safety_wit_18.
Axiom proof_of_generate_new_constr_safety_wit_19 : generate_new_constr_safety_wit_19.
Axiom proof_of_generate_new_constr_safety_wit_20 : generate_new_constr_safety_wit_20.
Axiom proof_of_generate_new_constr_safety_wit_21 : generate_new_constr_safety_wit_21.
Axiom proof_of_generate_new_constr_safety_wit_22 : generate_new_constr_safety_wit_22.
Axiom proof_of_generate_new_constr_safety_wit_23 : generate_new_constr_safety_wit_23.
Axiom proof_of_generate_new_constr_safety_wit_24 : generate_new_constr_safety_wit_24.
Axiom proof_of_generate_new_constr_safety_wit_25 : generate_new_constr_safety_wit_25.
Axiom proof_of_generate_new_constr_safety_wit_26 : generate_new_constr_safety_wit_26.
Axiom proof_of_generate_new_constr_safety_wit_27 : generate_new_constr_safety_wit_27.
Axiom proof_of_generate_new_constr_safety_wit_28 : generate_new_constr_safety_wit_28.
Axiom proof_of_generate_new_constr_safety_wit_29 : generate_new_constr_safety_wit_29.
Axiom proof_of_generate_new_constr_safety_wit_30 : generate_new_constr_safety_wit_30.
Axiom proof_of_generate_new_constr_entail_wit_1 : generate_new_constr_entail_wit_1.
Axiom proof_of_generate_new_constr_entail_wit_2 : generate_new_constr_entail_wit_2.
Axiom proof_of_generate_new_constr_entail_wit_3 : generate_new_constr_entail_wit_3.
Axiom proof_of_generate_new_constr_entail_wit_4 : generate_new_constr_entail_wit_4.
Axiom proof_of_generate_new_constr_return_wit_1 : generate_new_constr_return_wit_1.
Axiom proof_of_generate_new_constr_return_wit_2_1 : generate_new_constr_return_wit_2_1.
Axiom proof_of_generate_new_constr_return_wit_2_2 : generate_new_constr_return_wit_2_2.
Axiom proof_of_generate_new_constr_return_wit_3_1 : generate_new_constr_return_wit_3_1.
Axiom proof_of_generate_new_constr_return_wit_3_2 : generate_new_constr_return_wit_3_2.
Axiom proof_of_generate_new_constr_return_wit_4 : generate_new_constr_return_wit_4.
Axiom proof_of_generate_new_constr_partial_solve_wit_1 : generate_new_constr_partial_solve_wit_1.
Axiom proof_of_generate_new_constr_partial_solve_wit_2 : generate_new_constr_partial_solve_wit_2.
Axiom proof_of_generate_new_constr_partial_solve_wit_3_pure : generate_new_constr_partial_solve_wit_3_pure.
Axiom proof_of_generate_new_constr_partial_solve_wit_3 : generate_new_constr_partial_solve_wit_3.
Axiom proof_of_generate_new_constr_partial_solve_wit_4 : generate_new_constr_partial_solve_wit_4.
Axiom proof_of_generate_new_constr_partial_solve_wit_5 : generate_new_constr_partial_solve_wit_5.
Axiom proof_of_generate_new_constr_partial_solve_wit_6 : generate_new_constr_partial_solve_wit_6.
Axiom proof_of_generate_new_constr_partial_solve_wit_7 : generate_new_constr_partial_solve_wit_7.
Axiom proof_of_generate_new_constr_partial_solve_wit_8 : generate_new_constr_partial_solve_wit_8.
Axiom proof_of_generate_new_constr_partial_solve_wit_9 : generate_new_constr_partial_solve_wit_9.
Axiom proof_of_generate_new_constr_partial_solve_wit_10 : generate_new_constr_partial_solve_wit_10.
Axiom proof_of_generate_new_constr_partial_solve_wit_11_pure : generate_new_constr_partial_solve_wit_11_pure.
Axiom proof_of_generate_new_constr_partial_solve_wit_11 : generate_new_constr_partial_solve_wit_11.
Axiom proof_of_generate_new_constr_partial_solve_wit_12 : generate_new_constr_partial_solve_wit_12.
Axiom proof_of_generate_new_constr_partial_solve_wit_13 : generate_new_constr_partial_solve_wit_13.
Axiom proof_of_generate_new_constraint_list_safety_wit_1 : generate_new_constraint_list_safety_wit_1.
Axiom proof_of_generate_new_constraint_list_safety_wit_2 : generate_new_constraint_list_safety_wit_2.
Axiom proof_of_generate_new_constraint_list_safety_wit_3 : generate_new_constraint_list_safety_wit_3.
Axiom proof_of_generate_new_constraint_list_safety_wit_4 : generate_new_constraint_list_safety_wit_4.
Axiom proof_of_generate_new_constraint_list_safety_wit_5 : generate_new_constraint_list_safety_wit_5.
Axiom proof_of_generate_new_constraint_list_safety_wit_6 : generate_new_constraint_list_safety_wit_6.
Axiom proof_of_generate_new_constraint_list_safety_wit_7 : generate_new_constraint_list_safety_wit_7.
Axiom proof_of_generate_new_constraint_list_entail_wit_1 : generate_new_constraint_list_entail_wit_1.
Axiom proof_of_generate_new_constraint_list_entail_wit_2 : generate_new_constraint_list_entail_wit_2.
Axiom proof_of_generate_new_constraint_list_entail_wit_3 : generate_new_constraint_list_entail_wit_3.
Axiom proof_of_generate_new_constraint_list_entail_wit_4 : generate_new_constraint_list_entail_wit_4.
Axiom proof_of_generate_new_constraint_list_return_wit_1 : generate_new_constraint_list_return_wit_1.
Axiom proof_of_generate_new_constraint_list_return_wit_2 : generate_new_constraint_list_return_wit_2.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_1_pure : generate_new_constraint_list_partial_solve_wit_1_pure.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_1 : generate_new_constraint_list_partial_solve_wit_1.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_2_pure : generate_new_constraint_list_partial_solve_wit_2_pure.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_2 : generate_new_constraint_list_partial_solve_wit_2.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_3_pure : generate_new_constraint_list_partial_solve_wit_3_pure.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_3 : generate_new_constraint_list_partial_solve_wit_3.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_4 : generate_new_constraint_list_partial_solve_wit_4.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_5 : generate_new_constraint_list_partial_solve_wit_5.
Axiom proof_of_generate_new_constraint_list_which_implies_wit_1 : generate_new_constraint_list_which_implies_wit_1.
Axiom proof_of_generate_new_constraint_list_which_implies_wit_2 : generate_new_constraint_list_which_implies_wit_2.
Axiom proof_of_real_shadow_safety_wit_1 : real_shadow_safety_wit_1.
Axiom proof_of_real_shadow_safety_wit_2 : real_shadow_safety_wit_2.
Axiom proof_of_real_shadow_safety_wit_3 : real_shadow_safety_wit_3.
Axiom proof_of_real_shadow_safety_wit_4 : real_shadow_safety_wit_4.
Axiom proof_of_real_shadow_safety_wit_5 : real_shadow_safety_wit_5.
Axiom proof_of_real_shadow_safety_wit_6 : real_shadow_safety_wit_6.
Axiom proof_of_real_shadow_safety_wit_7 : real_shadow_safety_wit_7.
Axiom proof_of_real_shadow_safety_wit_8 : real_shadow_safety_wit_8.
Axiom proof_of_real_shadow_safety_wit_9 : real_shadow_safety_wit_9.
Axiom proof_of_real_shadow_safety_wit_10 : real_shadow_safety_wit_10.
Axiom proof_of_real_shadow_safety_wit_11 : real_shadow_safety_wit_11.
Axiom proof_of_real_shadow_safety_wit_12 : real_shadow_safety_wit_12.
Axiom proof_of_real_shadow_safety_wit_13 : real_shadow_safety_wit_13.
Axiom proof_of_real_shadow_safety_wit_14 : real_shadow_safety_wit_14.
Axiom proof_of_real_shadow_safety_wit_15 : real_shadow_safety_wit_15.
Axiom proof_of_real_shadow_safety_wit_16 : real_shadow_safety_wit_16.
Axiom proof_of_real_shadow_safety_wit_17 : real_shadow_safety_wit_17.
Axiom proof_of_real_shadow_safety_wit_18 : real_shadow_safety_wit_18.
Axiom proof_of_real_shadow_safety_wit_19 : real_shadow_safety_wit_19.
Axiom proof_of_real_shadow_safety_wit_20 : real_shadow_safety_wit_20.
Axiom proof_of_real_shadow_safety_wit_21 : real_shadow_safety_wit_21.
Axiom proof_of_real_shadow_safety_wit_22 : real_shadow_safety_wit_22.
Axiom proof_of_real_shadow_safety_wit_23 : real_shadow_safety_wit_23.
Axiom proof_of_real_shadow_safety_wit_24 : real_shadow_safety_wit_24.
Axiom proof_of_real_shadow_safety_wit_25 : real_shadow_safety_wit_25.
Axiom proof_of_real_shadow_entail_wit_1 : real_shadow_entail_wit_1.
Axiom proof_of_real_shadow_entail_wit_2_1 : real_shadow_entail_wit_2_1.
Axiom proof_of_real_shadow_entail_wit_2_2 : real_shadow_entail_wit_2_2.
Axiom proof_of_real_shadow_return_wit_1 : real_shadow_return_wit_1.
Axiom proof_of_real_shadow_return_wit_2 : real_shadow_return_wit_2.
Axiom proof_of_real_shadow_return_wit_3_1 : real_shadow_return_wit_3_1.
Axiom proof_of_real_shadow_return_wit_3_2 : real_shadow_return_wit_3_2.
Axiom proof_of_real_shadow_return_wit_3_3 : real_shadow_return_wit_3_3.
Axiom proof_of_real_shadow_return_wit_3_4 : real_shadow_return_wit_3_4.
Axiom proof_of_real_shadow_return_wit_4 : real_shadow_return_wit_4.
Axiom proof_of_real_shadow_partial_solve_wit_1_pure : real_shadow_partial_solve_wit_1_pure.
Axiom proof_of_real_shadow_partial_solve_wit_1 : real_shadow_partial_solve_wit_1.
Axiom proof_of_real_shadow_partial_solve_wit_2 : real_shadow_partial_solve_wit_2.
Axiom proof_of_real_shadow_partial_solve_wit_3 : real_shadow_partial_solve_wit_3.
Axiom proof_of_real_shadow_partial_solve_wit_4_pure : real_shadow_partial_solve_wit_4_pure.
Axiom proof_of_real_shadow_partial_solve_wit_4 : real_shadow_partial_solve_wit_4.
Axiom proof_of_real_shadow_partial_solve_wit_5_pure : real_shadow_partial_solve_wit_5_pure.
Axiom proof_of_real_shadow_partial_solve_wit_5 : real_shadow_partial_solve_wit_5.
Axiom proof_of_real_shadow_partial_solve_wit_6 : real_shadow_partial_solve_wit_6.
Axiom proof_of_real_shadow_partial_solve_wit_7 : real_shadow_partial_solve_wit_7.
Axiom proof_of_real_shadow_partial_solve_wit_8 : real_shadow_partial_solve_wit_8.
Axiom proof_of_real_shadow_partial_solve_wit_9 : real_shadow_partial_solve_wit_9.
Axiom proof_of_real_shadow_partial_solve_wit_10 : real_shadow_partial_solve_wit_10.
Axiom proof_of_real_shadow_partial_solve_wit_11 : real_shadow_partial_solve_wit_11.
Axiom proof_of_real_shadow_partial_solve_wit_12 : real_shadow_partial_solve_wit_12.
Axiom proof_of_real_shadow_partial_solve_wit_13 : real_shadow_partial_solve_wit_13.

End VC_Correct.
