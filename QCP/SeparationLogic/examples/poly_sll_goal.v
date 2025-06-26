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
Require Import poly_sll_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import poly_sll_strategy_goal.
From SimpleC.EE Require Import poly_sll_strategy_proof.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (A: Type) (p_pre: Z) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll storeA p_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_entail_wit_1 := 
forall (A: Type) (p_pre: Z) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) ,
  (sll storeA p_pre l )
|--
  EX l1 l2,
  [| (l = (app ((rev (l1))) (l2))) |] 
  &&  [| (sll_para storeA ) |]
  &&  (sll storeA 0 l1 )
  **  (sll storeA p_pre l2 )
.

Definition reverse_entail_wit_2 := 
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (w: Z) (l1_2: (@list A)) (l2_2: (@list A)) (v_next: Z) (v_data: Z) (x: A) (xs: (@list A)) ,
  [| (l2_2 = (cons (x) (xs))) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1_2))) (l2_2))) |] 
  &&  [| (sll_para storeA ) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Ptr  |-> v_data)
  **  (storeA v_data x )
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll storeA v_next xs )
  **  (sll storeA w l1_2 )
|--
  EX l1 l2,
  [| (l = (app ((rev (l1))) (l2))) |] 
  &&  [| (sll_para storeA ) |]
  &&  (sll storeA v l1 )
  **  (sll storeA v_next l2 )
.

Definition reverse_return_wit_1 := 
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (w: Z) (l1: (@list A)) (l2: (@list A)) ,
  [| (v = 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |] 
  &&  [| (sll_para storeA ) |]
  &&  (sll storeA w l1 )
  **  (sll storeA v l2 )
|--
  (sll storeA w (rev (l)) )
.

Definition reverse_partial_solve_wit_1_pure := 
forall (A: Type) (p_pre: Z) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (w: Z) (l1: (@list A)) (l2: (@list A)) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |] 
  &&  [| (sll_para storeA ) |]
  &&  ((( &( "w" ) )) # Ptr  |-> w)
  **  (sll storeA w l1 )
  **  ((( &( "v" ) )) # Ptr  |-> v)
  **  (sll storeA v l2 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  [| (v <> 0) |]
.

Definition reverse_partial_solve_wit_1_aux := 
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (w: Z) (l1: (@list A)) (l2: (@list A)) ,
  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |] 
  &&  [| (sll_para storeA ) |]
  &&  (sll storeA w l1 )
  **  (sll storeA v l2 )
|--
  [| (v <> 0) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l = (app ((rev (l1))) (l2))) |] 
  &&  [| (sll_para storeA ) |]
  &&  (sll storeA v l2 )
  **  (sll storeA w l1 )
.

Definition reverse_partial_solve_wit_1 := reverse_partial_solve_wit_1_pure -> reverse_partial_solve_wit_1_aux.

Definition reverse_which_implies_wit_1 := 
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (l2: (@list A)) (v: Z) ,
  [| (v <> 0) |]
  &&  (sll storeA v l2 )
|--
  EX v_next v_data x xs,
  [| (l2 = (cons (x) (xs))) |]
  &&  ((&((v)  # "list" ->ₛ "data")) # Ptr  |-> v_data)
  **  (storeA v_data x )
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> v_next)
  **  (sll storeA v_next xs )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include poly_sll_Strategy_Correct.

Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Axiom proof_of_reverse_partial_solve_wit_1_pure : reverse_partial_solve_wit_1_pure.
Axiom proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1.
Axiom proof_of_reverse_which_implies_wit_1 : reverse_which_implies_wit_1.

End VC_Correct.
