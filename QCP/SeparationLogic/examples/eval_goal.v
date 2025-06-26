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
Require Import eval_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import eval_strategy_goal.
From SimpleC.EE Require Import eval_strategy_proof.

(*----- Function eval -----*)

Definition eval_safety_wit_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_3 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition eval_safety_wit_4 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) ,
  [| (2 = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (11 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 11) |]
.

Definition eval_safety_wit_5 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_6 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_7 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_8 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) ,
  [| (v_3 <> 11) |] 
  &&  [| (2 = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (12 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 12) |]
.

Definition eval_safety_wit_9 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_10 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_11 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_12 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_13 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| ((retval + retval_2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + retval_2 )) |]
.

Definition eval_safety_wit_14 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_15 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| ((retval - retval_2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval - retval_2 )) |]
.

Definition eval_safety_wit_16 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition eval_safety_wit_17 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| ((retval * retval_2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval * retval_2 )) |]
.

Definition eval_safety_wit_18 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition eval_safety_wit_19 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) |] 
  &&  [| (retval_2 <> 0) |]
.

Definition eval_safety_wit_20 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition eval_safety_wit_21 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) |] 
  &&  [| (retval_2 <> 0) |]
.

Definition eval_safety_wit_22 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition eval_safety_wit_23 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition eval_safety_wit_24 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (7 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 7) |]
.

Definition eval_safety_wit_25 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition eval_safety_wit_26 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 8) |] 
  &&  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (9 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 9) |]
.

Definition eval_safety_wit_27 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 9) |] 
  &&  [| (v_3 <> 8) |] 
  &&  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition eval_safety_wit_28 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition eval_safety_wit_29 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) ,
  [| (3 = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_30 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_2 <> 1) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (retval <> (INT_MIN)) |]
.

Definition eval_entail_wit_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (v_3 <> 10) |] 
  &&  [| (v_3 <> 9) |] 
  &&  [| (v_3 <> 8) |] 
  &&  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval_2)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| False |]
  &&  emp
.

Definition eval_entail_wit_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t <> 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| False |]
  &&  emp
.

Definition eval_return_wit_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) ,
  [| (0 = 0) |] 
  &&  [| (e0 = (EConst (n))) |] 
  &&  [| (e_t = 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 0)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (n = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) ,
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (e0 = (EVar (n))) |] 
  &&  [| (e_t = 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  [| ((Znth n l 0) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_3 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_4 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_5 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_6 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_7 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_8 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_9 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| ((retval + retval_2 ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_10 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| ((retval - retval_2 ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_11 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| ((retval * retval_2 ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_12 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| ((retval ÷ retval_2 ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_13 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) ,
  [| (v_3 = 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| ((retval % ( retval_2 ) ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_14_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 >= retval) |] 
  &&  [| (v_3 = 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_14_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 < retval) |] 
  &&  [| (v_3 = 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_15_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 <= retval) |] 
  &&  [| (v_3 = 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_15_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 > retval) |] 
  &&  [| (v_3 = 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_16_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 > retval) |] 
  &&  [| (v_3 = 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_16_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 <= retval) |] 
  &&  [| (v_3 = 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_17_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 < retval) |] 
  &&  [| (v_3 = 8) |] 
  &&  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_17_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 >= retval) |] 
  &&  [| (v_3 = 8) |] 
  &&  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_18_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 <> retval) |] 
  &&  [| (v_3 = 9) |] 
  &&  [| (v_3 <> 8) |] 
  &&  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_18_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 = retval) |] 
  &&  [| (v_3 = 9) |] 
  &&  [| (v_3 <> 8) |] 
  &&  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_19_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 = retval) |] 
  &&  [| (v_3 = 10) |] 
  &&  [| (v_3 <> 9) |] 
  &&  [| (v_3 <> 8) |] 
  &&  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_19_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval_2: Z) (retval: Z) ,
  [| (retval_2 <> retval) |] 
  &&  [| (v_3 = 10) |] 
  &&  [| (v_3 <> 9) |] 
  &&  [| (v_3 <> 8) |] 
  &&  [| (v_3 <> 7) |] 
  &&  [| (v_3 <> 6) |] 
  &&  [| (v_3 <> 5) |] 
  &&  [| (v_3 <> 4) |] 
  &&  [| (v_3 <> 3) |] 
  &&  [| (v_3 <> 2) |] 
  &&  [| (v_3 <> 1) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (retval = (expr_eval (e2) (l))) |] 
  &&  [| (retval_2 = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_20_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_2 = 1) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_20_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_2 = 1) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_return_wit_21 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_2 <> 1) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  [| ((-retval) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_partial_solve_wit_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) ,
  [| (safe_eval e0 l ) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e0 l ) |]
  &&  (store_expr e_pre e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_partial_solve_wit_2_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t = 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (0 = 0) |]
.

Definition eval_partial_solve_wit_2_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t = 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (0 = 0) |] 
  &&  [| (e_t = 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 0)
  **  (store_expr_aux e_pre 0 e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_partial_solve_wit_2 := eval_partial_solve_wit_2_pure -> eval_partial_solve_wit_2_aux.

Definition eval_partial_solve_wit_3_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t = 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (1 = 1) |] 
  &&  [| (safe_eval e0 l ) |]
.

Definition eval_partial_solve_wit_3_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t = 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (1 = 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  (store_expr_aux e_pre 1 e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_partial_solve_wit_3 := eval_partial_solve_wit_3_pure -> eval_partial_solve_wit_3_aux.

Definition eval_partial_solve_wit_4 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) ,
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (1 = 1) |] 
  &&  [| (e0 = (EVar (n))) |] 
  &&  [| (e_t = 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (e0 = (EVar (n))) |] 
  &&  [| (e_t = 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (((var_value_pre + (n * sizeof(INT) ) )) # Int  |-> (Znth n l 0))
  **  (store_int_array_missing_i_rec var_value_pre n 0 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition eval_partial_solve_wit_5_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (2 = 2) |]
.

Definition eval_partial_solve_wit_5_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (2 = 2) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  (store_expr_aux e_pre 2 e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_partial_solve_wit_5 := eval_partial_solve_wit_5_pure -> eval_partial_solve_wit_5_aux.

Definition eval_partial_solve_wit_6_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) ,
  [| (v_3 = 11) |] 
  &&  [| (2 = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_6_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) ,
  [| (v_3 = 11) |] 
  &&  [| (2 = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
.

Definition eval_partial_solve_wit_6 := eval_partial_solve_wit_6_pure -> eval_partial_solve_wit_6_aux.

Definition eval_partial_solve_wit_7_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (safe_eval e2 l ) |]
.

Definition eval_partial_solve_wit_7_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  [| (safe_eval e2 l ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_7 := eval_partial_solve_wit_7_pure -> eval_partial_solve_wit_7_aux.

Definition eval_partial_solve_wit_8_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) ,
  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (2 = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_8_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) ,
  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (2 = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
.

Definition eval_partial_solve_wit_8 := eval_partial_solve_wit_8_pure -> eval_partial_solve_wit_8_aux.

Definition eval_partial_solve_wit_9_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (safe_eval e2 l ) |]
.

Definition eval_partial_solve_wit_9_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  [| (safe_eval e2 l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 = 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_9 := eval_partial_solve_wit_9_pure -> eval_partial_solve_wit_9_aux.

Definition eval_partial_solve_wit_10_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) ,
  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (2 = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "left_val" ) )) # Int  |->_)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_10_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) ,
  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (2 = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
.

Definition eval_partial_solve_wit_10 := eval_partial_solve_wit_10_pure -> eval_partial_solve_wit_10_aux.

Definition eval_partial_solve_wit_11_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "right_val" ) )) # Int  |->_)
  **  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  [| (safe_eval e2 l ) |]
.

Definition eval_partial_solve_wit_11_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v_2 e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  [| (safe_eval e2 l ) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v_3 <> 12) |] 
  &&  [| (v_3 <> 11) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e2 )
  **  (store_int_array var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_11 := eval_partial_solve_wit_11_pure -> eval_partial_solve_wit_11_aux.

Definition eval_partial_solve_wit_12_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (3 = 3) |]
.

Definition eval_partial_solve_wit_12_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) ,
  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (3 = 3) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  (store_expr_aux e_pre 3 e0 )
  **  (store_int_array var_value_pre 100 l )
.

Definition eval_partial_solve_wit_12 := eval_partial_solve_wit_12_pure -> eval_partial_solve_wit_12_aux.

Definition eval_partial_solve_wit_13_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) ,
  [| (v_2 = 1) |] 
  &&  [| (3 = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_13_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) ,
  [| (v_2 = 1) |] 
  &&  [| (3 = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v_2 = 1) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_13 := eval_partial_solve_wit_13_pure -> eval_partial_solve_wit_13_aux.

Definition eval_partial_solve_wit_14_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) ,
  [| (v_2 <> 1) |] 
  &&  [| (3 = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_14_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) ,
  [| (v_2 <> 1) |] 
  &&  [| (3 = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  (store_int_array var_value_pre 100 l )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v_2 <> 1) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e_t <> 2) |] 
  &&  [| (e_t <> 1) |] 
  &&  [| (e_t <> 0) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  (store_expr v e1 )
  **  (store_int_array var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_14 := eval_partial_solve_wit_14_pure -> eval_partial_solve_wit_14_aux.

Definition eval_which_implies_wit_1 := 
forall (e0: expr) (e: Z) ,
  (store_expr e e0 )
|--
  EX e_t,
  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
.

Definition eval_which_implies_wit_2 := 
forall (e0: expr) (e: Z) (e_t: Z) ,
  [| (e_t = 0) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  EX n,
  [| (e_t = 0) |] 
  &&  [| (e0 = (EConst (n))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
.

Definition eval_which_implies_wit_3 := 
forall (l: (@list Z)) (e0: expr) (e: Z) (e_t: Z) (var_value: Z) ,
  [| (e_t = 1) |] 
  &&  [| (safe_eval e0 l ) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
  **  (store_int_array var_value 100 l )
|--
  EX n,
  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (e_t = 1) |] 
  &&  [| (e0 = (EVar (n))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_int_array var_value 100 l )
.

Definition eval_which_implies_wit_4 := 
forall (e0: expr) (e: Z) (e_t: Z) ,
  [| (e_t = 2) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  EX v v_2 v_3 op e1 e2,
  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v_3 = (BinOpID (op))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
.

Definition eval_which_implies_wit_5 := 
forall (e0: expr) (e: Z) (e_t: Z) ,
  [| (e_t = 3) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  EX v v_2 op e1,
  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v_2 = (UnOpID (op))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include eval_Strategy_Correct.

Axiom proof_of_eval_safety_wit_1 : eval_safety_wit_1.
Axiom proof_of_eval_safety_wit_2 : eval_safety_wit_2.
Axiom proof_of_eval_safety_wit_3 : eval_safety_wit_3.
Axiom proof_of_eval_safety_wit_4 : eval_safety_wit_4.
Axiom proof_of_eval_safety_wit_5 : eval_safety_wit_5.
Axiom proof_of_eval_safety_wit_6 : eval_safety_wit_6.
Axiom proof_of_eval_safety_wit_7 : eval_safety_wit_7.
Axiom proof_of_eval_safety_wit_8 : eval_safety_wit_8.
Axiom proof_of_eval_safety_wit_9 : eval_safety_wit_9.
Axiom proof_of_eval_safety_wit_10 : eval_safety_wit_10.
Axiom proof_of_eval_safety_wit_11 : eval_safety_wit_11.
Axiom proof_of_eval_safety_wit_12 : eval_safety_wit_12.
Axiom proof_of_eval_safety_wit_13 : eval_safety_wit_13.
Axiom proof_of_eval_safety_wit_14 : eval_safety_wit_14.
Axiom proof_of_eval_safety_wit_15 : eval_safety_wit_15.
Axiom proof_of_eval_safety_wit_16 : eval_safety_wit_16.
Axiom proof_of_eval_safety_wit_17 : eval_safety_wit_17.
Axiom proof_of_eval_safety_wit_18 : eval_safety_wit_18.
Axiom proof_of_eval_safety_wit_19 : eval_safety_wit_19.
Axiom proof_of_eval_safety_wit_20 : eval_safety_wit_20.
Axiom proof_of_eval_safety_wit_21 : eval_safety_wit_21.
Axiom proof_of_eval_safety_wit_22 : eval_safety_wit_22.
Axiom proof_of_eval_safety_wit_23 : eval_safety_wit_23.
Axiom proof_of_eval_safety_wit_24 : eval_safety_wit_24.
Axiom proof_of_eval_safety_wit_25 : eval_safety_wit_25.
Axiom proof_of_eval_safety_wit_26 : eval_safety_wit_26.
Axiom proof_of_eval_safety_wit_27 : eval_safety_wit_27.
Axiom proof_of_eval_safety_wit_28 : eval_safety_wit_28.
Axiom proof_of_eval_safety_wit_29 : eval_safety_wit_29.
Axiom proof_of_eval_safety_wit_30 : eval_safety_wit_30.
Axiom proof_of_eval_entail_wit_1 : eval_entail_wit_1.
Axiom proof_of_eval_entail_wit_2 : eval_entail_wit_2.
Axiom proof_of_eval_return_wit_1 : eval_return_wit_1.
Axiom proof_of_eval_return_wit_2 : eval_return_wit_2.
Axiom proof_of_eval_return_wit_3 : eval_return_wit_3.
Axiom proof_of_eval_return_wit_4 : eval_return_wit_4.
Axiom proof_of_eval_return_wit_5 : eval_return_wit_5.
Axiom proof_of_eval_return_wit_6 : eval_return_wit_6.
Axiom proof_of_eval_return_wit_7 : eval_return_wit_7.
Axiom proof_of_eval_return_wit_8 : eval_return_wit_8.
Axiom proof_of_eval_return_wit_9 : eval_return_wit_9.
Axiom proof_of_eval_return_wit_10 : eval_return_wit_10.
Axiom proof_of_eval_return_wit_11 : eval_return_wit_11.
Axiom proof_of_eval_return_wit_12 : eval_return_wit_12.
Axiom proof_of_eval_return_wit_13 : eval_return_wit_13.
Axiom proof_of_eval_return_wit_14_1 : eval_return_wit_14_1.
Axiom proof_of_eval_return_wit_14_2 : eval_return_wit_14_2.
Axiom proof_of_eval_return_wit_15_1 : eval_return_wit_15_1.
Axiom proof_of_eval_return_wit_15_2 : eval_return_wit_15_2.
Axiom proof_of_eval_return_wit_16_1 : eval_return_wit_16_1.
Axiom proof_of_eval_return_wit_16_2 : eval_return_wit_16_2.
Axiom proof_of_eval_return_wit_17_1 : eval_return_wit_17_1.
Axiom proof_of_eval_return_wit_17_2 : eval_return_wit_17_2.
Axiom proof_of_eval_return_wit_18_1 : eval_return_wit_18_1.
Axiom proof_of_eval_return_wit_18_2 : eval_return_wit_18_2.
Axiom proof_of_eval_return_wit_19_1 : eval_return_wit_19_1.
Axiom proof_of_eval_return_wit_19_2 : eval_return_wit_19_2.
Axiom proof_of_eval_return_wit_20_1 : eval_return_wit_20_1.
Axiom proof_of_eval_return_wit_20_2 : eval_return_wit_20_2.
Axiom proof_of_eval_return_wit_21 : eval_return_wit_21.
Axiom proof_of_eval_partial_solve_wit_1 : eval_partial_solve_wit_1.
Axiom proof_of_eval_partial_solve_wit_2_pure : eval_partial_solve_wit_2_pure.
Axiom proof_of_eval_partial_solve_wit_2 : eval_partial_solve_wit_2.
Axiom proof_of_eval_partial_solve_wit_3_pure : eval_partial_solve_wit_3_pure.
Axiom proof_of_eval_partial_solve_wit_3 : eval_partial_solve_wit_3.
Axiom proof_of_eval_partial_solve_wit_4 : eval_partial_solve_wit_4.
Axiom proof_of_eval_partial_solve_wit_5_pure : eval_partial_solve_wit_5_pure.
Axiom proof_of_eval_partial_solve_wit_5 : eval_partial_solve_wit_5.
Axiom proof_of_eval_partial_solve_wit_6_pure : eval_partial_solve_wit_6_pure.
Axiom proof_of_eval_partial_solve_wit_6 : eval_partial_solve_wit_6.
Axiom proof_of_eval_partial_solve_wit_7_pure : eval_partial_solve_wit_7_pure.
Axiom proof_of_eval_partial_solve_wit_7 : eval_partial_solve_wit_7.
Axiom proof_of_eval_partial_solve_wit_8_pure : eval_partial_solve_wit_8_pure.
Axiom proof_of_eval_partial_solve_wit_8 : eval_partial_solve_wit_8.
Axiom proof_of_eval_partial_solve_wit_9_pure : eval_partial_solve_wit_9_pure.
Axiom proof_of_eval_partial_solve_wit_9 : eval_partial_solve_wit_9.
Axiom proof_of_eval_partial_solve_wit_10_pure : eval_partial_solve_wit_10_pure.
Axiom proof_of_eval_partial_solve_wit_10 : eval_partial_solve_wit_10.
Axiom proof_of_eval_partial_solve_wit_11_pure : eval_partial_solve_wit_11_pure.
Axiom proof_of_eval_partial_solve_wit_11 : eval_partial_solve_wit_11.
Axiom proof_of_eval_partial_solve_wit_12_pure : eval_partial_solve_wit_12_pure.
Axiom proof_of_eval_partial_solve_wit_12 : eval_partial_solve_wit_12.
Axiom proof_of_eval_partial_solve_wit_13_pure : eval_partial_solve_wit_13_pure.
Axiom proof_of_eval_partial_solve_wit_13 : eval_partial_solve_wit_13.
Axiom proof_of_eval_partial_solve_wit_14_pure : eval_partial_solve_wit_14_pure.
Axiom proof_of_eval_partial_solve_wit_14 : eval_partial_solve_wit_14.
Axiom proof_of_eval_which_implies_wit_1 : eval_which_implies_wit_1.
Axiom proof_of_eval_which_implies_wit_2 : eval_which_implies_wit_2.
Axiom proof_of_eval_which_implies_wit_3 : eval_which_implies_wit_3.
Axiom proof_of_eval_which_implies_wit_4 : eval_which_implies_wit_4.
Axiom proof_of_eval_which_implies_wit_5 : eval_which_implies_wit_5.

End VC_Correct.
