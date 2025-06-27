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
Require Import kmp_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.
Require Import safeexecE_strategy_goal.
Require Import safeexecE_strategy_proof.

(*----- Function inner -----*)

Definition inner_safety_wit_1 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition inner_safety_wit_2 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) = ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition inner_safety_wit_3 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) = ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition inner_safety_wit_4 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition inner_safety_wit_5 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| (j = 0) |] 
  &&  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition inner_safety_wit_6 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition inner_safety_wit_7 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition inner_entail_wit_1 := 
forall (j_pre: Z) (ch_pre: Z) (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) ,
  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch_pre) (j_pre)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch_pre) (j_pre)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
.

Definition inner_entail_wit_2 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
.

Definition inner_entail_wit_3 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_int_array vnext_pre m vnext0 )
  **  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
|--
  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) ((Znth (j - 1 ) vnext0 0))) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
.

Definition inner_return_wit_1 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) = ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (safeExec ATrue (return ((j + 1 ))) X ) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) < (m + 1 )) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
.

Definition inner_return_wit_2 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| (j = 0) |] 
  &&  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (safeExec ATrue (return (0)) X ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < (m + 1 )) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
.

Definition inner_partial_solve_wit_1 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (((str_pre + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (app (str0) ((cons (0) (nil)))) 0))
  **  (store_char_array_missing_i_rec str_pre j 0 (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
.

Definition inner_partial_solve_wit_2 := 
forall (vnext_pre: Z) (str_pre: Z) (X: (Z -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) (ch: Z) (j: Z) ,
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
|--
  [| (j <> 0) |] 
  &&  [| ((Znth j (app (str0) ((cons (0) (nil)))) 0) <> ch) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (inner_loop (0) (str0) (vnext0) (ch) (j)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (((vnext_pre + ((j - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j - 1 ) vnext0 0))
  **  (store_int_array_missing_i_rec vnext_pre (j - 1 ) 0 m vnext0 )
  **  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
.

(*----- Function constr -----*)

Definition constr_safety_wit_1 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (retval_2: Z) (l: (@list Z)) (retval: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_int_array retval retval_2 l )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval)
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval_2)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition constr_safety_wit_2 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (retval_2: Z) (l: (@list Z)) (retval: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_int_array retval retval_2 l )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval)
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval_2)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition constr_safety_wit_3 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  (store_int_array retval_2 retval (replace_Znth (0) (0) (l)) )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition constr_safety_wit_4 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  (store_int_array retval_2 retval (replace_Znth (0) (0) (l)) )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition constr_safety_wit_5 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (vnext0: (@list Z)) (l0: (@list Z)) (i: Z) (vnext: Z) (retval: Z) (a: Z) (l1: (@list Z)) ,
  [| (l0 = (cons (a) (l1))) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str) (i) (vnext0))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (((vnext + (i * sizeof(INT) ) )) # Int  |-> retval)
  **  (store_int_array (vnext + ((i + 1 ) * sizeof(INT) ) ) (n - (i + 1 ) ) l1 )
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext i vnext0 )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition constr_entail_wit_1 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (retval_2: Z) (l: (@list Z)) (retval: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_int_array retval retval_2 (replace_Znth (0) (0) (l)) )
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval_2)
|--
  EX (l0: (@list Z))  (vnext0: (@list Z)) ,
  [| (safeExec ATrue (constr_loop_from (0) (str) (1) (vnext0) (0)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= 1) |]
  &&  ((( &( "len" ) )) # Int  |-> n)
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array retval 1 vnext0 )
  **  (store_int_array (retval + (1 * sizeof(INT) ) ) (n - 1 ) l0 )
.

Definition constr_entail_wit_2 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (vnext0_2: (@list Z)) (l0_2: (@list Z)) (i: Z) (vnext: Z) (retval: Z) (a: Z) (l1: (@list Z)) ,
  [| (l0_2 = (cons (a) (l1))) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str) (i) (vnext0_2))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (((vnext + (i * sizeof(INT) ) )) # Int  |-> retval)
  **  (store_int_array (vnext + ((i + 1 ) * sizeof(INT) ) ) (n - (i + 1 ) ) l1 )
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext i vnext0_2 )
|--
  EX (l0: (@list Z))  (vnext0: (@list Z)) ,
  [| (safeExec ATrue (constr_loop_from (0) (str) ((i + 1 )) (vnext0) (retval)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= (i + 1 )) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext (i + 1 ) vnext0 )
  **  (store_int_array (vnext + ((i + 1 ) * sizeof(INT) ) ) (n - (i + 1 ) ) l0 )
.

Definition constr_return_wit_1 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (vnext0: (@list Z)) (l0: (@list Z)) (j: Z) (i: Z) (vnext_2: Z) ,
  [| (i >= n) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str) (i) (vnext0) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext_2 i vnext0 )
  **  (store_int_array (vnext_2 + (i * sizeof(INT) ) ) (n - i ) l0 )
|--
  EX (vnext: (@list Z)) ,
  [| (safeExec ATrue (return (vnext)) X ) |]
  &&  (store_int_array vnext_2 n vnext )
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
.

Definition constr_partial_solve_wit_1 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) ,
  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
|--
  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
.

Definition constr_partial_solve_wit_2_pure := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (retval: Z) ,
  [| (retval = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  ((( &( "vnext" ) )) # Ptr  |->_)
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  [| (retval > 0) |]
.

Definition constr_partial_solve_wit_2_aux := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (retval: Z) ,
  [| (retval = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
|--
  [| (retval > 0) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
.

Definition constr_partial_solve_wit_2 := constr_partial_solve_wit_2_pure -> constr_partial_solve_wit_2_aux.

Definition constr_partial_solve_wit_3 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_int_array retval_2 retval l )
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (safeExec ATrue (constr_loop (0) (str)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 0 0 retval l )
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
.

Definition constr_partial_solve_wit_4 := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (vnext0: (@list Z)) (l0: (@list Z)) (j: Z) (i: Z) (vnext: Z) ,
  [| (i < n) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str) (i) (vnext0) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext i vnext0 )
  **  (store_int_array (vnext + (i * sizeof(INT) ) ) (n - i ) l0 )
|--
  [| (i < n) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str) (i) (vnext0) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (((patn_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (str) ((cons (0) (nil)))) 0))
  **  (store_char_array_missing_i_rec patn_pre i 0 (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext i vnext0 )
  **  (store_int_array (vnext + (i * sizeof(INT) ) ) (n - i ) l0 )
.

Definition constr_partial_solve_wit_5_pure := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (vnext0: (@list Z)) (l0: (@list Z)) (j: Z) (i: Z) (vnext: Z) ,
  [| (i < n) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str) (i) (vnext0) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  (store_int_array vnext i vnext0 )
  **  (store_int_array (vnext + (i * sizeof(INT) ) ) (n - i ) l0 )
|--
  [| (safeExec ATrue (bind ((inner_loop (0) (str) (vnext0) ((Znth i (app (str) ((cons (0) (nil)))) 0)) (j))) ((constr_loop_from_after (0) (str) (i) (vnext0)))) X ) |] 
  &&  [| (i <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (equiv (constr_loop_from (0) (str) (i) (vnext0) (j)) (bind ((inner_loop (0) (str) (vnext0) ((Znth i (app (str) ((cons (0) (nil)))) 0)) (j))) ((constr_loop_from_after (0) (str) (i) (vnext0)))) ) |]
.

Definition constr_partial_solve_wit_5_aux := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (vnext0: (@list Z)) (l0: (@list Z)) (j: Z) (i: Z) (vnext: Z) ,
  [| (i < n) |] 
  &&  [| (safeExec ATrue (constr_loop_from (0) (str) (i) (vnext0) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext i vnext0 )
  **  (store_int_array (vnext + (i * sizeof(INT) ) ) (n - i ) l0 )
|--
  [| (safeExec ATrue (bind ((inner_loop (0) (str) (vnext0) ((Znth i (app (str) ((cons (0) (nil)))) 0)) (j))) ((constr_loop_from_after (0) (str) (i) (vnext0)))) X ) |] 
  &&  [| (i <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (equiv (constr_loop_from (0) (str) (i) (vnext0) (j)) (bind ((inner_loop (0) (str) (vnext0) ((Znth i (app (str) ((cons (0) (nil)))) 0)) (j))) ((constr_loop_from_after (0) (str) (i) (vnext0)))) ) |] 
  &&  [| (i < n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext i vnext0 )
  **  (store_int_array (vnext + (i * sizeof(INT) ) ) (n - i ) l0 )
.

Definition constr_partial_solve_wit_5 := constr_partial_solve_wit_5_pure -> constr_partial_solve_wit_5_aux.

Definition constr_partial_solve_wit_6_pure := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (vnext0: (@list Z)) (l0: (@list Z)) (i: Z) (vnext: Z) (retval: Z) ,
  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str) (i) (vnext0))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext i vnext0 )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  (store_int_array (vnext + (i * sizeof(INT) ) ) (n - i ) l0 )
|--
  [| (i < n) |]
.

Definition constr_partial_solve_wit_6_aux := 
forall (patn_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (n: Z) (str: (@list Z)) (vnext0: (@list Z)) (l0: (@list Z)) (i: Z) (vnext: Z) (retval: Z) ,
  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str) (i) (vnext0))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext i vnext0 )
  **  (store_int_array (vnext + (i * sizeof(INT) ) ) (n - i ) l0 )
|--
  [| (i < n) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (applyf ((constr_loop_from_after (0) (str) (i) (vnext0))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (i + 1 )) |] 
  &&  [| (i < n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (1 <= i) |]
  &&  (store_int_array (vnext + (i * sizeof(INT) ) ) (n - i ) l0 )
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
  **  (store_int_array vnext i vnext0 )
.

Definition constr_partial_solve_wit_6 := constr_partial_solve_wit_6_pure -> constr_partial_solve_wit_6_aux.

Definition constr_which_implies_wit_1 := 
forall (n: Z) (l0: (@list Z)) (i: Z) (vnext: Z) ,
  [| (i < n) |]
  &&  (store_int_array (vnext + (i * sizeof(INT) ) ) (n - i ) l0 )
|--
  EX (a: Z)  (l1: (@list Z)) ,
  [| (l0 = (cons (a) (l1))) |]
  &&  (((vnext + (i * sizeof(INT) ) )) # Int  |-> a)
  **  (store_int_array (vnext + ((i + 1 ) * sizeof(INT) ) ) (n - (i + 1 ) ) l1 )
.

(*----- Function match -----*)

Definition match_safety_wit_1 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) ,
  [| (safeExec ATrue (match_loop (0) (patn0) (text0) (vnext0)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_safety_wit_2 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0) (text0) (vnext0)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  ((( &( "patn_len" ) )) # Int  |-> retval)
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  ((( &( "text_len" ) )) # Int  |-> retval_2)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_safety_wit_3 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval_2: Z) (retval_3: Z) (i: Z) (retval: Z) ,
  [| (retval = n) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (n + 1 )) |] 
  &&  [| (i < m) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_3 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m)
  **  ((( &( "patn_len" ) )) # Int  |-> n)
|--
  [| (((i - n ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((i - n ) + 1 )) |]
.

Definition match_safety_wit_4 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval_2: Z) (retval_3: Z) (i: Z) (retval: Z) ,
  [| (retval = n) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (n + 1 )) |] 
  &&  [| (i < m) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_3 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m)
  **  ((( &( "patn_len" ) )) # Int  |-> n)
|--
  [| ((i - n ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - n )) |]
.

Definition match_safety_wit_5 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval_2: Z) (retval_3: Z) (i: Z) (retval: Z) ,
  [| (retval = n) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (n + 1 )) |] 
  &&  [| (i < m) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_3 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m)
  **  ((( &( "patn_len" ) )) # Int  |-> n)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_safety_wit_6 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval_2: Z) (retval_3: Z) (i: Z) (retval: Z) ,
  [| (retval <> n) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (n + 1 )) |] 
  &&  [| (i < m) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_3 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m)
  **  ((( &( "patn_len" ) )) # Int  |-> n)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_safety_wit_7 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i >= m) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0) (text0) (vnext0) (i) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m)
  **  ((( &( "patn_len" ) )) # Int  |-> n)
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition match_safety_wit_8 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i >= m) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0) (text0) (vnext0) (i) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m)
  **  ((( &( "patn_len" ) )) # Int  |-> n)
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_entail_wit_1 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0) (text0) (vnext0)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  ((( &( "patn_len" ) )) # Int  |-> retval_2)
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  ((( &( "text_len" ) )) # Int  |-> retval)
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (safeExec ATrue (match_loop_from (0) (patn0) (text0) (vnext0) (0) (0)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (0 >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  ((( &( "text_len" ) )) # Int  |-> m)
  **  ((( &( "patn_len" ) )) # Int  |-> n)
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
.

Definition match_entail_wit_2 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) ,
  [| (retval_3 <> n) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i))) (retval_3)) X ) |] 
  &&  [| (0 <= retval_3) |] 
  &&  [| (retval_3 < (n + 1 )) |] 
  &&  [| (i < m) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
|--
  [| (safeExec ATrue (match_loop_from (0) (patn0) (text0) (vnext0) ((i + 1 )) (retval_3)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((i + 1 ) >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
.

Definition match_return_wit_1 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval_2: Z) (retval_3: Z) (i: Z) (retval: Z) ,
  [| (retval = n) |] 
  &&  [| (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i))) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (n + 1 )) |] 
  &&  [| (i < m) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_3 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
|--
  EX (ret: (@option Z)) ,
  [| (safeExec ATrue (return (ret)) X ) |] 
  &&  [| (((i - n ) + 1 ) = (option_int_repr (ret))) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
.

Definition match_return_wit_2 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i >= m) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0) (text0) (vnext0) (i) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
  EX (ret: (@option Z)) ,
  [| (safeExec ATrue (return (ret)) X ) |] 
  &&  [| ((-1) = (option_int_repr (ret))) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
.

Definition match_partial_solve_wit_1 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) ,
  [| (safeExec ATrue (match_loop (0) (patn0) (text0) (vnext0)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0) (text0) (vnext0)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
.

Definition match_partial_solve_wit_2 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval: Z) ,
  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0) (text0) (vnext0)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (safeExec ATrue (match_loop (0) (patn0) (text0) (vnext0)) X ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
.

Definition match_partial_solve_wit_3 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i < m) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0) (text0) (vnext0) (i) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (i < m) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0) (text0) (vnext0) (i) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (((text_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (text0) ((cons (0) (nil)))) 0))
  **  (store_char_array_missing_i_rec text_pre i 0 (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
.

Definition match_partial_solve_wit_4_pure := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i < m) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0) (text0) (vnext0) (i) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m)
  **  ((( &( "patn_len" ) )) # Int  |-> n)
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (safeExec ATrue (bind ((inner_loop (0) (patn0) (vnext0) ((Znth i (app (text0) ((cons (0) (nil)))) 0)) (j))) ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i)))) X ) |] 
  &&  [| (n <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (equiv (match_loop_from (0) (patn0) (text0) (vnext0) (i) (j)) (bind ((inner_loop (0) (patn0) (vnext0) ((Znth i (app (text0) ((cons (0) (nil)))) 0)) (j))) ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i)))) ) |]
.

Definition match_partial_solve_wit_4_aux := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X: ((@option Z) -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) ,
  [| (i < m) |] 
  &&  [| (safeExec ATrue (match_loop_from (0) (patn0) (text0) (vnext0) (i) (j)) X ) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
  [| (safeExec ATrue (bind ((inner_loop (0) (patn0) (vnext0) ((Znth i (app (text0) ((cons (0) (nil)))) 0)) (j))) ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i)))) X ) |] 
  &&  [| (n <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (equiv (match_loop_from (0) (patn0) (text0) (vnext0) (i) (j)) (bind ((inner_loop (0) (patn0) (vnext0) ((Znth i (app (text0) ((cons (0) (nil)))) 0)) (j))) ((match_loop_from_after (0) (patn0) (text0) (vnext0) (i)))) ) |] 
  &&  [| (i < m) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| (i >= 0) |] 
  &&  [| (retval_2 = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (retval = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
.

Definition match_partial_solve_wit_4 := match_partial_solve_wit_4_pure -> match_partial_solve_wit_4_aux.

Definition match_derive_high_level_spec_by_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (vnext0: (@list Z)) (text0: (@list Z)) (patn0: (@list Z)) ,
  [| (is_prefix_func vnext0 patn0 ) |] 
  &&  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (m < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 )
|--
EX (patn0_2: (@list Z)) (text0_2: (@list Z)) (vnext0_2: (@list Z)) (n_2: Z) (m_2: Z) (X: ((@option Z) -> (unit -> Prop))) ,
  ([| (safeExec ATrue (match_loop (0) (patn0_2) (text0_2) (vnext0_2)) X ) |] 
  &&  [| (n_2 > 0) |] 
  &&  [| (n_2 < INT_MAX) |] 
  &&  [| (m_2 < INT_MAX) |]
  &&  (store_char_array patn_pre (n_2 + 1 ) (app (patn0_2) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m_2 + 1 ) (app (text0_2) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n_2 vnext0_2 ))
  **
  ((EX ret retval_2,
  [| (safeExec ATrue (return (ret)) X ) |] 
  &&  [| (retval_2 = (option_int_repr (ret))) |]
  &&  (store_char_array patn_pre (n_2 + 1 ) (app (patn0_2) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m_2 + 1 ) (app (text0_2) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n_2 vnext0_2 ))
  -*
  ((EX retval,
  [| (retval >= 0) |] 
  &&  [| (first_occur patn0 text0 retval ) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 ))
  ||
  (EX retval,
  [| (retval = (-1)) |] 
  &&  [| (no_occurance patn0 text0 ) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (patn0) ((cons (0) (nil)))) )
  **  (store_char_array text_pre (m + 1 ) (app (text0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre n vnext0 ))))
.

Definition constr_derive_high_level_spec_by_low_level_spec := 
forall (patn_pre: Z) (n: Z) (str: (@list Z)) ,
  [| (n > 0) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )
|--
EX (str_2: (@list Z)) (n_2: Z) (X: ((@list Z) -> (unit -> Prop))) ,
  ([| (safeExec ATrue (constr_loop (0) (str_2)) X ) |] 
  &&  [| (n_2 > 0) |] 
  &&  [| (n_2 < INT_MAX) |]
  &&  (store_char_array patn_pre (n_2 + 1 ) (app (str_2) ((cons (0) (nil)))) ))
  **
  ((EX vnext_2 retval_2,
  [| (safeExec ATrue (return (vnext_2)) X ) |]
  &&  (store_int_array retval_2 n_2 vnext_2 )
  **  (store_char_array patn_pre (n_2 + 1 ) (app (str_2) ((cons (0) (nil)))) ))
  -*
  (EX vnext retval,
  [| (is_prefix_func vnext str ) |]
  &&  (store_int_array retval n vnext )
  **  (store_char_array patn_pre (n + 1 ) (app (str) ((cons (0) (nil)))) )))
.

Definition inner_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (j_pre: Z) (ch_pre: Z) (vnext_pre: Z) (str_pre: Z) (f: (Z -> (@program unit B))) (X: (B -> (unit -> Prop))) (m: Z) (n: Z) (vnext0: (@list Z)) (str0: (@list Z)) ,
  [| (safeExec ATrue (bind ((inner_loop (0) (str0) (vnext0) (ch_pre) (j_pre))) (f)) X ) |] 
  &&  [| (m <= n) |] 
  &&  [| (n < INT_MAX) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )
|--
EX (str0_2: (@list Z)) (vnext0_2: (@list Z)) (n_2: Z) (m_2: Z) (X_2: (Z -> (unit -> Prop))) ,
  ([| (safeExec ATrue (inner_loop (0) (str0_2) (vnext0_2) (ch_pre) (j_pre)) X_2 ) |] 
  &&  [| (m_2 <= n_2) |] 
  &&  [| (n_2 < INT_MAX) |]
  &&  (store_char_array str_pre (n_2 + 1 ) (app (str0_2) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m_2 vnext0_2 ))
  **
  ((EX retval_2,
  [| (safeExec ATrue (return (retval_2)) X_2 ) |] 
  &&  [| (0 <= retval_2) |] 
  &&  [| (retval_2 < (m_2 + 1 )) |]
  &&  (store_char_array str_pre (n_2 + 1 ) (app (str0_2) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m_2 vnext0_2 ))
  -*
  (EX retval,
  [| (safeExec ATrue (applyf (f) (retval)) X ) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < (m + 1 )) |]
  &&  (store_char_array str_pre (n + 1 ) (app (str0) ((cons (0) (nil)))) )
  **  (store_int_array vnext_pre m vnext0 )))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include char_array_Strategy_Correct.
Include safeexecE_Strategy_Correct.

Axiom proof_of_inner_safety_wit_1 : inner_safety_wit_1.
Axiom proof_of_inner_safety_wit_2 : inner_safety_wit_2.
Axiom proof_of_inner_safety_wit_3 : inner_safety_wit_3.
Axiom proof_of_inner_safety_wit_4 : inner_safety_wit_4.
Axiom proof_of_inner_safety_wit_5 : inner_safety_wit_5.
Axiom proof_of_inner_safety_wit_6 : inner_safety_wit_6.
Axiom proof_of_inner_safety_wit_7 : inner_safety_wit_7.
Axiom proof_of_inner_entail_wit_1 : inner_entail_wit_1.
Axiom proof_of_inner_entail_wit_2 : inner_entail_wit_2.
Axiom proof_of_inner_entail_wit_3 : inner_entail_wit_3.
Axiom proof_of_inner_return_wit_1 : inner_return_wit_1.
Axiom proof_of_inner_return_wit_2 : inner_return_wit_2.
Axiom proof_of_inner_partial_solve_wit_1 : inner_partial_solve_wit_1.
Axiom proof_of_inner_partial_solve_wit_2 : inner_partial_solve_wit_2.
Axiom proof_of_constr_safety_wit_1 : constr_safety_wit_1.
Axiom proof_of_constr_safety_wit_2 : constr_safety_wit_2.
Axiom proof_of_constr_safety_wit_3 : constr_safety_wit_3.
Axiom proof_of_constr_safety_wit_4 : constr_safety_wit_4.
Axiom proof_of_constr_safety_wit_5 : constr_safety_wit_5.
Axiom proof_of_constr_entail_wit_1 : constr_entail_wit_1.
Axiom proof_of_constr_entail_wit_2 : constr_entail_wit_2.
Axiom proof_of_constr_return_wit_1 : constr_return_wit_1.
Axiom proof_of_constr_partial_solve_wit_1 : constr_partial_solve_wit_1.
Axiom proof_of_constr_partial_solve_wit_2_pure : constr_partial_solve_wit_2_pure.
Axiom proof_of_constr_partial_solve_wit_2 : constr_partial_solve_wit_2.
Axiom proof_of_constr_partial_solve_wit_3 : constr_partial_solve_wit_3.
Axiom proof_of_constr_partial_solve_wit_4 : constr_partial_solve_wit_4.
Axiom proof_of_constr_partial_solve_wit_5_pure : constr_partial_solve_wit_5_pure.
Axiom proof_of_constr_partial_solve_wit_5 : constr_partial_solve_wit_5.
Axiom proof_of_constr_partial_solve_wit_6_pure : constr_partial_solve_wit_6_pure.
Axiom proof_of_constr_partial_solve_wit_6 : constr_partial_solve_wit_6.
Axiom proof_of_constr_which_implies_wit_1 : constr_which_implies_wit_1.
Axiom proof_of_match_safety_wit_1 : match_safety_wit_1.
Axiom proof_of_match_safety_wit_2 : match_safety_wit_2.
Axiom proof_of_match_safety_wit_3 : match_safety_wit_3.
Axiom proof_of_match_safety_wit_4 : match_safety_wit_4.
Axiom proof_of_match_safety_wit_5 : match_safety_wit_5.
Axiom proof_of_match_safety_wit_6 : match_safety_wit_6.
Axiom proof_of_match_safety_wit_7 : match_safety_wit_7.
Axiom proof_of_match_safety_wit_8 : match_safety_wit_8.
Axiom proof_of_match_entail_wit_1 : match_entail_wit_1.
Axiom proof_of_match_entail_wit_2 : match_entail_wit_2.
Axiom proof_of_match_return_wit_1 : match_return_wit_1.
Axiom proof_of_match_return_wit_2 : match_return_wit_2.
Axiom proof_of_match_partial_solve_wit_1 : match_partial_solve_wit_1.
Axiom proof_of_match_partial_solve_wit_2 : match_partial_solve_wit_2.
Axiom proof_of_match_partial_solve_wit_3 : match_partial_solve_wit_3.
Axiom proof_of_match_partial_solve_wit_4_pure : match_partial_solve_wit_4_pure.
Axiom proof_of_match_partial_solve_wit_4 : match_partial_solve_wit_4.
Axiom proof_of_match_derive_high_level_spec_by_low_level_spec : match_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_constr_derive_high_level_spec_by_low_level_spec : constr_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_inner_derive_bind_spec_by_low_level_spec : inner_derive_bind_spec_by_low_level_spec.

End VC_Correct.
