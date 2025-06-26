Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition char_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (list Z)),
    TT &&
    ([| (Z.le 0 i) |]) &&
    ([| (Z.lt i n) |]) &&
    emp **
    ((store_char_array p n l))
    |--
    (
    TT &&
    emp **
    ((store_char_array_missing_i_rec p i 0 n l))
    ) ** (
    ALL (v : Z),
      TT &&
      ([| (v = (Znth i l  0)) |]) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char (Z.add p (Z.mul i (@sizeof_front_end_type FET_char))) v))
      ).

Definition char_array_strategy4 :=
  forall (p : Z) (l1 : (list Z)) (n : Z),
    TT &&
    emp **
    ((store_char_array p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (list Z)),
      TT &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((store_char_array p n l2))
      ).

Definition char_array_strategy5 :=
  forall (p : Z) (v : Z) (l : (list Z)) (n : Z) (i : Z),
    TT &&
    emp **
    ((store_char_array_missing_i_rec p i v n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_char_array_missing_i_rec p i v n l))
    ).

Definition char_array_strategy6 :=
  forall (n : Z) (p : Z) (l1 : (list Z)),
    TT &&
    emp **
    ((store_char_array p n l1))
    |--
    (
    TT &&
    ([| (Z.le 0 n) |]) &&
    emp **
    ((store_char_array p n l1))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition char_array_strategy2 :=
  forall (i : Z) (n : Z) (l : (list Z)) (p : Z),
    TT &&
    ([| (Z.le 0 i) |]) &&
    ([| (Z.lt i n) |]) &&
    emp **
    ((store_char_array_missing_i_rec p i 0 n l)) **
    ((poly_store FET_char (Z.add p (Z.mul i (@sizeof_front_end_type FET_char))) (Znth i l  0)))
    |--
    (
    TT &&
    emp **
    ((store_char_array p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition char_array_strategy3 :=
  forall (i : Z) (n : Z) (l : (list Z)) (v : Z) (p : Z),
    TT &&
    ([| (Z.le 0 i) |]) &&
    ([| (Z.lt i n) |]) &&
    emp **
    ((store_char_array_missing_i_rec p i 0 n l)) **
    ((poly_store FET_char (Z.add p (Z.mul i (@sizeof_front_end_type FET_char))) v))
    |--
    (
    TT &&
    emp **
    ((store_char_array p n (@replace_Znth Z i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type char_array_Strategy_Correct.

  Axiom char_array_strategy1_correctness : char_array_strategy1.
  Axiom char_array_strategy4_correctness : char_array_strategy4.
  Axiom char_array_strategy5_correctness : char_array_strategy5.
  Axiom char_array_strategy6_correctness : char_array_strategy6.
  Axiom char_array_strategy2_correctness : char_array_strategy2.
  Axiom char_array_strategy3_correctness : char_array_strategy3.

End char_array_Strategy_Correct.
