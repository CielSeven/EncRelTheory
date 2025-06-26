Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import dll_shape_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition dll_shape_strategy1 :=
  forall (x : Z),
    TT &&
    emp **
    ((dlistrep 0 x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition dll_shape_strategy2 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x : Z),
    TT &&
    emp -*
    TT &&
    emp **
    ((dlistrep 0 x))
    ).

Definition dll_shape_strategy3 :=
  forall (p : Z),
    TT &&
    ([| (p = 0) |] || [| (0 = p) |]) &&
    emp
    |--
    (
    TT &&
    ([| (p = 0) |] || [| (0 = p) |]) &&
    emp
    ) ** (
    ALL (x : Z),
      TT &&
      emp -*
      TT &&
      emp **
      ((dlistrep p x))
      ).

Definition dll_shape_strategy4 :=
  forall (p : Z) (x : Z),
    TT &&
    ([| (p = 0) |] || [| (0 = p) |]) &&
    emp **
    ((dlistrep p x))
    |--
    (
    TT &&
    ([| (p = 0) |] || [| (0 = p) |]) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition dll_shape_strategy7 :=
  forall (q : Z) (x : Z) (p : Z) (r : Z) (s : Z),
    TT &&
    ([| (q = x) |]) &&
    emp **
    ((dllseg p q r s))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp **
    ((dlistrep s r)) -*
    TT &&
    emp **
    ((dlistrep p x))
    ).

Definition dll_shape_strategy9 :=
  forall (x : Z) (q : Z) (r : Z) (s : Z) (p : Z),
    TT &&
    ([| (x = q) |]) &&
    emp **
    ((dlistrep p x))
    |--
    (
    TT &&
    emp **
    ((dllseg p r s q))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((dllseg p q r s))
    ).

Definition dll_shape_strategy8 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    ([| (x = y) |]) &&
    emp **
    ((dlistrep p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((dlistrep p y))
    ).

Definition dll_shape_strategy10 :=
  forall (p : Z) (s : Z) (r : Z) (q : Z),
    TT &&
    ([| (q = r) |]) &&
    ([| (p = s) |]) &&
    emp **
    ((dllseg p q r s))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition dll_shape_strategy11 :=
  forall (p : Z) (s : Z) (r : Z) (q : Z),
    TT &&
    ([| (q = r) |]) &&
    ([| (p = s) |]) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((dllseg p q r s))
    ).

Definition dll_shape_strategy5 :=
  forall (p : Z) (prev : Z),
    TT &&
    ([| (p <> 0) |] || [| (0 <> p) |]) &&
    emp **
    ((dlistrep p prev))
    |--
    EX (x : Z) (y : Z),
      (
      TT &&
      ([| (p <> 0) |] || [| (0 <> p) |]) &&
      emp **
      ((poly_store FET_int &( ((p)) # "dlist" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "dlist" ->ₛ "next") y)) **
      ((poly_store FET_ptr &( ((p)) # "dlist" ->ₛ "prev") prev)) **
      ((dlistrep y p))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "dlist" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "dlist" ->ₛ "next") q) || (poly_store FET_ptr &( ((p)) # "dlist" ->ₛ "prev") q)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "dlist" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "dlist" ->ₛ "next") q) || (poly_store FET_ptr &( ((p)) # "dlist" ->ₛ "prev") q))
        ).

Definition dll_shape_strategy6 :=
  forall (p : Z),
    TT &&
    ([| (p <> 0) |] || [| (0 <> p) |]) &&
    emp
    |--
    (
    TT &&
    ([| (p <> 0) |] || [| (0 <> p) |]) &&
    emp
    ) ** (
    ALL (prev : Z) (x : Z) (y : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "dlist" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "dlist" ->ₛ "next") y)) **
      ((poly_store FET_ptr &( ((p)) # "dlist" ->ₛ "prev") prev)) **
      ((dlistrep y p)) -*
      TT &&
      emp **
      ((dlistrep p prev))
      ).

Module Type dll_shape_Strategy_Correct.

  Axiom dll_shape_strategy1_correctness : dll_shape_strategy1.
  Axiom dll_shape_strategy2_correctness : dll_shape_strategy2.
  Axiom dll_shape_strategy3_correctness : dll_shape_strategy3.
  Axiom dll_shape_strategy4_correctness : dll_shape_strategy4.
  Axiom dll_shape_strategy7_correctness : dll_shape_strategy7.
  Axiom dll_shape_strategy9_correctness : dll_shape_strategy9.
  Axiom dll_shape_strategy8_correctness : dll_shape_strategy8.
  Axiom dll_shape_strategy10_correctness : dll_shape_strategy10.
  Axiom dll_shape_strategy11_correctness : dll_shape_strategy11.
  Axiom dll_shape_strategy5_correctness : dll_shape_strategy5.
  Axiom dll_shape_strategy6_correctness : dll_shape_strategy6.

End dll_shape_Strategy_Correct.
