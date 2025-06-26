Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Nat.
Require Import Permutation.
Require Import String.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Local Open Scope Z_scope.
Import ListNotations.
Local Open Scope list.
Local Open Scope sets.
Local Open Scope string.

Import naive_C_Rules.
Require Import algorithm.
Local Open Scope sac.

Notation "'Zto_nat'" := (Z.to_nat).

Definition store_int_array (x: addr) (n: Z) (l: list Z): Assertion :=
  store_array (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a) x n l.

Definition store_int_array_missing_i_rec (x: addr) (i lo hi: Z) (l: list Z): Assertion := 
  store_array_missing_i_rec (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a) x i lo hi l.

Definition Constraint_list (c: Constraint): list Z :=
  c.(const) :: c.(coef).

Definition list_Constraint (l: list Z): Constraint :=
  match l with
    | nil    => {| const := 0; coef := nil; |}
    | l0::l' => {| const := l0; coef := l'; |}
  end.

Definition coef_Znth (i: Z) (c: Constraint) (default: Z): Z :=
  Znth i (Constraint_list c) default.

Definition coef_Zlength (c: Constraint): Z :=
  Z.of_nat (Datatypes.length (Constraint_list c)).

Definition coef_array (x: addr) (n: Z) (c: Constraint): Assertion :=
  [| x = NULL |] && emp || 
  [| x <> NULL |] && store_int_array x n (Constraint_list c).

Definition coef_array_missing_i_rec (x: addr) (i lo hi: Z) (c: Constraint): Assertion :=
  store_int_array_missing_i_rec x i lo hi (Constraint_list c).

Definition coef_replace_Znth (i v: Z) (c: Constraint): Constraint :=
  list_Constraint (replace_Znth i v (Constraint_list c)).

Definition coef_pre_eq (i: Z) (c1 c2: Constraint): Prop :=
  forall i0, (0 <= i0 /\ i0 < i) -> coef_Znth i0 c1 0 = coef_Znth i0 c2 0.

Definition generate_new_constraint_partial (n: nat) (m m1 m2: Z) (c1 c2 c: Constraint): Prop :=
  m1 > 0 /\ m2 > 0 /\
  (forall i, (0 <= i /\ i < m) -> coef_Znth i c 0 = m1 * coef_Znth i c1 0 + m2 * coef_Znth i c2 0).
  
Fixpoint InequList (x: addr) (coef_len: Z) (lp: LP): Assertion :=
  match lp with
    | nil    => [| x = NULL |] && emp
    | a::lp' => [| x <> NULL |] &&
                EX c y: addr, 
                  [| c <> NULL |] &&
                  &(x # "InequList" ->ₛ "coef") # Ptr |-> c **
                  coef_array c coef_len a ** 
                  &(x # "InequList" ->ₛ "next") # Ptr |-> y **
                  InequList y coef_len lp'
  end.

Fixpoint InequList_seg (x y: addr) (coef_len: Z) (lp: LP): Assertion :=
  match lp with
    | nil    => [| x = y |] && emp
    | a::lp' => [| x <> NULL |] &&
                EX c z: addr,
                  [| c <> NULL |] &&
                  &(x # "InequList" ->ₛ "coef") # Ptr |-> c **
                  coef_array c coef_len a **
                  &(x # "InequList" ->ₛ "next") # Ptr |-> z **
                  InequList_seg z y coef_len lp'
  end.

Definition InequList_nth_pos (n: Z) (lp: LP): Prop :=
  forall c, In c lp -> coef_Znth n c 0 > 0 /\ coef_Znth n c 0 <= INT_MAX.

Definition InequList_nth_neg (n: Z) (lp: LP): Prop :=
  forall c, In c lp -> coef_Znth n c 0 < 0 /\ -coef_Znth n c 0 <= INT_MAX.

Definition generate_new_constraints_partial (n: nat) (lp11: LP) (x: Constraint) (lp21 lp22 lp: LP): Prop :=
  exists res1 res2, (forall c, In c lp <-> (In c res1 \/ In c res2)) /\
                     generate_new_constraints n lp11 (List.app lp21 lp22) res1 /\
                    (forall c2, In c2 res2 -> (exists c1, In c1 lp21 /\ generate_new_constraint n x c1 c2)).

Definition construct_new_constraint (n: nat) (m1 m2: Z) (c1 c2: Constraint): Constraint :=
  {|
    const := m1 * c1.(const) + m2 * c2.(const);
    coef := list_add (mul_list m1 c1.(coef)) (mul_list m2 c2.(coef));
  |}.

Fixpoint construct_new_constraints1 (n: nat) (p1: Constraint) (lp2: LP): LP :=
  match lp2 with
    | nil    => nil
    | p2::l2 => (construct_new_constraint n 1 1 p1 p2)::(construct_new_constraints1 n p1 l2)
  end.

Fixpoint construct_new_constraints (n: nat) (lp1 lp2: LP): LP :=
  match lp1 with
    | nil    => nil
    | p1::l1 => List.app (construct_new_constraints1 n p1 lp2) (construct_new_constraints n l1 lp2)
  end.

Definition BoundPair (x: addr) (coef_len: Z) (bp: BP): Assertion :=
  EX u l r,
    &(x # "InequList" ->ₛ "upper") # Ptr |-> u **
    &(x # "InequList" ->ₛ "lower") # Ptr |-> l **
    &(x # "InequList" ->ₛ "remain") # Ptr |-> r **
    InequList u coef_len bp.(upper) **
    InequList l coef_len bp.(lower) **
    InequList r coef_len bp.(remain).

Definition form_BP (up lo re: LP) (bp: BP): Prop :=
  up = bp.(upper) /\ lo = bp.(lower) /\ re = bp.(remain).

Definition in_int_range (n m: Z) (c: Constraint): Prop :=
  forall i, (0 <= i /\ i < n) -> (-INT_MAX <= m * coef_Znth i c 0 /\ m * coef_Znth i c 0 <= INT_MAX).

Definition abs_in_int_range (n: Z) (c: Constraint): Prop :=
  forall i, (0 <= i /\ i < n) -> (coef_Znth i c 0 >= -INT_MAX /\ coef_Znth i c 0 <= INT_MAX).

Definition LP_abs_in_int_range (n: Z) (lp: LP): Prop :=
  forall c, In c lp -> abs_in_int_range n c.
