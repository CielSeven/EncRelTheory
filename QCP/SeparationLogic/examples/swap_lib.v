Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
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

Export naive_C_Rules.
Local Open Scope sac.

Inductive swap_para: Type :=
| swap_eq_para: Z -> swap_para
| swap_neq_para: Z -> Z -> swap_para.

Definition swap_pre (px py: addr) (para: swap_para): Assertion :=
  match para with
  | swap_eq_para x => [| px = py |] && store_int px x
  | swap_neq_para x y => store_int px x ** store_int py y
  end.

Definition swap_post (px py: addr) (para: swap_para): Assertion :=
  match para with
  | swap_eq_para x => [| px = py |] && store_int px x
  | swap_neq_para x y => store_int px y ** store_int py x
  end.

