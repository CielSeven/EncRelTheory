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
From SimpleC.EE Require Import swap_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import swap_lib.
Local Open Scope sac.

Lemma proof_of_swap_partial_solve_wit_1 : swap_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_swap_partial_solve_wit_2 : swap_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_swap_partial_solve_wit_3 : swap_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_swap_test1_return_wit_1 : swap_test1_return_wit_1.
Proof. Admitted. 

Lemma proof_of_swap_test1_partial_solve_wit_1 : swap_test1_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_swap_test2_return_wit_1 : swap_test2_return_wit_1.
Proof. Admitted. 

Lemma proof_of_swap_test2_partial_solve_wit_1_pure : swap_test2_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_swap_test2_partial_solve_wit_1 : swap_test2_partial_solve_wit_1.
Proof. Admitted. 

