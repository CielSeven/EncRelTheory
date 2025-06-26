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
From SimpleC.EE Require Import sll_insert_sort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Require Import sll_insert_sort_lib.
Local Open Scope sac.

Lemma proof_of_insertion_safety_wit_1 : insertion_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_insertion_partial_solve_wit_1 : insertion_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_insertion_partial_solve_wit_2_pure : insertion_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_insertion_partial_solve_wit_2 : insertion_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_insertion_partial_solve_wit_3_pure : insertion_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_insertion_partial_solve_wit_3 : insertion_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_insertion_partial_solve_wit_4_pure : insertion_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_insertion_partial_solve_wit_4 : insertion_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_insertion_which_implies_wit_1 : insertion_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_insertion_sort_safety_wit_1 : insertion_sort_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_insertion_sort_safety_wit_2 : insertion_sort_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_insertion_sort_partial_solve_wit_1_pure : insertion_sort_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_insertion_sort_partial_solve_wit_1 : insertion_sort_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_insertion_sort_partial_solve_wit_2_pure : insertion_sort_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_insertion_sort_partial_solve_wit_2 : insertion_sort_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_insertion_sort_which_implies_wit_1 : insertion_sort_which_implies_wit_1.
Proof. Admitted. 

