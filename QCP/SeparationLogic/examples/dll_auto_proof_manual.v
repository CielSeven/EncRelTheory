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
From SimpleC.EE Require Import dll_auto_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import dll_shape_lib.
Local Open Scope sac.

Lemma proof_of_dll_copy_entail_wit_1 : dll_copy_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dll_copy_entail_wit_2 : dll_copy_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_dll_free_partial_solve_wit_2_pure : dll_free_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_append_entail_wit_2 : append_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_append_return_wit_2_1 : append_return_wit_2_1.
Proof. Admitted. 

Lemma proof_of_append_return_wit_2_2 : append_return_wit_2_2.
Proof. Admitted. 

Lemma proof_of_iter_entail_wit_1 : iter_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_entail_wit_2 : iter_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_iter_back_entail_wit_1 : iter_back_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_iter_back_entail_wit_2 : iter_back_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_iter_back_return_wit_2 : iter_back_return_wit_2.
Proof. Admitted. 

