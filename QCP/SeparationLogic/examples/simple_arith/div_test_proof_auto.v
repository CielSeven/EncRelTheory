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
From SimpleC.EE.simple_arith Require Import div_test_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import PDiv_lib.
Local Open Scope sac.

Lemma proof_of_div_test_safety_wit_1 : div_test_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_div_test_safety_wit_2 : div_test_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_div_test_safety_wit_5 : div_test_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_div_test_safety_wit_6 : div_test_safety_wit_6.
Proof. Admitted. 

