Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import String.
Require Import Permutation.

From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From compcert.lib Require Export Integers.

From SimpleC.SL Require Import Mem.
From SimpleC.SL Require Export IntLib ArrayLib StoreAux.
From AUXLib Require Export ListLib.
From SimpleC.SL Require Export CommonAssertion.
From SimpleC.SL Require Assertion ConAssertion CriticalSTS.

Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.

Module CRules <: SeparationLogicSig.
  Include Assertion.SL.
  Include DerivedPredSig.
  Include StoreLibSig.
  Include ArrayLibSig.
End CRules.

Module naive_C_Rules <: ConAssertion.CSL ConAssertion.STS_naive <: SeparationLogicSig.
  Include ConAssertion.STS_naive.
  Include ConAssertion.CSL.
  Include DerivedPredSig.
  Include StoreLibSig.
  Include ArrayLibSig.
End naive_C_Rules.

Parameter field_address : Z -> string -> string -> Z.
Definition should_be_equal {A : Type} (x y : A) : Prop := True.