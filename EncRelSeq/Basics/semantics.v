(**
  * @file semantics.v
  * @brief Defines generic relational denotational semantics over a state space Σ.
  *
  * @details
  *   - denosem: A record capturing normal transition semantics as binary relations.
  *   - skip, seq, assert, assume: Basic denotational constructs.
  *   - ife, while: Conditional and looping constructs via relational composition and fixed points.
  *   - Built using union, composition, and greatest fixed point over sets of state transitions.
  *)

From SetsClass Require Import SetsClass.
From FP Require Import SetsFixedpoints.

Import SetsNotation.
Local Open Scope sets.

Module normaldeno.
Record denosem {Σ : Type}: Type := {
  nrm: Σ  -> Σ -> Prop;
}.

End normaldeno.

Arguments normaldeno.nrm  {Σ}.

Ltac any_nrm x := exact (normaldeno.nrm x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Module NormalDenoConstructs.

Import normaldeno.
Definition skip {Σ : Type}: @denosem Σ := 
{|
  nrm := Rels.id ;
|}.

Definition seq {Σ : Type} (D1 D2: @denosem Σ) : @denosem Σ := 
{|
  nrm := D1.(nrm) ∘ D2.(nrm);
|}.

Definition deno_test {Σ : Type} : Type := Σ -> Prop. (* change it into bool *) 

Definition deno_and {Σ : Type} (b1 b2: @deno_test Σ) := fun st => b1 st /\ b2 st.

Definition assert {Σ : Type} (B: deno_test) : @denosem Σ  :=
{|
  nrm := fun st1 st2 => B st1 /\ st2 = st1;
|}.

Definition assume {Σ : Type} (B: deno_test) : @denosem Σ  :=
{|
  nrm := fun st1 st2 => B st1 /\ st2 = st1;
|}.

Definition notB {Σ : Type} (B: @deno_test Σ) : deno_test := fun st => ~ B st.

Definition ife {Σ : Type} (B: deno_test) (D1 D2: @denosem Σ) : @denosem Σ :=
{|
  nrm := ((assume B).(nrm) ∘ D1.(nrm)) ∪
         ((assume (notB B)).(nrm) ∘ D2.(nrm));
|}.

Definition while  {Σ : Type}
             (B: deno_test)
             (Ds: denosem): @denosem Σ:=
  {|
    nrm := Lfix (fun X => (((assume B).(nrm)) ∘ Ds.(nrm) ∘ X) ∪ ((assume (notB B)).(nrm)));
  |}.


End NormalDenoConstructs.
