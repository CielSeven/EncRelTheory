(**
  * @file errsem.v
  * @brief Extends relational denotational semantics with error handling over state space Σ.
  *
  * @details
  *   - denosem: A relational semantics model with both normal transitions and error cases.
  *   - skip, seq, assert, assume: Standard constructs, now tracking error propagation.
  *   - ife, while: Branching and looping semantics with explicit error components.
  *   - Includes lemmas characterizing the behavior of skip and sequencing with respect to errors.
  *)

From SetsClass Require Import SetsClass.
From FP Require Import SetsFixedpoints.
From EncRelSeq.Basics Require Import semantics.

Import SetsNotation.
Local Open Scope sets.

Module practicaldeno.

Record denosem {Σ : Type}: Type := {
  nrm: Σ  -> Σ -> Prop;
  err: Σ -> Prop
}.

End practicaldeno.

Arguments practicaldeno.nrm  {Σ}.
Arguments practicaldeno.err  {Σ}.

Ltac any_nrm x ::=
  match type of x with
  | normaldeno.denosem => exact (normaldeno.nrm x)
  | practicaldeno.denosem => exact (practicaldeno.nrm x)
  end.

Ltac any_err x := exact (practicaldeno.err x).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).


Module PracticalDenoConstructs.

Import practicaldeno.
Definition skip {Σ : Type}: @denosem Σ := 
{|
  nrm := Rels.id ;
  err := ∅
|}.

Definition seq {Σ : Type} (D1 D2: @denosem Σ) : @denosem Σ := 
{|
  nrm := D1.(nrm) ∘ D2.(nrm);
  err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err))
|}.

Definition deno_test {Σ : Type} : Type := Σ -> Prop. (* change it into bool *) 

Definition deno_and {Σ : Type} (b1 b2: @deno_test Σ) := fun st => b1 st /\ b2 st.

Definition assert {Σ : Type} (B: deno_test) : @denosem Σ  :=
{|
  nrm := fun st1 st2 => B st1 /\ st2 = st1;
  err := fun st1 => ~ B st1
|}.

Definition assume {Σ : Type} (B: deno_test) : @denosem Σ  :=
{|
  nrm := fun st1 st2 => B st1 /\ st2 = st1;
  err := ∅
|}.

Definition notB {Σ : Type} (B: @deno_test Σ) : deno_test := fun st => ~ B st.

Definition ife {Σ : Type} (B: deno_test) (D1 D2: @denosem Σ) : @denosem Σ :=
{|
  nrm := ((assume B).(nrm) ∘ D1.(nrm)) ∪
         ((assume (notB B)).(nrm) ∘ D2.(nrm));
  err := (((assume B).(nrm)) ∘ D1.(err)) ∪ 
         (((assume (notB B)).(nrm)) ∘ (err D2))
|}.

Definition while  {Σ : Type}
             (B: deno_test)
             (Ds: denosem): @denosem Σ:=
  {|
    nrm := Lfix (fun X => (((assume B).(nrm)) ∘ Ds.(nrm) ∘ X) ∪ ((assume (notB B)).(nrm)));
    err := Lfix (fun X : Σ -> Prop => (((assume B).(nrm)) ∘ ((Ds.(nrm) ∘ X) ∪ Ds.(err))))
  |}.

  Lemma skip_nrm {Σ : Type} (st1 st2: Σ) :
    (@skip Σ).(nrm) st1 st2 <-> st1 = st2.
  Proof.
    unfold skip, practicaldeno.nrm. sets_unfold. tauto.
  Qed.

  Lemma skip_err {Σ : Type} (st: Σ) :
    (@skip Σ).(err) st <-> False.
  Proof.
    unfold skip, practicaldeno.err. sets_unfold. tauto.
  Qed.

  Lemma seq_err1 {Σ : Type} (D1 D2: @denosem Σ) (st1 st2: Σ) :
    (D1.(err) st1) ->
    (seq D1 D2).(err) st1.
  Proof.
    destruct D1 as (nrm1 & err1). destruct D2 as (nrm2 & err2).
    unfold seq, practicaldeno.nrm, practicaldeno.err.
    sets_unfold. intros H.
    left;auto.
  Qed.

  Lemma seq_err2 {Σ : Type} (D1 D2: @denosem Σ) (st1 st2 st3: Σ) :
    (D1.(nrm) st1 st3) ->
    (D2.(err) st3) ->
    (seq D1 D2).(err) st1.
  Proof.
    destruct D1 as (nrm1 & err1). destruct D2 as (nrm2 & err2).
    unfold seq, practicaldeno.nrm, practicaldeno.err.
    sets_unfold. intros H.
    right;eauto.
  Qed.

End PracticalDenoConstructs.
