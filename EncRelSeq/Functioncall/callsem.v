Require Import Coq.Lists.List.
From SetsClass Require Import SetsClass.
From AUXLib Require Import Axioms Idents.
From FP Require Import SetsFixedpoints.
From EncRelSeq Require Export semantics errsem.

Import SetsNotation.
Local Open Scope sets.


(*************************************************************************************************************)
(******************************* denotational semantics with procedure calls for state Σ *********************)
(*************************************************************************************************************)
Module CallNormalDeno.
Import normaldeno.

Class  calllangclass {Σ : Type} := {
  Langstmts: Type;
  evalnrm: (func -> Σ -> Σ -> Prop) -> (Langstmts) -> Σ -> Σ -> Prop;
  evalerr: (func -> Σ -> Σ -> Prop) -> (func -> Σ -> Prop) -> (Langstmts) -> Σ -> Prop;
}.


Section procedurecall_sem.
  Context {Σ : Type}.
  Context (χnrm : func -> Σ  -> Σ -> Prop).

  Definition call_denote f  : @denosem Σ :=
  {|
    nrm := (χnrm f);
  |}.

End procedurecall_sem.


(*************************************************************************************************************)
(**********************************             program semantics            *********************************)
(**********************************   Normal Setting                         *********************************)
(**********************************          1. no join                      *********************************)
(**********************************          2. χ: func -> deno Σ            *********************************)
(*************************************************************************************************************)
Module ProgramSem. 
Section  program_sem.
  Context {Σ: Type}.
  Context {callc : @calllangclass Σ}.

  Definition program : Type := list (func * Langstmts).

  Definition prosem_nrm (p : program) : func -> Σ  -> Σ -> Prop :=
  Lfix (fun X f st1 st2 =>
    exists c, In (f, c) p /\
    (evalnrm X c) st1 st2).

  Definition prosem_err (p : program) : func -> Σ  -> Prop :=
  Lfix (fun X f st1 =>
    exists c, In (f, c) p /\
    (evalerr (prosem_nrm p) X c) st1 ).

  Definition prosem (p : program) (f: func) : @denosem Σ := {|
    nrm := prosem_nrm p f;
  |}.

  Definition eval (p : program) (stmt: Langstmts): @denosem Σ := {|
    nrm := evalnrm (prosem_nrm p) stmt;
  |}.

End  program_sem.

End ProgramSem.
End CallNormalDeno.


(*************************************************************************************************************)
(******************************* denotational semantics with procedure calls for state Σ *********************)
(*************************************************  including error   ****************************************)
(*************************************************************************************************************)
Module CallPracticalDeno.
Import practicaldeno.

Class  calllangclass {Σ : Type} := {
  Langstmts: Type;
  evalnrm: (func -> Σ -> Σ -> Prop) -> (Langstmts) -> Σ -> Σ -> Prop;
  evalerr: (func -> Σ -> Σ -> Prop) -> (func -> Σ -> Prop) -> (Langstmts) -> Σ -> Prop;
}.


Section procedurecall_sem.
  Context {Σ : Type}.
  Context (χnrm : func -> Σ  -> Σ -> Prop).
  Context (χerr : func -> Σ  -> Prop).

  Definition call_denote f  : @denosem Σ :=
  {|
    nrm := (χnrm f);
    err := (χerr f);
  |}.

End procedurecall_sem.


(*************************************************************************************************************)
(**********************************             program semantics            *********************************)
(**********************************   Normal Setting                         *********************************)
(**********************************          1. no join                      *********************************)
(**********************************          2. χ: func -> deno Σ            *********************************)
(*************************************************************************************************************)
Module ProgramSem. 
Section  program_sem.
  Context {Σ: Type}.
  Context {callc : @calllangclass Σ}.

  Definition program : Type := list (func * Langstmts).

  Definition prosem_nrm (p : program) : func -> Σ  -> Σ -> Prop :=
  Lfix (fun X f st1 st2 =>
    exists c, In (f, c) p /\
    (evalnrm X c) st1 st2).

  Definition prosem_err (p : program) : func -> Σ  -> Prop :=
  Lfix (fun X f st1 =>
    exists c, In (f, c) p /\
    (evalerr (prosem_nrm p) X c) st1 ).

  Definition prosem (p : program) (f: func) : @denosem Σ := {|
    nrm := prosem_nrm p f;
    err := prosem_err p f;
  |}.

  Definition eval (p : program) (stmt: Langstmts): @denosem Σ := {|
    nrm := evalnrm (prosem_nrm p) stmt;
    err := evalerr (prosem_nrm p) (prosem_err p) stmt
  |}.

End  program_sem.

End ProgramSem.
End CallPracticalDeno.
