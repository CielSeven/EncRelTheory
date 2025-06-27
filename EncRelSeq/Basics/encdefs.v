(**
  * @file encdefs.v
  * @brief This file defines the core encoding from relational assertions 
  *        into unary assertions used in standard Hoare logic.
  *
  * @details
  *   - encode_asrt: Encodes a relational assertion P into a low-level unary assertion [| P |](X), 
  *                  parameterized by a high-level postcondition X.
  *   - valid_relT: Defines `forall X, { [| P |](X) } cₗ { [| Q |](X) }`  
  *   - Exec: Encodes the execution of a high-level program.
  *   - Lemma encode_exp_equiv: EX v, [|P v|](X) --||-- [|EX v, (P v)|](X) 
  *   - Lemma encode_prop_andp:  !! B && P --||-- !! B && [| P |](X)
  *   - Lemma encode_decomposed: [| ⌊ P ⌋ && ⌈ P' ⌉ && [cₕ ]ₕ |](X) --||-- !! Exec P' cₕ X && P
  *)
  
From SetsClass Require Import SetsClass. 
From EncRelSeq.Basics Require Import basictacs basicasrt relasrt hoarelogic.

Import SetsNotation.
Local Open Scope sets_scope.
Local Open Scope asrt_scope.

Class lowlevel_defs (Σₗ Progₗ: Type) : Type :=
  { lowlevel_valid_triple: @HT_validity Σₗ Progₗ
  }.

Class highlevel_defs (Σₕ Progₕ Postasrt: Type): Type :=
  { highlevel_wlp: @Deno_weakestpre Σₕ Progₕ Postasrt
  }.

Section  encoding.
  Context (Σₗ Σₕ: Type).
  Context (Progₗ: Type).
  Context (Progₕ: Type).
  Context (Postasrt: Type).
  Context {LDefs: lowlevel_defs Σₗ Progₗ}.
  Context {HDefs: highlevel_defs Σₕ Progₕ Postasrt}.

  (* This is the definition of "safe".
   It means that if we start in state σ, then after executing c,
   we will end up in a state that belongs to set X. *)    
  Definition safe  (σ : Σₕ) (c: Progₕ) (X: Postasrt) := 
    σ ∈ (highlevel_wlp c X).

  Definition encode_asrt  (P: @relasrt Σₗ Σₕ Progₕ) (X: Postasrt): @asrt Σₗ :=
  fun σₗ => exists (σₕ: Σₕ) (cₕ: Progₕ),  
           σₕ ∈ (highlevel_wlp cₕ X) /\  P (σₗ, σₕ, cₕ).

  Definition valid_relT (P: @relasrt Σₗ Σₕ Progₕ) (cₗ: Progₗ) (Q : @relasrt Σₗ Σₕ Progₕ) := 
  forall X, lowlevel_valid_triple
                    (encode_asrt P X)
                    cₗ 
                    (encode_asrt Q X).

  Definition Exec  (P: @asrt Σₕ) (cₕ: Progₕ) (X: Postasrt) :=
    exists σₕ, σₕ ∈ P /\ σₕ ∈ (highlevel_wlp cₕ X).
End  encoding.



Arguments safe {Σₕ Progₕ Postasrt}%type_scope {HDefs}.
Arguments Exec {Σₕ Progₕ Postasrt}%type_scope {HDefs}. 
Arguments encode_asrt {Σₗ Σₕ Progₕ Postasrt}%type_scope {HDefs}.

Notation " '[|' P '|]' '(' x ')' " := (encode_asrt P x)  (at level 20, no associativity) : asrt_scope. 

Ltac simpl_hdefs:= simpl (highlevel_wlp) in *.

Ltac simpl_ldefs:= simpl (lowlevel_valid_triple) in *.


Section  EncodeLemmas.
  Context (Σₗ Σₕ: Type).
  Context (Progₗ: Type).
  Context (Progₕ: Type).
  Context (Postasrt: Type).
  Context {LDefs: lowlevel_defs Σₗ Progₗ}.
  Context {HDefs: highlevel_defs Σₕ Progₕ Postasrt}.

Ltac destructs H := rel_destruct Σₗ Σₕ Progₗ Progₕ H.


Lemma encode_exp_intro : forall {A: Type} X (P : A ->  @relasrt Σₗ Σₕ Progₕ), 
  EX v, [|P v|](X) |-- [|EX v, (P v)|](X) .
Proof.
  intros.
  unfold derivable1, encode_asrt, exp.
  intros.
  destructs H.
  do 2 eexists.
  split;eauto.
Qed.


Lemma encode_exp_equiv : forall {A: Type} X (P : A ->  @relasrt Σₗ Σₕ  Progₕ), 
  EX v, [|P v|](X) --||-- [|EX v, (P v)|](X) .
Proof.
  intros;split;intros.
  - apply encode_exp_intro.
    auto.
  - 
  unfold derivable1, encode_asrt, exp, exp in *.
  destructs H.
  do 3 eexists.
  split;eauto.
Qed.

Lemma encode_prop_andp : forall (B: Prop) X (P:  @relasrt Σₗ Σₕ  Progₕ), 
  [| !! B && P |](X) --||--  !! B && [| P |](X).
Proof.
  intros.
  unfold logic_equiv, encode_asrt, andp, andp, coq_prop, coq_prop.
  split;intros.
  - destructs H.
    split;auto.
    do 2 eexists.
    split;eauto.
  - destructs H.
    do 2 eexists.
    split;eauto.
Qed.


Lemma encode_decomposed: forall X (P: @asrt Σₗ) (P' : @asrt Σₕ) cₕ,
  [|⌊ P ⌋ && ⌈ P' ⌉ && [cₕ ]ₕ|](X) --||-- !! Exec P' cₕ X && P.
Proof.
  intros;split.
  { unfold derivable1, andp, coq_prop, encode_asrt, andp, Alst, Ahst, Aspec, Exec.
  intros.
  destructs H.
  sets_unfold.
  subst cₕ0.
  split;auto.
  eexists;
  split;eauto. }

  unfold derivable1, andp, coq_prop, encode_asrt, andp, Alst, Ahst, Aspec, Exec.
  intros.
  destructs H.
  sets_unfold. sets_unfold in H1.
  do 2 eexists.
  split;eauto.
Qed.

Lemma Exec_prop_andp : forall B (P: @asrt Σₕ) s X,
  Exec ( !! B && P) s X <-> B /\ Exec P s X.
Proof.
  unfold Exec, basicasrt.andp, basicasrt.coq_prop.
  sets_unfold.
  intros. split;intros.
  - destructs H.
    split;auto.
    eexists.
    split;eauto.
  - destructs H.
    eexists.
    splits;eauto.
Qed.

Lemma encode_logicequiv: forall X (P: @relasrt Σₗ Σₕ Progₕ) (P' : @relasrt Σₗ Σₕ Progₕ),
  P --||-- P' -> 
  [|P|](X) --||-- [|P'|](X).
Proof.
  intros.
  unfold logic_equiv, encode_asrt.
  split;intros.
  - destructs H0.
    do 2 eexists.
    split;eauto. apply H;auto. 
  - destructs H0.
    do 2 eexists.
    split;eauto. apply H;auto. 
Qed.


Lemma encode_normal_form {A:Type}: forall B (P: A -> @asrt Σₗ) (P': A ->  @asrt Σₕ) cₕ X,
  [|EX a : A, !! B a && ⌊ P a ⌋ && ⌈ P' a ⌉ && [cₕ ]ₕ|](X) --||-- 
  EX a : A, !! Exec (P' a) cₕ X && !! B a && P a.
Proof.
  intros.
  eapply logic_equiv_trans.
  apply logic_equiv_symm; apply (encode_exp_equiv _ _ ).
  apply ex_logic_euiqv_elim_both;intros a.
  eapply logic_equiv_trans.
  { apply encode_logicequiv.
    eapply logic_equiv_trans.
    apply logic_equiv_andp_assoc.
    eapply logic_equiv_trans.
    apply logic_equiv_andp_assoc.
    eapply logic_equiv_andp_mono;[apply logic_equiv_refl | ].
    apply logic_equiv_symm.
    apply logic_equiv_andp_assoc. }
  eapply logic_equiv_trans.
  apply (encode_prop_andp (B a) _ _).
  eapply logic_equiv_trans.
  apply logic_equiv_andp_mono;[apply logic_equiv_refl | ].
  apply encode_decomposed.
  eapply logic_equiv_trans.
  apply logic_equiv_symm.
  apply logic_equiv_andp_assoc.
  apply logic_equiv_andp_mono;[ | apply logic_equiv_refl].
  apply logic_equiv_andp_comm.
Qed.


Lemma encode_derives: forall X (P: @relasrt Σₗ Σₕ Progₕ) (P' : @relasrt Σₗ Σₕ Progₕ),
  P |-- P' -> 
  [|P|](X) |-- [|P'|](X).
Proof.
  intros.
  unfold derivable1, encode_asrt.
  intros.
  destructs H0.
  do 2 eexists.
  split;eauto. 
Qed.

Lemma encode_andp_split : forall X (x y: @relasrt Σₗ Σₕ Progₕ), 
  [| x && y |](X) |-- [| x |](X) && [| y |](X).
Proof.
  intros.
  unfold derivable1, encode_asrt, andp.
  intros.
  destructs H.
  split.
  all :do 2 eexists;
      split;eauto. 
Qed.

Lemma encode_andp_merge : forall X (x y: @relasrt Σₗ Σₕ Progₕ), 
  [| x |](X) && [| y |](X) |-- [| x && y |](X).
Proof.
  intros. 
  unfold derivable1, encode_asrt, andp.
  intros.
  destructs H.
  do 2 eexists;
      split;eauto. 
Abort.
(* ATTENTION : THE REVERSE IS WRONG *)


Lemma encode_expunit_equiv : forall X (P :  @relasrt Σₗ Σₕ Progₕ), 
  EX (v : unit), [|P|](X) --||-- [|P|](X) .
Proof.
  intros;split;intros.
  - destructs H.
    auto.
  - 
  unfold derivable1, encode_asrt, exp, exp in *.
  destructs H.
  do 3 eexists.
  split;eauto.
Qed.



(**********************************************************************************)
(*    relation asrt rules                                                         *)
(**********************************************************************************)
Lemma derives_imply_lderi : forall (P P' : @relasrt Σₗ Σₕ  Progₕ) ,
 P |-- P' ->
 (forall X,  [| P |] (X)  |-- [| P' |] (X) ).
Proof.
  unfold derivable1, encode_asrt.
  intros.
  destructs H0.
  do 2 eexists;split;eauto. 
Qed.


Lemma rhasrt_purelow_equiv : forall (B: Prop) (P: @asrt Σₗ) Ps (Pfrm: @relasrt Σₗ Σₕ  Progₕ) , 
  !! B && Pfrm && ⌊ P ⌋ && ⌈ Ps ⌉  --||--  Pfrm &&  ⌊ !! B && P ⌋ && ⌈ Ps ⌉ .
Proof.
  intros.
  unfold coq_prop, coq_prop, andp, andp, Alst, logic_equiv.
  intros;split;destruct st as ((? & ?) & ?).
  - intros [? ?].
    destructs H.
    auto.
  - intros.
    split.
    + unfold andp in H.
      destructs H.
      auto.
    + tauto.
Qed.

Lemma rhasrt_purehigh_equiv : forall B P Ps (Pfrm: @relasrt Σₗ Σₕ  Progₕ), 
  !! B && Pfrm && ⌊ P ⌋ && ⌈ Ps ⌉  --||-- Pfrm && ⌊ P ⌋ && ⌈ !! B && Ps ⌉.
Proof.
  intros.
  unfold coq_prop, andp,  logic_equiv, Alst, Ahst.
  intros;split;destruct st as ((? & ?) & ?).
  - intros. 
    tauto.
  - intros.
    tauto.
Qed.

Lemma rhasrt_exlow_equiv : forall {A: Type} (P: A -> ( Σₗ -> Prop ) ) Ps (Pfrm: @relasrt Σₗ Σₕ  Progₕ), 
  EX v, Pfrm && ⌊ P v ⌋ && ⌈ Ps ⌉ --||-- Pfrm && ⌊ EX v, P v ⌋ && ⌈ Ps ⌉.
Proof.
  intros.
  unfold exp, andp, logic_equiv, Alst, Ahst.
  intros;split;destruct st as ((? & ?) & ?).
  - intros.
    destructs H.
    splits;auto.
    eexists;eauto.
  - intros.
    destructs H.
    exists x.
    splits;auto.
Qed.

Lemma rhasrt_exhigh_equiv : forall {A: Type} P (Ps : A -> (Σₕ -> Prop)) (Pfrm: @relasrt Σₗ Σₕ  Progₕ), 
  EX v, Pfrm && ⌊ P ⌋ && ⌈ Ps v ⌉ --||-- Pfrm && ⌊ P ⌋ && ⌈ EX v, Ps v ⌉ .
Proof.
  intros.
  unfold exp, andp, logic_equiv, Alst, Ahst.
  intros;split;destruct st as ((? & ?) & ?).
  - intros.
    destructs H.
    splits;auto.
    eexists;eauto.
  - intros.
    destructs H.
    exists x.
    splits;auto.
Qed.


Lemma rhasrt_exsepc_equiv : forall {A: Type} (P : A -> @relasrt Σₗ Σₕ  Progₕ) s, 
  EX x,  Aspec s && P x --||--  Aspec s && (EX x, P x).
Proof.
  unfold exp, andp, Aspec, logic_equiv;split;intros;destruct st as ((? & ?) & ?).
  - destructs H.
    splits;auto.
    eexists;eauto.
  - destructs H.
    eexists;splits;eauto.
Qed. 

Lemma rhasrt_propsepc_equiv : forall (P : Prop) s (Pfrm: @relasrt Σₗ Σₕ  Progₕ), 
  !! P && Aspec s && Pfrm --||--  Aspec s && (!! P && Pfrm).
Proof.
  unfold coq_prop, andp, Aspec, logic_equiv;split;intros;destruct st as ((? & ?) & ?).
  - destructs H.
    splits;auto.
  - tauto.
Qed. 

Lemma rh_ex_elim_both : forall {A: Type} (P Q : A -> @relasrt Σₗ Σₕ  Progₕ),
  (forall v, P v |-- Q v) -> EX v, P v |--  EX v, Q v.
Proof.
  unfold exp, derivable1;intros * H * HP.
  destruct st as ((? & ?) & ?).
  destructs HP.
  eexists.
  eapply H;eauto.
Qed.

Lemma rh_prop_andp_andp1: forall P Q (R: @relasrt Σₗ Σₕ  Progₕ),
  (!! P && Q) && R  --||-- !! P && (Q && R).
Proof.
  unfold coq_prop, andp, logic_equiv;intros.
  split;intros.
  + destructs H.
    split;auto.
  + destructs H.
    splits;eauto.
Qed.

End  EncodeLemmas.


Arguments encode_decomposed {Σₗ Σₕ Progₕ Postasrt HDefs}.
Arguments encode_exp_intro {Σₗ Σₕ  Progₕ Postasrt HDefs A}.
Arguments encode_exp_equiv {Σₗ Σₕ  Progₕ Postasrt HDefs A}.
Arguments encode_prop_andp {Σₗ Σₕ  Progₕ Postasrt HDefs}.
Arguments encode_derives {Σₗ Σₕ  Progₕ Postasrt HDefs}.
Arguments encode_andp_split {Σₗ Σₕ  Progₕ Postasrt HDefs}.
Arguments encode_expunit_equiv {Σₗ Σₕ  Progₕ Postasrt HDefs}.
Arguments derives_imply_lderi {Σₗ Σₕ  Progₕ Postasrt HDefs}.
Arguments rhasrt_purelow_equiv {Σₗ Σₕ  Progₕ }.
Arguments rhasrt_purehigh_equiv {Σₗ Σₕ  Progₕ }.
Arguments rhasrt_exlow_equiv {Σₗ Σₕ  Progₕ }.
Arguments rhasrt_exhigh_equiv {Σₗ Σₕ  Progₕ A}.
Arguments rhasrt_exsepc_equiv {Σₗ Σₕ  Progₕ A}.
Arguments rhasrt_propsepc_equiv {Σₗ Σₕ  Progₕ }.
Arguments rh_ex_elim_both {Σₗ Σₕ  Progₕ A}.
Arguments rh_prop_andp_andp1 {Σₗ Σₕ  Progₕ }.