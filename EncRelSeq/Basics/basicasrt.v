(**
  * @file basicasrt.v
  * @brief This file defines a shallow embedding of logical assertions over a parameterized state space.
  *        Assertions are predicates over program states, and logical connectives are modeled as operations
  *        over these predicates.
  *
  * @details
  1. Section base_connectives: Defines the basic logical connectives and assertions including:
    - Logical Entailment : P |-- Q
    - Implication: P --> Q
    - Conjunction: P && Q 
    - Disjunction: P || Q
    - Existential quantification: EX x, P x
    - Universal quantification: ALL x, P x
    - Lifted Coq-level proposition: !! P
    - Always-true assertion: TT
    - Logical Equivalence: P --||-- Q

  2. Section sepcon_connectives: Defines separation logic connectives such as:
    - Separation conjunction: P ** Q
    - Wand (implication in separation logic): P -* Q
    - Emp (empty heap assertion): emp
*)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import EncRelSeq.Basics.basictacs.

(** ** Assertion Type *)
(* An assertion is just a predicate over states. *)
Definition asrt {state: Type} : Type := state -> Prop.

(** ** Logical Connectives over Assertions *)
Section base_connectives.
  Context {state : Type}.
  
  (* Alias for assertions over this state. *)
  Definition expr :Type := @asrt state.

  (* Logical Entailment :[P |-- Q] *)
  Definition derivable1 : (expr -> expr -> Prop) := fun P Q => forall st, P st -> Q st.
  (* Implication: [P --> Q] *)
  Definition impp (P: expr) (Q: expr) : expr := fun st => P st -> Q st.
  (* Conjunction: [P && Q] *)
  Definition andp (P: expr) (Q: expr) : expr := fun st => P st /\ Q st.
  (* Disjunction: [P || Q] *)
  Definition orp (P: expr) (Q: expr) : expr := fun st => P st \/ Q st.
  (* Existential quantification: [EX x, P x] *)
  Definition exp {A : Type} (p : A -> asrt) : expr :=
    fun st => exists x, p x st.
  (* Universal quantification: [ALL x, P x] *)
  Definition allp {A : Type} (p : A -> asrt) : expr :=
    fun st => forall x, p x st.
  (* Lift a Coq-level proposition into an assertion : [!! P] *)
  Definition coq_prop P : expr := fun st => P.
  (* Always-true assertion: [TT] *)
  Definition truep : expr := fun st => True.
  (* Logical Equivalence: [P --||-- Q] *)
  Definition logic_equiv : expr -> expr -> Prop := fun P Q => forall st, P st <-> Q st.

  Lemma logic_equiv_derivable1_1 : forall P Q, logic_equiv P Q -> derivable1 P Q.
  Proof. cbv. intros. apply H. auto. Qed.  
  Lemma logic_equiv_derivable1_2 : forall P Q, logic_equiv P Q -> derivable1 Q P.
  Proof.  cbv. intros. apply H. auto. Qed. 

  Lemma ex_elim_both: forall (A: Type) (P Q: A -> expr),
  (forall v, derivable1 (P v)  (Q v)) -> derivable1 (exp P) (exp Q).
  Proof. cbv. intros. destruct H0. apply H in H0. eexists. eauto. Qed.
  
End base_connectives.

Arguments logic_equiv_derivable1_1 {state} [P] [Q].
Arguments logic_equiv_derivable1_2 {state} [P] [Q].

#[export] Instance derivable1_reflexivity {state: Type}: Reflexive (@derivable1 state).
Proof.
  hnf. unfold derivable1. intros. intuition eauto. Qed. 
#[export] Instance derivable1_transivity {state: Type}: Transitive (@derivable1 state).
Proof.
  hnf. unfold derivable1. intros. intuition eauto. Qed. 


(** ** Notations for Assertions *)
Declare Scope asrt_scope.
Notation "x |-- y" := (derivable1 x y) (at level 70, no associativity): asrt_scope.
Notation "x --||-- y" := (logic_equiv x y ) (at level 60, no associativity): asrt_scope.
Notation "x && y" := (andp x y) : asrt_scope.
Notation "x || y" := (orp x y): asrt_scope.
Notation "x --> y " := (impp x y): asrt_scope.
Notation " !! P " := (coq_prop P) (at level 29, no associativity): asrt_scope.
Notation " 'TT' " := (truep) (at level 29, no associativity): asrt_scope.
Notation "'EX' x , p " :=
  (exp (fun x => p))
    (at level 45, x binder, right associativity): asrt_scope.
Notation "'EX' x : t , p " :=
  (exp (fun x : t => p))
    (at level 45, x binder, right associativity): asrt_scope.
Notation "'EX' x .. y , p" :=
  (exp (fun x => .. (exp (fun y => p)) ..))
    (at level 45, x binder, right associativity): asrt_scope.
Notation "'ALL' x , p " :=
  (allp (fun x => p))
    (at level 45, x binder, right associativity): asrt_scope.
Notation "'ALL' x : t , p " :=
  (allp (fun x : t => p))
    (at level 45, x binder, right associativity): asrt_scope.
Notation "'ALL' x .. y , p" :=
  (allp (fun x => .. (allp (fun y => p)) ..))
    (at level 45, x binder, right associativity): asrt_scope.

Local Open Scope asrt_scope.

  
Section  base_connectives_lemmas.
  Context {state: Type}.

Lemma derivable1_imp : forall (P Q: @asrt state) st, P |-- Q ->  P st -> Q st.
Proof.
  unfold derivable1; intros.
  intuition auto.
Qed.

Lemma exp_right_exists : forall {A: Type} P (Q: A -> @asrt state),
 (exists x, P |-- Q x) -> P |-- EX x, Q x.
Proof.
  unfold derivable1, exp;intros.
  destruct H.
  eexists. intuition auto. Qed.

Lemma ex_comm_logic_euiqv:
  forall {A B: Type} (P : A -> B -> @asrt state),
  EX a b, P a b  --||-- EX b a, P a b.
Proof.
  unfold basicasrt.exp, basicasrt.logic_equiv;split;intros * H;
  Destruct H; do 2 eexists;eauto.
Qed.

Lemma ex_uncurry_logic_euiqv:
  forall {A B: Type} (P : A -> B -> @asrt state),
  EX a b, P a b  --||-- EX (c : A * B), uncurry P c.
Proof.
  unfold basicasrt.exp, basicasrt.logic_equiv, uncurry;split;intros * H.
  - Destruct H.
    exists (x, x0).
    auto.
  - Destruct H.
    destruct x.
    exists a, b.
    auto.
Qed.

Lemma uncurry_ex_logic_euiqv:
  forall {A B: Type} (P : A -> B -> @asrt state) (a: A * B),
  uncurry P a  --||-- P (fst a) (snd a).
Proof.
  unfold basicasrt.logic_equiv, uncurry;intros A B P [? ?]; split;intros * H;simpl;auto.
Qed.

Lemma ex_fstsnd_logic_euiqv:
  forall {A B: Type} (P : A -> B -> @asrt state),
  EX a b, P a b  --||-- EX (c : A * B), P (fst c) (snd c).
Proof.
  unfold basicasrt.exp, basicasrt.logic_equiv, uncurry;split;intros * H.
  - Destruct H.
    exists (x, x0).
    auto.
  - Destruct H.
    destruct x.
    exists a, b.
    auto.
Qed.

Lemma ex_unit_logic_euiqv:
  forall (P : unit -> @asrt state),
  EX (a: unit ), P a  --||-- P tt.
Proof.
  unfold basicasrt.exp, basicasrt.logic_equiv;split;intros * H.
  - Destruct H.
    destruct x.
    auto.
  - eexists. eauto.
Qed.

Lemma ex_logic_euiqv_andp:
  forall {A : Type} (P : A -> @asrt state) (Q :  @asrt state),
  (EX y, P y) && Q  --||-- EX x : A, P x && Q.
Proof.
  unfold basicasrt.andp, basicasrt.exp, basicasrt.logic_equiv;split;intros.
  Destruct H.
  splits;eauto.

  Destruct H.
  splits;eauto.
Qed.

Lemma ex_logic_euiqv_elim_both : forall {A: Type} (P Q : A -> @asrt state),
  (forall v, P v --||-- Q v) -> EX v, P v --||--  EX v, Q v.
Proof.
  unfold basicasrt.exp, basicasrt.logic_equiv;simpl;intros * H st. 
  split;intros H0;
  destruct H0;
  eexists; eapply H;eauto.
Qed.

Lemma logic_equiv_andp_mono : forall x y (u v: @asrt state), 
  x --||-- u -> y --||-- v ->
  x && y --||-- u && v.
Proof.
  unfold basicasrt.logic_equiv, basicasrt.andp. intros.
  split;intuition eauto. 
  apply H;auto. apply H0;auto. apply H;auto. apply H0;auto.
Qed.

Lemma derivable1_andp_mono : (forall x1 x2 y1 y2 :  @asrt state, x1 |-- x2 -> y1 |-- y2 -> (x1 && y1) |-- (x2  && y2)) .
Proof.
  unfold basicasrt.derivable1, basicasrt.andp; intros * H H0 * [? ?].
  split;intuition auto.
Qed.

Lemma prop_andp_elim_equiv:
forall  (P : Prop) (Q : @asrt state), P ->
  (!! P && Q) --||--  Q.
Proof.
  unfold basicasrt.logic_equiv, basicasrt.coq_prop, basicasrt.andp; intros. 
  split;intros;tauto.
Qed.


Lemma truep_andp_elim1 : forall (P: @asrt state),  P --||-- TT && P.
Proof. unfold basicasrt.logic_equiv,basicasrt.andp, basicasrt.truep;intros. tauto. Qed.

Lemma truep_andp_elim2 : forall (P: @asrt state),  P --||-- P && TT.
Proof. unfold basicasrt.logic_equiv,basicasrt.andp, basicasrt.truep;intros. tauto. Qed.

Lemma prop_add_left : forall (P: @asrt state) Q, 
   P |-- !! Q -> P --||-- !! Q && P.
Proof.
  unfold coq_prop, logic_equiv, derivable1, andp ; intros.
  split ; try tauto ; split ; auto.
  eapply H. eauto.
Qed.

Lemma truep_andp_left_equiv : forall (P: @asrt state) , TT && P --||-- P.
Proof.
  intros.
  unfold logic_equiv, andp, truep, derivable1; split; intros ; tauto.
Qed.

Lemma truep_andp_right_equiv : forall (P: @asrt state) , P && TT --||-- P.
Proof.
  intros.
  unfold logic_equiv, andp, truep, derivable1; split; intros ; tauto.
Qed.

Lemma coq_prop_imply : forall (P Q : Prop), (P -> Q) -> @derivable1 state (!! P)  (!! Q) .
Proof.
  intros.
  unfold coq_prop, derivable1 ; intros ; tauto.
Qed.

Lemma exp_allp_left: forall {A: Type} (P: A -> @asrt state) Q,
  (exists x, P x |-- Q) -> 
  ALL x, P x |-- Q.
Proof.
  intros.
  unfold exp, allp, derivable1 in *.
  destruct H. intros. auto.
Qed.

Lemma exp_allp_swap: forall {A B : Type} (P : A -> B -> @asrt state), EX x, ALL y, P x y |-- ALL y, EX x, P x y.
Proof.
  intros.
  unfold exp, allp, derivable1; intros.
  destruct H. exists x0. auto.
Qed.

Lemma allp_allp_swap: forall {A B : Type} (P : A -> B -> @asrt state), ALL x, ALL y, P x y |-- ALL y, ALL x, P x y.
Proof.
  intros.
  unfold exp, allp, derivable1; intros.
  auto.
Qed.

Lemma coq_prop_right : (forall (P : Prop) (x : @asrt state), P -> derivable1 x (coq_prop P)) .
Proof. unfold derivable1, coq_prop, basicasrt.derivable1, basicasrt.coq_prop;intros;auto. Qed.
Lemma coq_prop_left : (forall (P : Prop) (x : @asrt state), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) .
Proof. unfold coq_prop, truep, derivable1, basicasrt.coq_prop, basicasrt.truep, basicasrt.derivable1;intros. intuition auto. Qed.
Lemma shallow_exp_right : (forall (A : Type) (P : @asrt state) (Q : A -> @asrt state) (x : A), derivable1 P (Q x) -> derivable1 P (exp Q)) .
Proof. unfold derivable1, exp, basicasrt.derivable1. intros. eexists. intuition auto. Qed.
Lemma shallow_exp_left : (forall (A : Type) (P : A -> @asrt state) (Q : @asrt state), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp P) Q) .
Proof. unfold derivable1, exp, basicasrt.derivable1. intros. destruct H0. intuition eauto. Qed.
Lemma derivable1_orp_intros1 : (forall x y : @asrt state, derivable1 x (orp x y)) .
Proof. unfold derivable1, orp, basicasrt.derivable1, basicasrt.orp;intros. intuition auto. Qed.
Lemma derivable1_orp_intros2 : (forall x y : @asrt state, derivable1 y (orp x y)) .
Proof. unfold derivable1, orp, basicasrt.derivable1, basicasrt.orp;intros. intuition auto. Qed.
Lemma derivable1_orp_elim : (forall x y z : @asrt state, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) .
Proof. unfold derivable1, orp. cbv. intros. intuition auto. Qed.
Lemma derivable1_andp_intros : (forall x y z : @asrt state, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) .
Proof. unfold derivable1, andp. cbv. intros. intuition auto. Qed.
Lemma derivable1_andp_elim1 : (forall x y : @asrt state, derivable1 (andp x y) x) .
Proof. unfold derivable1, andp;cbv. intros. intuition auto. Qed.
Lemma derivable1_andp_elim2 : (forall x y : @asrt state, derivable1 (andp x y) y) .
Proof. unfold derivable1, andp;cbv. intros. intuition auto. Qed.
Lemma derivable1_impp_andp_adjoint : (forall x y z : @asrt state, derivable1 x (impp y z) <-> derivable1 (andp x y) z) .
Proof. unfold derivable1, impp, andp;cbv. intros P Q R. intuition auto. Qed.
Lemma derivable1_refl : (forall x : @asrt state, derivable1 x x) .
Proof. unfold derivable1. cbv. intros P *. intuition auto. Qed.
Lemma derivable1_trans : (forall x y z : @asrt state, derivable1 x y -> derivable1 y z -> derivable1 x z) .
Proof. unfold derivable1. cbv. intros P Q R. intuition auto. Qed.
Lemma derivable1_coq_prop_impp : (forall P Q : Prop, @derivable1 state (impp (coq_prop P) (coq_prop Q)) (coq_prop (P -> Q))).
Proof. unfold derivable1, impp, coq_prop; cbv. intros. intuition auto. Qed.
Lemma logic_equiv_refl : (forall x : @asrt state, logic_equiv x x) .
Proof. unfold logic_equiv;cbv. split;intros;auto. Qed.
Lemma logic_equiv_symm : forall x y : @asrt state, logic_equiv x y -> logic_equiv y x.
Proof. unfold logic_equiv;cbv. split;intros;apply H; auto. Qed.
Lemma logic_equiv_trans : forall x y z : @asrt state, logic_equiv x y -> logic_equiv y z -> logic_equiv x z.
Proof. unfold logic_equiv;cbv. intros * H H0;split;intros. 
        apply H0;apply H;auto.
        apply H;apply H0;auto. Qed.
Lemma logic_equiv_derivable1 : (forall x y : @asrt state, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) .
Proof. unfold logic_equiv, derivable1; cbv. intros;split;intros.
        split;intros;apply H;auto.
        destruct H. split;intros;[apply H| apply H0];auto. Qed.
Lemma derivable1_truep_intros : forall x : @asrt state, derivable1 x truep.
Proof. unfold derivable1, truep;cbv. intros. auto. Qed. 
Lemma logic_equiv_andp_congr : forall x1 x2 y1 y2 : @asrt state,
                        logic_equiv x1 x2 ->
                        logic_equiv y1 y2 ->
                        logic_equiv (andp x1 y1) (andp x2 y2).
Proof.  unfold logic_equiv, andp;cbv. intros. 
      split;intros [? ?]. 
      split;[apply H | apply H0];auto.
      split;[apply H | apply H0];auto. Qed. 
Lemma logic_equiv_andp_comm : forall x y : @asrt state,
                          logic_equiv (andp x y) (andp y x).
Proof. unfold logic_equiv, andp;cbv. tauto. Qed.
Lemma logic_equiv_andp_assoc : forall x y z : @asrt state,
                          logic_equiv (andp (andp x y) z) (andp x (andp y z)).
Proof. unfold logic_equiv, andp;cbv. tauto. Qed.
Lemma logic_equiv_orp_congr : forall x1 x2 y1 y2 : @asrt state,
logic_equiv x1 x2 ->
  logic_equiv y1 y2 ->
  logic_equiv (orp x1 y1) (orp x2 y2).
Proof. unfold logic_equiv, orp;cbv. intros. 
split;intros [ | ]. 1,3: left;apply H;auto. all: right;apply H0;auto. Qed. 

Lemma logic_equiv_orp_comm : forall x y : @asrt state, logic_equiv (orp x y) (orp y x).
Proof. unfold logic_equiv, orp;cbv. tauto. Qed.
Lemma logic_equiv_orp_assoc : forall x y z : @asrt state,
    logic_equiv (orp (orp x y) z) (orp x (orp y z)).
Proof. unfold logic_equiv, orp;cbv. tauto. Qed.

End  base_connectives_lemmas.

Module Type Lang.
Parameter state : Type.
End Lang.


(* The [JoinM] class describes a model of separation logic with:
   - [join s1 s2 s]: s is the result of joining disjoint states s1 and s2
   - [is_unit s]: s behaves as a unit (identity) for [join] *)
Class  JoinM {state : Type} := {
  join : state -> state -> state -> Prop;
  is_unit : state -> Prop
}.


Section sepcon_connectives.
  Context {state : Type}.
  Context `{mc: @JoinM state}.

  (* Separating conjunction: [P ** Q] holds on state [st] if [st] can be split into [st1] and [st2]
     such that [P st1] and [Q st2] both hold. *)
  Definition sepcon (P: expr) (Q: expr) :@expr state:=  
    fun st => exists st1 st2, join st1 st2 st  /\
      P st1 /\ Q st2.

  (* The [emp] assertion holds on unit states. *)
  Definition emp : expr := fun st  => is_unit st.

  (* Magic wand: [P -* Q] holds on [st] if, whenever [st] can be extended with [st1] to [st2]
     and [P] holds on [st1], then [Q] holds on [st2]. *)
  Definition wand := (fun (x y : expr) st => forall st1 st2, join st st1 st2 -> x st1 -> y st2) .
End sepcon_connectives.

Notation "x ** y" := (sepcon x y) (at level 31, left associativity): asrt_scope.
Notation "x -* y" := (wand x y) (at level 45, right associativity) : asrt_scope.

(** ** JoinM Axioms *)
(* The [JoinMAxioms] class captures the axioms of a join monoid, which are:
   - Existence of a unit element for each state
   - Joining with a unit leaves the state unchanged
   - Commutativity and associativity of the join operation *)
Class  JoinMAxioms {state : Type} {JM: @JoinM state}:= {
  unit_join : (forall n : state, exists u : state, is_unit u /\ join n u n);
  unit_spec : (forall n m u : state, is_unit u -> join n u m -> n = m);
  join_comm : (forall m1 m2 m : state, join m1 m2 m -> join m2 m1 m);
  join_assoc : (forall mx my mz mxy mxyz : state, join mx my mxy -> join mxy mz mxyz -> exists myz : state, join my mz myz /\ join mx myz mxyz);
}.

Section sepcon_connectives_lemmas.
  Context {state : Type}.
  Context `{mc: @JoinM state}.
  Context `{jma: @JoinMAxioms state mc}.

  

Lemma ex_sepcon2:
forall (A : Type) (P : @asrt state) (Q : A -> @asrt state),
P ** (EX y, Q y) |-- EX x : A, (P ** Q x).
Proof.
  unfold basicasrt.exp, basicasrt.derivable1, basicasrt.sepcon;intros.
  Destruct H.
  do 3 eexists.
  splits;eauto.
Qed.

Lemma ex_sepcon1:
  forall (A : Type) (P : A -> @asrt state) (Q :  @asrt state),
  (EX y, P y) ** Q  |-- EX x : A, (P x ** Q).
Proof.
  unfold basicasrt.exp, basicasrt.derivable1, basicasrt.sepcon;intros.
  Destruct H.
  do 3 eexists.
  splits;eauto.
Qed.

Lemma ex_logic_euiqv_sepcon:
  forall {A : Type} (P : A -> @asrt state) (Q :  @asrt state),
  (EX y, P y) ** Q  --||-- EX x : A, P x ** Q.
Proof.
  unfold basicasrt.exp, basicasrt.derivable1, basicasrt.sepcon;split;intros.
  Destruct H.
  do 3 eexists.
  splits;eauto.

  Destruct H.
  do 2 eexists.
  splits;eauto.
Qed.

Lemma prop_andp_sepcon1: forall P Q R,
  (!! P && Q) ** R  --||-- !! P && (Q ** R).
Proof.
  unfold basicasrt.logic_equiv, basicasrt.coq_prop, basicasrt.andp, basicasrt.sepcon;intros.
  split;intros.
  + Destruct H.
    split;auto.
    do 2 eexists.
    splits;eauto.
  + Destruct H.
    do 2 eexists.
    splits;eauto.
Qed.

Lemma sepcon_prop_equiv : 
forall (P : @asrt state) (Q : Prop),
P ** (!! Q) --||--  !! Q && P ** TT.
Proof.
  unfold basicasrt.logic_equiv, basicasrt.coq_prop, basicasrt.andp, basicasrt.truep, basicasrt.sepcon;
  split;intros.
  - Destruct H.
    split;auto.
    do 2 eexists. splits;eauto.
  - Destruct H.
    do 2 eexists. splits;eauto.
Qed.
  

Lemma truep_sepcon_elim1 : forall (P: @asrt state),  P |-- TT ** P.
Proof. unfold basicasrt.sepcon,basicasrt.derivable1, basicasrt.truep;intros.
    pose proof unit_join st as (u  & ? & ?).
    apply join_comm in H1.
    do 2 eexists.
    split;eauto.
Qed.

Lemma truep_sepcon_elim2 : forall P,  P |-- P ** TT.
Proof. unfold basicasrt.sepcon,basicasrt.derivable1, basicasrt.truep;intros.
    pose proof unit_join st as (u  & ? & ?).
    do 2 eexists.
    split;eauto.
Qed.

Lemma truep_sepcon_frm_r : forall P Q ,  P ** Q |-- P ** TT.
Proof. unfold basicasrt.sepcon,basicasrt.derivable1, basicasrt.truep;intros.
     Destruct H.
     exists x, x0.
     splits;auto.
Qed.

Lemma truep_sepcon_frm_l : forall P Q ,  P ** Q |-- TT ** Q.
Proof. unfold basicasrt.sepcon,basicasrt.derivable1, basicasrt.truep;intros.
     Destruct H.
     exists x, x0.
     splits;auto.
Qed.

Lemma ex_logic_equiv_sepcon:
  forall {A : Type} (P : A -> expr) (Q : expr),
  (EX y, P y) ** Q  --||-- EX x : A, P x ** Q.
Proof.
  unfold sepcon, logic_equiv, exp, derivable1 ;split;intros;Destruct H.
  - do 3 eexists. split; eauto.
  - do 2 eexists. split;eauto.
Qed.

Lemma all_sepcon1:
  forall (A : Type) (P : A -> @asrt state) (Q :  @asrt state),
  (ALL y, P y) ** Q  |-- ALL x : A, (P x ** Q).
Proof.
  unfold basicasrt.allp, basicasrt.derivable1, basicasrt.sepcon;intros.
  Destruct H.
  do 3 eexists.
  splits;eauto.
  split;eauto.
Qed.
Lemma shallow_allp_right : (forall (A : Type) (P : @asrt state) (Q : A -> @asrt state), (forall x : A, derivable1 P (Q x)) -> derivable1 P (allp Q)) .
Proof. cbv. intros. intuition eauto. Qed.
Lemma shallow_allp_left : (forall (A : Type) (P : A -> @asrt state) (Q : @asrt state) (x : A), derivable1 (P x) Q -> derivable1 (allp P) Q) . 
Proof. cbv. intros.  intuition eauto. Qed.
Lemma sepcon_emp_left : (forall x : @asrt state, derivable1 (sepcon x emp) x) .
Proof.  cbv. intros P * H.
  destruct H as (? & ? & ? & ? & ?).
  eapply unit_spec in H;eauto. subst. auto.
Qed. 

Lemma sepcon_emp_right : (forall x : @asrt state, derivable1 x (sepcon x emp)) .
Proof. cbv. intros P * H.
  destruct (unit_join st) as [? [? ?]].
  exists st, x.
  split;auto.
Qed.

Lemma derivable1_sepcon_comm : (forall x y : @asrt state, derivable1 (sepcon x y) (sepcon y x)) .
Proof. cbv. intros P Q * H.
  destruct H as (? & ? & ? & ? & ?).
  exists x0, x. split;auto. apply join_comm. auto.
Qed.

Lemma derivable1_sepcon_assoc1 : (forall x y z : @asrt state, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
Proof. cbv. intros P Q R * H.
  destruct H as (? & ? & ? & ? & ?).
  destruct H1 as (? & ? & ? & ? & ?).
  apply join_comm in H, H1.
  eapply join_assoc in H;eauto.
  destruct H as (? & ? & ? ).
  apply join_comm in H4.
  exists x3, x2. split;auto. split;auto.
  apply join_comm in H.
  do 2 eexists.
  split;eauto. 
Qed.

Lemma derivable1_sepcon_mono : (forall x1 x2 y1 y2 : @asrt state, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
Proof. cbv. intros P1 P2 Q1 Q2 * He1 He2 * H.
  destruct H as (? & ? & ? & ? & ?).
  specialize (He1 _ H0). specialize (He2 _ H1).
  do 2 eexists.
  split;eauto.
Qed.

Lemma derivable1_wand_sepcon_adjoint : (forall x y z : @asrt state, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) .
Proof. cbv. intros. split; intros.
+ apply H. 
  exists st, st1. split; try split; try tauto.
+ destruct H0 as [st1 [st2 ?]].
  specialize (H st1 (proj1 (proj2 H0)) st2 st).
  apply H; tauto.
Qed.

Lemma sepcon_andp_prop1 : forall (P : @asrt state) (Q : Prop) (R : @asrt state), derivable1 (sepcon P (andp (coq_prop Q) R)) (andp (coq_prop Q) (sepcon P R)).
Proof. cbv;intros.
        destruct H as (? & ? & ? & ? & ? & ?).
        split;auto.
        do 2 eexists. split;eauto. Qed.

Lemma derivable1_sepcon_coq_prop_andp_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon P (andp (coq_prop Q) R))) .
Proof. cbv;intros.
        destruct H as (? & ? & ? & ? & ? & ?).
        do 2 eexists. split;eauto. Qed.


End sepcon_connectives_lemmas.

Ltac st_destruct Σ H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | Σ => let σ := fresh "st" in destruct H as [σ H];st_destruct Σ H
              | _ => destruct H as [? H];st_destruct Σ H
              end
  | (@exp _ ?t ?P) _ => match t with 
              | Σ => let σ := fresh "σ" in destruct H as [σ H];st_destruct Σ H
              | _ => destruct H as [? H];st_destruct Σ H
              end 
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              st_destruct Σ H;
              st_destruct Σ H0
  | _ \/ _ => destruct H as [H | H];
              st_destruct Σ H
  | _ => (discriminate || contradiction  || idtac)
  end.



Ltac one_destruct Σ Prog H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | Σ => let σ := fresh "st" in destruct H as [σ H];one_destruct Σ Prog H
              | Prog => let s := fresh "c" in destruct H as [s H];one_destruct Σ Prog H
              | _ => destruct H as [? H];one_destruct Σ Prog H
              end
  | (@exp _ ?t ?P) _ => match t with 
              | Σ => let σ := fresh "σ" in destruct H as [σ H];one_destruct Σ Prog H
              | Prog => let s := fresh "s" in destruct H as [s H];one_destruct Σ Prog H
              | _ => destruct H as [? H];one_destruct Σ Prog H
              end 
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              one_destruct Σ Prog H;
              one_destruct Σ Prog H0
  | _ \/ _ => destruct H as [H | H];
              one_destruct Σ Prog H
  | _ => (discriminate || contradiction  || idtac)
  end.




