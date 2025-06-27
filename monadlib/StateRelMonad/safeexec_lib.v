Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
From SetsClass Require Import SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare.
From EncRelSeq.Basics Require Import basictacs basicasrt.
From EncRelSeq.Basics Require Export encdefs.

Import SetsNotation.
Local Open Scope sets_scope.
Local Open Scope asrt_scope.

#[export] Instance staterelmonad_highlevel_defs {Σ A: Type} : highlevel_defs Σ (program Σ A) (A -> Σ -> Prop) := {|
  highlevel_wlp := @weakestpre Σ A
|}.

Import Monad SetsNotation MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Definition result_state {Σ A: Type} (P: Σ -> Prop) (c: program Σ A): A -> Σ -> Prop :=
  fun a s1 => exists s0, P s0 /\ c s0 a s1. 

Definition hs_eval {Σ: Type}  {A: Type} (c : program Σ A) (P : Σ -> Prop) (P' : (Σ -> Prop)) (a : A) := 
  forall (σₕ : Σ), P σₕ -> exists (σₕ' : Σ), c σₕ a σₕ' /\ P' σₕ'.

(* ⥅  rightarrowplus *)
Notation " P '-@' s '-⥅' P' '♯' a " := (hs_eval s P P' a) (at level 70, no associativity).

Notation " P '-@' s '-→' P' " := (exists a,  hs_eval s P P' a) (at level 70, no associativity).

Section  safeexec_rules.
  Context {Σ: Type}.

  Definition asrt : Type :=  Σ -> Prop.

  Ltac destructs H := st_destruct Σ H.
  Lemma ret_eq : forall {A : Type} (s: Σ) s0 (a a0: A),
    (ret a) s a0 s0 <-> s = s0 /\ a0 = a.
  Proof.
    unfold_monad; tauto.
  Qed.

  Lemma hs_eval_equiv_angelic_triple: forall {A : Type} (c1: program Σ A)  (P  : Σ -> Prop) a Q, 
    P -@ c1 -⥅ Q ♯ a <->
    valid_angelic_triple P c1 (fun r σ => r = a /\ Q σ).
  Proof.
    intros.
    unfold hs_eval, valid_angelic_triple. unfold_monad.
    split;intros.
    - specialize (H _ H0) as (? & ? & ?).
      eexists. splits;eauto.
    - specialize (H _ H0) as (? & ? & ? & ? & ?). subst.
      eexists. splits;eauto.
  Qed. 

  Lemma highstependret_derive : forall  {A : Type} (c1: program Σ A)  (P  : Σ -> Prop) a P',
  P -@ c1 -⥅ (P' a) ♯ a ->
  (forall X, Exec P (c1) X ->  Exec (P' a) (ret a) X).
  Proof.
    intros.
    unfold hs_eval, Exec in *; simpl in *. unfold weakestpre in *. 
    destructs H0. 
    simpl in *.
    specialize (H _ H0) as [σₕ' [? ?]].
    exists σₕ'.
    splits;auto.
    intros.
    unfold_monad in H3.
    destruct H3;subst.
    eapply H1;eauto.
  Qed.


  Lemma highstepend_derive : forall  (c1: program Σ unit)  (P  : Σ -> Prop) P',
  P -@ c1 -→ P' ->
  (forall X, Exec P (c1) X ->  Exec P' (ret tt) X).
  Proof.
    intros.
    destruct H.
    destruct x.
    pose proof (highstependret_derive c1  P tt ((fun _ => P')) H).
    eapply H1;eauto.
  Qed.

  Lemma highstepbind_derive : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) a P',
  P -@ c1 -⥅ (P') ♯ a ->
  (forall X, Exec P (x <- c1;; c2 x) X ->  Exec (P') (c2 a) X).
  Proof.
    intros.
    unfold hs_eval, Exec in *; simpl in *. unfold weakestpre in *. 
    destructs H0. 
    simpl in *.
    specialize (H _ H0) as [σₕ' [? ?]].
    exists σₕ'.
    splits;auto.
    intros.
    unfold_monad in H1.
    sets_unfold; sets_unfold in H1.
    eapply H1;eauto.
  Qed.

  Lemma highstepseq_derive : forall  {A B: Type} (c1: program Σ A) (c2:  program Σ B) (P P': Σ -> Prop),
    P -@ c1 -→ P'  ->
    (forall X, Exec P (c1 ;; c2) X ->  Exec P' c2 X).
  Proof.
    intros.
    destruct H.
    unfold_monad in H0.
    pose proof (highstepbind_derive c1 (fun _ => c2) P x ((P')) H).
    eapply H1;eauto.
  Qed. 


  Lemma highret_eval1 : forall {A: Type}  (P  : Σ -> Prop) (a: A), 
    P -@ (ret a) -→ P.
  Proof.
    intros. cbv. intros.
    eexists. splits;eauto.
  Qed.

  Lemma highret_eval2 : forall {A: Type}  (P  : Σ -> Prop) (a: A), 
    P -@ (ret a) -⥅ P ♯ a.
  Proof.
    intros. cbv. intros.
    eexists. splits;eauto.
  Qed.

  Lemma hsevalbind_derive : forall  {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) P' a Q b,
  P -@ c1 -⥅ (P' a) ♯ a ->  (P' a) -@ (c2 a) -⥅ (Q b) ♯ b ->
  P -@ (x  <- c1 ;; c2 x) -⥅ (Q b) ♯ b.
  Proof.
    unfold hs_eval. intros.
    specialize (H _ H1).
    destructs H.
    specialize (H0 _ H2).
    destructs H0.
    unfold_monad.
    sets_unfold.
    eexists.
    splits;eauto.
  Qed.

  Lemma hsevalbind_derive' : forall  {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) P' a Q b,
  P -@ c1 -⥅ P' ♯ a ->  P' -@ (c2 a) -⥅ Q ♯ b ->
  P -@ (x  <- c1 ;; c2 x) -⥅ Q ♯ b.
  Proof.
    unfold hs_eval. intros.
    specialize (H _ H1).
    destructs H.
    specialize (H0 _ H2).
    destructs H0.
    unfold_monad.
    sets_unfold.
    eexists.
    splits;eauto.
  Qed.

  Lemma hsevalchoice_left_derive:
    forall {A: Type} (c1 c2: program Σ A) (P  : Σ -> Prop) Q a,
      P -@ c1 -⥅ Q ♯ a ->
      P -@ (choice c1 c2) -⥅ Q ♯ a.
  Proof.
    intros.
    unfold hs_eval.
    intros.
    specialize (H _ H0) as [? [? ?]].
    eexists.
    split; [left; apply H | apply H1].
  Qed.

  Lemma hsevalchoice_right_derive:
    forall {A: Type} (c1 c2: program Σ A) (P: Σ -> Prop) Q a,
      P -@ c2 -⥅ Q ♯ a ->
      P -@ (choice c1 c2) -⥅ Q ♯ a.
  Proof.
    intros.
    unfold hs_eval.
    intros.
    specialize (H _ H0) as [? [? ?]].
    eexists.
    split; [right; apply H | apply H1].
  Qed.

  Lemma hsevaltest_derive:
    forall (P: Σ -> Prop) (Q: Prop) a,
      Q -> P -@ (assume!! Q ) -⥅ P ♯ a.
  Proof.
    intros.
    unfold hs_eval, test'.
    intros.
    eauto.
  Qed.

  Lemma Exec_ex : forall {A B: Type} (P: A -> Σ -> Prop) (c:  program Σ B) X,
  (exists a, Exec (P a) (c) X) <->  Exec (fun σ => exists a, P a σ) (c) X.
  Proof.
    unfold Exec;simpl;unfold weakestpre;intros;split;intros.
    - destruct H as (? & ? & ? & ?).
      eexists.
      split;eauto.
    - destruct H as (? & (? & ?) & ?).
      do 2 eexists.
      split;eauto.
  Qed. 

  Lemma Exec_prorefine: forall {A : Type} (c1 c2: program Σ A)  (P  : Σ -> Prop) X,
  c2 ⊆ c1 ->
  Exec P c1 X -> Exec P c2 X.
  Proof.
    unfold Exec;simpl;unfold weakestpre; intros.
    destructs H0.
    eexists.
    split;eauto.
    unfold safe in *.
    intros.
    sets_unfold in H.
    eapply H1;eauto.
  Qed.

  Lemma Exec_X_subset {A: Type} (c: program Σ A) (P: Σ -> Prop) X1 X2:
    X1 ⊆ X2 ->
    Exec P c X1 ->
    Exec P c X2.
  Proof.
    unfold Exec;simpl;unfold weakestpre; intros Hx [s [H1 H2]].
    exists s; split; auto.
    intros a s' H3.
    apply Hx.
    apply H2; auto.
  Qed.

  Lemma Exec_proequiv: forall {A : Type} (c1 c2: program Σ A)  (P  : Σ -> Prop) X,
    c1 == c2 ->
    Exec P c1 X -> Exec P c2 X.
  Proof.
    unfold Exec;simpl;unfold weakestpre; intros.
    destructs H0.
    eexists.
    split;eauto.
    unfold safe in *.
    intros.
    sets_unfold in H.
    eapply H1;eauto.
    eapply H;eauto.
  Qed.

  Lemma hs_eval_proequiv: forall {A : Type} (c1 c2: program Σ A)  (P  Q: Σ -> Prop) a,
  c1 == c2 ->
  P -@ c1 -⥅ Q ♯ a ->
  P -@ c2 -⥅ Q ♯ a.
  Proof.
    unfold hs_eval. intros.
    specialize (H0 _ H1).
    destructs H0.
    eexists.
    split;eauto.
    eapply H;eauto.
  Qed.

  Lemma Exec_bind : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P : Σ -> Prop) ,
    forall X, Exec P (x <- c1 ;; c2 x) X ->
    exists X', Exec P c1 X' /\
    (forall P' a, Exec P'  (ret a) X' -> 
              Exec P' (c2 a) X).
  Proof.
    intros.
    unfold Exec in H. simpl_hdefs.
    destructs H.
    unfold weakestpre in H0.
    exists (fun (r : A) (x : Σ) => c1 st r x).
    unfold Exec. simpl_hdefs;unfold weakestpre. sets_unfold.
    splits;eauto.
    { eexists.
      split;eauto.
      unfold safe.
      intros. auto.
    }
    intros.
    destructs H1.
    eexists.
    split;eauto.
    unfold_monad in H2.
    specialize (H2 a st0 (ltac:(auto))).
    unfold safe.
    intros.
    eapply H0.
    unfold_monad.
    sets_unfold; sets_unfold in H0; sets_unfold; sets_unfold in H2.
    do 2 eexists.
    split;eauto.
  Qed. 

  Lemma Exec_bind_high {A B: Type}: forall a (Q: A -> Σ -> Prop) (P : Σ -> Prop) (c1: program Σ A) (c2: A -> program Σ B) X,
    Exec P (x <- c1;; c2 x) X ->
    (forall s1, P s1 -> exists s2, c1 s1 a s2 /\ Q a s2) ->
    Exec (Q a) (c2 a) X.
  Proof.
    unfold Exec;simpl_hdefs;unfold weakestpre; unfold_monad; sets_unfold; intros.
    destruct H as [s [HP Hs]].
    specialize (H0 s HP); destruct H0 as [s1 [Hc1 Qs2]].
    exists s1; split; auto.
    intros b s2 Hc2.
    apply Hs.
    exists a, s1; tauto.
  Qed.

  Lemma Exec_bind_unit {B: Type}: forall (Q: Σ -> Prop) (P : Σ -> Prop) (c1: program Σ unit) (c2:program Σ B) X,
    Exec P (c1;; c2) X ->
    (forall s1, P s1 -> exists s2, c1 s1 tt s2 /\ Q s2) ->
    Exec Q c2 X.
  Proof.
    unfold Exec;simpl_hdefs;unfold weakestpre; unfold_monad; sets_unfold; intros.
    destruct H as [s [HP Hs]].
    specialize (H0 s HP); destruct H0 as [s1 [Hc1 Qs2]].
    exists s1; split; auto.
    intros b s2 Hc2.
    apply Hs.
    exists tt, s1; tauto.
  Qed.

  Lemma Exec_conseq: forall {A: Type} (P' P: Σ -> Prop) (c: program Σ A)  X,
    Exec P c X ->
    (forall s, P s -> P' s) ->
    Exec P' c X.
  Proof.
    unfold Exec;simpl_hdefs;unfold weakestpre;sets_unfold; intros.
    destruct H as [hs [Ps Hc]].
    exists hs; split; auto.
  Qed.
  
  (* Lemma Exec_bind'  : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P : Σ -> Prop) P',
    (forall X, Exec P c1 X -> exists a, Exec (P')  (ret a) X) ->
    (forall X, Exec P (x <- c1 ;; c2 x) X -> exists a, Exec (P') (c2 a) X). *)

  Lemma Exec_choice_left: forall {A: Type} (c1 c2: program Σ A) P X,
    Exec P (choice c1 c2) X ->
    Exec P c1 X.
  Proof.
    unfold Exec, choice;simpl_hdefs;unfold weakestpre;sets_unfold.
    intros.
    destruct H as [σ [? ?]].
    exists σ.
    split; [tauto | ].
    intros.
    specialize (H0 r σ' ltac:(left; tauto)).
    tauto.
  Qed.

  Lemma Exec_choice_right: forall {A: Type} (c1 c2: program Σ A) P X,
    Exec P (choice c1 c2) X ->
    Exec P c2 X.
  Proof.
    unfold Exec, choice;simpl_hdefs;unfold weakestpre;sets_unfold.
    intros.
    destruct H as [σ [? ?]].
    exists σ.
    split; [tauto | ].
    intros.
    specialize (H0 r σ' ltac:(right; tauto)).
    tauto.
  Qed.

  Lemma Exec_test_bind: forall {A: Type} (Q: Prop) (c: program Σ A) P X,
    Q ->
    Exec P (assume!! Q ;; c) X ->
    Exec P c X.
  Proof.
    intros.
    eapply (Exec_bind_high tt (fun _ => P)) in H0; auto.
    unfold test'; intros.
    exists s1; tauto.
  Qed.

  Lemma Exec_testst_bind: forall {A: Type} (Q: Σ -> Prop) (c: program Σ A) (P: Σ -> Prop) X,
    (forall st, P st -> Q st) ->
    Exec P (assume Q;; c) X ->
    Exec P c X.
  Proof.
    unfold Exec, test, bind;simpl_hdefs;unfold weakestpre;sets_unfold.
    intros.
    destruct H0 as [σ [? ?]].
    exists σ.
    split; [tauto | ].
    intros.
    apply (H1 r σ').
    exists tt, σ.
    sets_unfold.
    splits;auto.
  Qed.

  Lemma Exec_any_bind: forall {A: Type} (Q: Type) (c: Q -> program Σ A) (P: Σ -> Prop) X a,
    Exec P (a <- any Q;; c a) X ->
    Exec P (c a) X.
  Proof.
    unfold Exec, any, bind;simpl_hdefs;unfold weakestpre;sets_unfold.
    intros.
    destruct H as [σ [? ?]].
    exists σ.
    split; [tauto | ].
    intros.
    apply (H0 r σ').
    exists a, σ.
    sets_unfold.
    splits;auto.
  Qed.

  Lemma Exec_get_bind {A B: Type} (a: A) (Pa: Σ -> A -> Prop) (P: Σ -> Prop) (c: A -> program Σ B) X:
    (forall s, P s -> Pa s a) ->
    Exec P (a0 <- get Pa;; c a0) X ->
    Exec P (c a) X.
  Proof.
    intros.
    apply ( Exec_bind_high  a (fun _ => P)) in H0; auto.
    intros; unfold get.
    exists s1; split; auto.
  Qed.

  Lemma Exec_update'_bind {B: Type} (f: Σ -> Σ) (P: Σ -> Prop) (c:program Σ B) X:
    Exec P (update' f;; c) X ->
    Exec (fun s => exists s0, s = f s0 /\ P s0) c X.
  Proof.
    intros.
    eapply Exec_bind_unit; eauto.
    unfold update', update; intros.
    exists (f s1).
    split; auto.
    exists s1; tauto.
  Qed.

  Lemma Exec_bind_rightsubst : forall {A B: Type} (c1: program Σ A) (c2 c2': A -> program Σ B) (P : Σ -> Prop) X X',
    (forall σ a, safe σ (c2 a) X -> safe σ (c2' a) X') ->
    (Exec P (x <- c1 ;; c2 x) X -> Exec P (x <- c1 ;; c2' x) X').
  Proof.
    unfold Exec, safe;simpl_hdefs;unfold weakestpre;sets_unfold.
    unfold_monad.
    intros.
    destructs H0.
    eexists.
    split;eauto.
    intros.
    destruct H2 as (a  & σ'' & ? & ?).
    sets_unfold;
    sets_unfold in H; sets_unfold in H1;
    sets_unfold in H2; sets_unfold in H3.
    eapply H; eauto.
  Qed.

  Lemma Exec_subst : forall {A: Type} (c1 c1': program Σ A)  (P : Σ -> Prop) X X',
    (forall σ, safe σ c1 X -> safe σ c1' X') ->
    (Exec P (c1) X -> Exec P (c1') X').
  Proof.
    unfold Exec, safe.
    intros.
    destructs H0.
    eexists.
    split;eauto.
  Qed.

  Lemma Exec_monad_Atrue_finnal: forall  {A: Type} (m: program unit A) ,
    Exec ATrue m (fun r x => m tt r x).
  Proof.
    intros.
    unfold Exec, ATrue;simpl_hdefs;unfold weakestpre;sets_unfold.
    exists tt.
    splits;auto.
  Qed.

  Lemma Exec_ret_Atrue_finnal: forall  {A: Type}  (m: program Σ A) (l : A) (σ: Σ) ,
    Exec ATrue (ret l) (fun r x => m σ r x) ->
    exists σ', m σ l σ'.
  Proof.
    unfold Exec, ATrue;simpl_hdefs;unfold weakestpre;sets_unfold.
    intros.
    destructs H.
    specialize (H0 l st (ltac:(unfold_monad;auto))).
    exists st.
    auto.
  Qed.

  Lemma Exec_choice_l {A: Type}:
    forall (c0 c1: program Σ A) X (s: Σ -> Prop),
      Exec s (choice c0 c1) X -> Exec s c0 X.
  Proof.
    unfold Exec;simpl_hdefs;unfold weakestpre.
    intros.
    destruct H as [? [? ?]].
    unfold safe in *.
    unfold choice in H0; simpl in H0.
    exists x; split; auto.
    simpl; sets_unfold.
    unfold safe.
    sets_unfold in H0.
    intros; specialize (H0 r σ').
    tauto.
  Qed.
  
  (* same as choice_l *)
  Lemma Exec_choice_r {A: Type}:
    forall (c0 c1: program Σ A) X (s: Σ -> Prop),
      Exec s (choice c0 c1) X -> Exec s c1 X.
  Proof.
    unfold Exec;simpl_hdefs;unfold weakestpre.
    intros.
    destruct H as [? [? ?]].
    unfold safe in *.
    unfold choice in H0; simpl in H0.
    exists x; split; auto.
    simpl;  sets_unfold.
    sets_unfold in H0.
    unfold safe.
    intros; specialize (H0 r σ').
    tauto.
  Qed.

  Lemma Exec_test' {A: Type}:
    forall (s: Σ -> Prop) (P: Prop) (c: program Σ A) X,
      P ->
      Exec s (test' P;; c) X ->
      Exec s c X.
  Proof.
    unfold Exec;simpl_hdefs;unfold weakestpre.
    intros.
    destructs H0.
    exists st.
    split; auto.
    sets_unfold.
    intros.
    specialize (H1 r σ').
    unfold test' in H1; simpl in H1.
    unfold_monad in H1.
    sets_unfold in H1.
    apply H1.
    exists tt; exists st; tauto.
  Qed.

  Lemma hseval_stateless_ret: forall  {A: Type}  (m: program unit A) (a : A),
    m tt a tt ->
    ATrue -@ m -⥅ ATrue ♯ a.
  Proof.
    intros. hnf. 
    exists tt.
    destruct σₕ.
    easy.
  Qed.
  
  Lemma Exec_ret {A: Type} a (P: Σ -> Prop) (X: A -> Σ -> Prop):
    Exec P (ret a) X ->
    exists s, P s /\ (a, s) ∈ X.
  Proof.
    unfold Exec;simpl_hdefs;unfold weakestpre. unfold_monad.
    intros [s [? ?]].
    specialize (H0 a s).
    exists s; tauto.
  Qed.

  Lemma Exec_ret_tt (P: Σ -> Prop) (X: Σ -> Prop):
    Exec P (ret tt) (fun _ => X) ->
    exists s, P s /\  X s.
  Proof.
    intros; apply Exec_ret in H.
    sets_unfold in H; auto.
  Qed.

End  safeexec_rules.

#[export] Instance Exec_programrefine_impl_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (Sets.included ==> eq ==> (Basics.flip Basics.impl)) (@Exec Σ (program Σ A) _ _ P).
Proof.
  unfold Proper, respectful.
  intros. subst y0.
  hnf.
  apply Exec_prorefine;eauto.
Qed.

#[export] Instance Exec_X_subset_impl_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (eq ==> Sets.included ==> Basics.impl) (@Exec Σ (program Σ A) _ _ P).
Proof.
  unfold Proper, respectful.
  intros; subst.
  hnf; apply Exec_X_subset; auto.
Qed.

#[export] Instance Exec_programequiv_iff_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (Sets.equiv ==> eq ==>  iff) (@Exec Σ (program Σ A) _ _ P).
Proof.
  unfold Proper, respectful.
  intros. subst y0. split. 
  apply Exec_proequiv. auto.
  apply Exec_proequiv. symmetry. auto.
Qed.

#[export] Instance Exec_programequiv_iff_Proper'
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (Sets.equiv ==> eq ==>  iff) (@Exec Σ (program Σ A) _ _ P).
Proof.
  unfold Proper, respectful.
  intros. subst y0. split. 
  apply Exec_proequiv. auto.
  apply Exec_proequiv. symmetry. auto.
Qed.

#[export] Instance hseval_programequiv_Proper
  {Σ: Type} {A: Type}:
  Proper (Sets.equiv ==> eq ==> eq ==> eq ==> iff ) (@hs_eval Σ A).
Proof.
  unfold Proper, respectful.
  intros. subst y0 y1 y2. split.
  apply hs_eval_proequiv. auto.
  apply hs_eval_proequiv. symmetry. auto.
Qed.

#[export] Instance hseval_programequiv_Proper'
  {Σ: Type} {A: Type}:
  Proper (Sets.equiv ==> eq ==> eq ==> eq ==> iff ) (@hs_eval Σ A).
Proof.
  unfold Proper, respectful.
  intros. subst y0 y1 y2. split.
  apply hs_eval_proequiv. auto.
  apply hs_eval_proequiv. symmetry. auto.
Qed.

Lemma  program_para_equiv {Σ: Type} {A B: Type}: forall 
  (f1 f2: A -> program Σ B),
  f1 == f2 -> forall x, f1 x == f2 x.
Proof.
  intros.
  apply H.
Qed.

Arguments program_para_equiv {Σ} {A B}%type_scope [f1] [f2].

Ltac __prove_by_one_abs_step x :=
  match goal with
  | H: Exec ?P1 (bind ?c11 ?c12) ?X |- Exec ?P2 ?c2 ?X =>
      unify (c12 x) c2; 
      refine (highstepbind_derive _ _ _ x P2 _ X H);
      clear H
  end.

Tactic Notation "prove_by_one_abs_step" uconstr(x) :=
  __prove_by_one_abs_step x.

Ltac abs_choice_left :=
  prog_nf;apply hsevalchoice_left_derive.

Ltac abs_choice_right :=
  prog_nf;apply hsevalchoice_right_derive.

Ltac abs_test_step :=
  match goal with
  | |- hs_eval (test' _) _ _ _ => apply hsevaltest_derive
  | |- hs_eval (bind (test' _) _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltest_derive | ]
  | |- hs_eval ((test' _) ;; _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltest_derive | ]
  end.

Ltac abs_ret_step :=
  apply highret_eval2.

Ltac safe_step H := prog_nf in H;
  match type of H with
  | Exec _ ((test' _ ) ;; _) _ => apply Exec_test' in H; [try safe_step H | auto]
  end.

Ltac safe_choice_l H :=
  prog_nf in H;apply Exec_choice_l in H; try safe_step H.

Ltac safe_choice_r H :=
  prog_nf in H;apply Exec_choice_r in H; try safe_step H.

Ltac safe_equiv :=
  eapply Exec_proequiv; eauto.  


Section  safeexec_Hoare_composition_rules.
  
  Context {Σ: Type}.

  Ltac destructs H := st_destruct Σ H.
  Lemma Exec_result_state {A: Type} (P: Σ -> Prop) (c: program Σ A):
    (exists s, P s) ->
    Exec P c (result_state P c).
  Proof.
    unfold Exec, result_state, safe.
    intros [s HP].
    exists s; split; auto.
    sets_unfold; intros a s' ?.
    exists s; tauto.
  Qed.

  Lemma Hoare_result_state {A: Type} (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop):
    Hoare P c Q ->
    result_state P c ⊆ Q.
  Proof.
    unfold Hoare, result_state; sets_unfold; intros.
    destruct H0 as [s0 [? ?]].
    eapply H; eauto.
  Qed.

  Lemma Hoare_safeexec_compose {A: Type} (P1 : Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop):
    Hoare P1 c Q ->
    forall (P2: Σ -> Prop) (a: A) (σ : Σ),
    Exec P2 (return a) (c σ) -> 
    σ ∈ P1 ->
    (exists σ', Q a σ' /\ P2 σ').
  Proof.
    unfold Hoare, Exec;simpl_hdefs;unfold weakestpre.
    intros. 
    destructs H0.
    sets_unfold.
    specialize (H2 a st (ltac:(unfold_monad;auto))).
    specialize (H σ _ _ H1 H2).
    eexists. eauto.
  Qed.

End  safeexec_Hoare_composition_rules.
