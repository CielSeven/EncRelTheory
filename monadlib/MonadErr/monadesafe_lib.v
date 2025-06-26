Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid. 
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare.

Import Monad MonadNotation SetsNotation.
Local Open Scope sets.
Local Open Scope order_scope.
Import MonadErr.

Definition safe {Σ: Type} {A: Type} (σ : Σ) (c:  program Σ A) (X : A -> Σ -> Prop) := 
    ~ c.(err) σ /\
    forall r σ', c.(nrm) σ r σ' -> (r, σ') ∈ X.  

Definition safeExec {Σ: Type} {A: Type} (P: Σ -> Prop) (c: program Σ A) (X: A -> Σ -> Prop) :=
  exists σₕ, P σₕ /\ safe σₕ c X.

Definition result_state {Σ A: Type} (P: Σ -> Prop) (c: program Σ A): A -> Σ -> Prop :=
  fun a s1 => exists s0, P s0 /\  c.(nrm) s0 a s1.   

Definition hs_eval {Σ: Type}  {A: Type} (c : program Σ A) (P : Σ -> Prop) (P' : (Σ -> Prop)) (a : A) := 
  forall (σₕ : Σ), P σₕ -> exists (σₕ' : Σ), c.(nrm) σₕ a σₕ' /\ P' σₕ'.

(* ⥅  rightarrowplus *)
Notation " P '-@' s '-⥅' P' '♯' a " := (hs_eval s P P' a) (at level 70, no associativity).

Notation " P '-@' s '-→' P' " := (exists a,  hs_eval s P P' a) (at level 70, no associativity).


Import MonadNotation.
Local Open Scope monad.
(**********************************************************************************)
(*    safe exec  rules                                                            *)
(**********************************************************************************)
Ltac splits :=
  match goal with 
  | |- _ /\ _ => split;splits
  | |- _ => idtac end.

Local Ltac my_destruct Σ H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | Σ => let σ := fresh "σₕ" in destruct H as [σ H];my_destruct Σ H
              | program Σ ?A => let c := fresh "c" in destruct H as [c H];my_destruct Σ H
              | _ => destruct H as [? H];my_destruct Σ H
              end
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              my_destruct Σ H;
              my_destruct Σ H0
  | _ \/ _ => destruct H as [H | H];
              my_destruct Σ H
  | _ => (discriminate || contradiction  || idtac)
  end.

Section  safeexec_rules.
  Context {Σ: Type}.

  Definition asrt : Type :=  Σ -> Prop.

  Ltac destructs H := my_destruct Σ H.


  Lemma ret_eq : forall {A : Type} (s: Σ) s0 (a a0: A),
    (ret a).(nrm) s a0 s0 <-> s0 = s /\ a0 = a.
  Proof.
    unfold_monad. intros; tauto.
  Qed.


  Lemma highstependret_derive : forall  {A : Type} (c1: program Σ A)  (P  : Σ -> Prop) a P',
  P -@ c1 -⥅ (P' a) ♯ a ->
  (forall X, safeExec P (c1) X ->  safeExec (P' a) (ret a) X).
  Proof.
    intros.
    unfold hs_eval, safeExec, safe in *.
    destructs H0. 
    simpl in *.
    specialize (H _ H0) as [σₕ' [? ?]].
    exists σₕ'.
    splits;auto.
    intros.
    destruct H4;subst.
    eapply H2;eauto.
  Qed.


  Lemma highstepend_derive : forall  (c1: program Σ unit)  (P  : Σ -> Prop) P',
  P -@ c1 -→ P' ->
  (forall X, safeExec P (c1) X ->  safeExec P' (ret tt) X).
  Proof.
    intros.
    destruct H.
    destruct x.
    pose proof (highstependret_derive c1  P tt ((fun _ => P')) H).
    eapply H1;eauto.
  Qed.

  
  Lemma highstepbind_derive : forall  {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) a P',
  P -@ c1 -⥅ (P') ♯ a ->
  (forall X, safeExec P (x <- c1;; c2 x) X ->  safeExec (P') (c2 a) X).
  Proof.
    intros.
    unfold hs_eval, safeExec, safe in *.
    destructs H0. 
    specialize (H _ H0) as [σₕ' [? ?]].
    exists σₕ'.
    splits;auto.
    eapply bind_noerr_right;eauto.
    intros.
    eapply H2;eauto.
    simpl. do 2 eexists. split;eauto.
  Qed.

  Lemma highstepseq_derive : forall  {A B: Type} (c1: program Σ A) (c2:  program Σ B) (P P': Σ -> Prop),
    P -@ c1 -→ P'  ->
    (forall X, safeExec P (c1 ;; c2) X ->  safeExec P' c2 X).
  Proof.
    intros.
    destruct H.
    unfold seq in H0.
    pose proof (highstepbind_derive c1 (fun _ => c2) P x (P') H).
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
    eexists.
    splits;eauto.
    do 2 eexists.
    split;eauto.
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
    eexists.
    splits;eauto.
    do 2 eexists.
    split;eauto.
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

  Lemma hsevaltestpure_derive:
    forall (P: Σ -> Prop) (Q: Prop) a,
      Q -> P -@ (testPure Q) -⥅ P ♯ a.
  Proof.
    intros.
    unfold hs_eval, testPure. simpl.
    intros.
    eauto.
  Qed.

  Lemma hsevalassert_derive:
    forall (P: Σ -> Prop) (Q: Prop) a,
      Q -> P -@ (assert Q) -⥅ P ♯ a.
  Proof.
    intros.
    unfold hs_eval, assert. simpl.
    intros.
    eauto.
  Qed.

  Lemma safeExec_ex : forall {A B: Type} (P: A -> Σ -> Prop) (c:  program Σ B) X,
  (exists a, safeExec (P a) (c) X) <->  safeExec (fun σ => exists a, P a σ) (c) X.
  Proof.
    unfold safeExec;intros;split;intros.
    - destruct H as (? & ? & ? & ?).
      eexists.
      split;eauto.
    - destruct H as (? & (? & ?) & ?).
      do 2 eexists.
      split;eauto.
  Qed.
  
  Lemma safeExec_X_subset {A: Type} (c: program Σ A) (P: Σ -> Prop) X1 X2:
    X1 ⊆ X2 ->
    safeExec P c X1 ->
    safeExec P c X2.
  Proof.
    unfold safeExec, safe; intros Hx [s [H1 [? H2]]].
    exists s; splits; auto.
    intros a s' H3.
    rewrite <- Hx.
    apply H2; auto.
  Qed.


  Lemma safeExec_proequiv: forall {A : Type} (c1 c2: program Σ A)  (P  : Σ -> Prop) X,
  c1 == c2 ->
  safeExec P c1 X -> safeExec P c2 X.
  Proof.
    unfold safeExec. intros.
    destructs H0.
    eexists.
    split;eauto.
    unfold safe in *. destruct H1.
    split.
    - unfold not in *.
      intros.
      apply H1.
      apply H. auto.
    - 
      intros.
      eapply H2;eauto.
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

  Lemma safeExec_bind : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P : Σ -> Prop) ,
    forall X, safeExec P (x <- c1 ;; c2 x) X ->
    exists X', safeExec P c1 X' /\
    (forall P' a, safeExec P'  (ret a) X' -> 
              safeExec P' (c2 a) X).
  Proof.
    intros.
    unfold safeExec in H.
    destructs H.
    unfold safe in H0.
    destruct H0 as [H0 H0'].
    exists (fun (r : A) (x : Σ) => c1.(nrm) σₕ r x).
    unfold safeExec.
    splits;eauto.
    { eexists.
      split;eauto.
      unfold safe.
      split.
      eapply bind_noerr_left;eauto.
      intros. auto.
    }
    intros.
    destructs H1.
    eexists.
    split;eauto.
    unfold safe in H2; unfold_monad in H2.
    sets_unfold in H2.
    simpl in H2. 
    destruct H2 as [_ H2].
    specialize (H2 a σₕ0  (ltac:(auto))).
    unfold safe.
    intros.
    split.
    eapply bind_noerr_right;eauto.
    intros.
    eapply H0'.
    do 2 eexists.
    split;eauto.
  Qed. 


  Lemma safeExec_conseq: forall {A: Type} (P' P: Σ -> Prop) (c: program Σ A)  X,
    safeExec P c X ->
    (forall s, P s -> P' s) ->
    safeExec P' c X.
  Proof.
    unfold safeExec, safe; intros.
    destruct H as [hs [Ps Hc]].
    exists hs; split; auto.
  Qed.
  

  (* Lemma safeExec_bind' : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P : Σ -> Prop) P',
    (forall X, safeExec P c1 X -> exists a, safeExec P' (ret a) X) ->
    (forall X, safeExec P (x <- c1 ;; c2 x) X -> exists a, safeExec P' (c2 a) X). *)


  Lemma safeExec_test_bind: forall {A: Type} (Q: Prop) (c: program Σ A) P X,
    Q ->
    safeExec P (assume!! Q;; c) X ->
    safeExec P c X.
  Proof.
    intros.
    eapply (highstepbind_derive) with (a:= tt) (P':=  P) in H0; auto.
    unfold hs_eval.
    unfold test; intros.
    simpl.
    exists σₕ; tauto.
  Qed.

  Lemma safeExec_testst_bind: forall {A: Type} (Q: Σ -> Prop) (c: program Σ A) (P: Σ -> Prop) X,
    (forall st, P st -> Q st) ->
    safeExec P (assume Q;; c) X ->
    safeExec P c X.
  Proof.
    unfold safeExec, test, safe.
    unfold_monad.
    intros.
    destruct H0 as [σ [? ?]].
    simpl in H1. unfold nrm_err, nrm_nrm in H1.
    destruct H1.
    exists σ.
    split; [tauto |].
    split.
    - unfold not in *;intros.
      apply H1.
      right.
      do 2 eexists. 
      eauto.
    - intros.
      apply (H2 r σ'); clear H1.
      exists tt, σ.
      sets_unfold.
      split;auto.
  Qed.

  Lemma safeExec_any_bind: forall {A: Type} (Q: Type) (c: Q -> program Σ A) (P: Σ -> Prop) X a,
    safeExec P (a <- any Q;; c a) X ->
    safeExec P (c a) X.
  Proof.
    unfold safeExec, any, safe, seq, bind.
    intros.
    destruct H as [σ [? ?]].
    simpl in H0. unfold nrm_err, nrm_nrm in H0.
    destruct H0.
    exists σ.
    split; [tauto |].
    split.
    - sets_unfold in H0.
      unfold not in *.
      intros. apply H0.
      right.
      eauto.
    - 
      intros.
      apply (H1 r σ').
      exists a, σ.
      sets_unfold.
      splits;auto.
  Qed.

  Lemma safeExec_assert_seq : forall {A: Type}  (B : Prop) (c: program Σ A) (P : Σ -> Prop) ,
    forall X, safeExec P (assert B ;; c) X ->
    B /\ safeExec P c X.
  Proof.
    intros.
    unfold safeExec in H.
    destructs H.
    unfold safe in H0.
    destruct H0 as [H0 H0'].
    cut (B);[ intros;split;auto | ].
    - unfold safeExec.
      eexists.
      split;eauto.
      unfold safe.
      split. 
      { pose proof bind_noerr_right (assert B) (fun (x : unit) => c) _ H0.
        eapply H2 with (a:= tt).
        unfold assert. cbn.  split;eauto. }
      intros.
      eapply H0'.
      exists tt. eexists.
      split;eauto.
      unfold assert. cbn. split;auto.
    - apply bind_noerr_left in H0.
      unfold assert in H0.
      cbn [err] in H0.
      tauto.
  Qed. 

  Lemma safeExec_monad_Atrue_finnal: forall  {A: Type} (m: program unit A),
    ~ m.(err) tt ->
    safeExec ATrue m (fun r x => m.(nrm) tt r x).
  Proof.
    intros.
    unfold safeExec, ATrue, safe.
    exists tt.
    splits;auto.
  Qed.

  Lemma safeExec_ret_Atrue_finnal: forall  {A: Type}  (m: program Σ A) (l : A) (σ: Σ) ,
    safeExec ATrue (ret l) (fun r x => m.(nrm) σ r x) ->
    exists σ', m.(nrm) σ l σ'.
  Proof.
    unfold safeExec,safe; unfold_monad.
    intros.
    destructs H; simpl in H1.
    specialize (H1 l σₕ (ltac:(auto))).
    exists σₕ.
    auto.
  Qed.
  
  Lemma safeExec_choice_l {A: Type}:
    forall (c0 c1: program Σ A) X (s: Σ -> Prop),
      safeExec s (choice c0 c1) X -> safeExec s c0 X.
  Proof.
    intros.
    destruct H as [? [? ?]].
    unfold safe in *.
    unfold choice in H0; simpl in H0.
    exists x; split; auto.
    simpl; split; sets_unfold.
    - intros E.
      sets_unfold in H0; tauto.
    - destruct H0 as [_ H0].
      sets_unfold in H0.
      intros; specialize (H0 r σ').
      tauto.
  Qed.
  
  (* same as choice_l *)
  Lemma safeExec_choice_r {A: Type}:
    forall (c0 c1: program Σ A) X (s: Σ -> Prop),
      safeExec s (choice c0 c1) X -> safeExec s c1 X.
  Proof.
    intros.
    destruct H as [? [? ?]].
    unfold safe in *.
    unfold choice in H0; simpl in H0.
    exists x; split; auto.
    simpl; split; sets_unfold.
    - intros E.
      sets_unfold in H0; tauto.
    - destruct H0 as [_ H0].
      sets_unfold in H0.
      intros; specialize (H0 r σ').
      tauto.
  Qed.

  Lemma safeExec_testpure {A: Type}:
    forall (s: Σ -> Prop) (P: Prop) (c: program Σ A) X,
      P ->
      safeExec s (testPure P;; c) X ->
      safeExec s c X.
  Proof.
    intros; unfold safeExec in *.
    destructs H0.
    exists σₕ.
    split; auto.
    unfold safe in *; split.
    - destruct H1 as [H1 _].
      unfold test in H1; simpl in H1.
      unfold nrm_err in H1.
      sets_unfold in H1.
      intros E.
      apply H1; right.
      exists tt; exists σₕ; tauto.
    - destruct H1 as [_ H1].
      intros.
      specialize (H1 r σ').
      unfold test in H1; simpl in H1.
      unfold nrm_nrm in H1.
      sets_unfold in H1.
      apply H1.
      exists tt; exists σₕ; tauto.
Qed.

End  safeexec_rules.

#[export] Instance safeExec_X_subset_impl_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (eq ==> Sets.included ==> Basics.impl) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros; subst.
  hnf; apply safeExec_X_subset; auto.
Qed.

#[export] Instance safeExec_programequiv_iff_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (equiv ==> eq ==>  iff) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros. subst y0. split. 
  apply safeExec_proequiv. auto.
  apply safeExec_proequiv. symmetry. auto.
Qed.


#[export] Instance hseval_programequiv_Proper
  {Σ: Type} {A: Type}:
  Proper (equiv ==> eq ==> eq ==> eq ==> iff ) (@hs_eval Σ A).
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
  | H: safeExec ?P1 (bind ?c11 ?c12) ?X |- safeExec ?P2 ?c2 ?X =>
      unify (c12 x) c2; 
      refine (highstepbind_derive _ _ _ x P2 _ X H);
      clear H
  end.

Tactic Notation "prove_by_one_abs_step" uconstr(x) :=
  __prove_by_one_abs_step x.

Ltac abs_choice_left :=
  apply hsevalchoice_left_derive.

Ltac abs_choice_right :=
  apply hsevalchoice_right_derive.

Ltac abs_test_step :=
  match goal with
  | |- hs_eval (testPure _) _ _ _ => apply hsevaltestpure_derive
  | |- hs_eval (bind (testPure _) _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltestpure_derive | ]
  | |- hs_eval ((testPure _) ;; _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltestpure_derive | ]
  end.

Ltac abs_assert_step :=
  match goal with
  | |- hs_eval (assert _) _ _ _ => apply hsevalassert_derive
  | |- hs_eval (bind (assert _) _) _ _ _ =>
          refine (hsevalbind_derive _ _ _
                    (fun _ => ATrue) tt (fun _ => ATrue) _ _ _);
          [ apply hsevalassert_derive | ]
  | |- hs_eval ((assert _) ;; _) _ _ _ =>
          refine (hsevalbind_derive _ _ _
                    (fun _ => ATrue) tt (fun _ => ATrue) _ _ _);
          [ apply hsevalassert_derive | ]
  end.

Ltac abs_ret_step :=
  apply highret_eval2.

Ltac safe_step H := prog_nf in H;
  match type of H with
  | safeExec _ ((assert _) ;;  _) _ => apply safeExec_assert_seq in H; destruct H as [? H]; try safe_step H
  | safeExec _ ((testPure _ ) ;;  _) _ => apply safeExec_testpure in H; [try safe_step H | auto]
  end.

Ltac safe_choice_l H :=
  prog_nf in H;apply safeExec_choice_l in H; try safe_step H.

Ltac safe_choice_r H :=
  prog_nf in H;apply safeExec_choice_r in H; try safe_step H.

Ltac safe_equiv :=
  eapply safeExec_proequiv; eauto.  


Section  safeexec_Hoare_composition_rules.
  
  Context {Σ: Type}.

  Ltac destructs H := my_destruct Σ H.

  Lemma safeExec_result_state {A: Type} (P: Σ -> Prop) (c: program Σ A):
    (exists s, P s /\ ~ err c s) ->
    safeExec P c (result_state P c).
  Proof.
    unfold safeExec, result_state, safe.
    intros [s [HP ?]].
    exists s; splits; auto.
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
    safeExec P2 (return a) (c.(nrm) σ) -> 
    σ ∈ P1 ->
    (exists σ', Q a σ' /\ P2 σ').
  Proof.
    unfold Hoare, safeExec, safe.
    intros. 
    destructs H0.
    sets_unfold.
    specialize (H3 a σₕ (ltac:(unfold_monad;auto))).
    destruct H.
    specialize (H a σ _ H1 H3).
    eexists. eauto.
  Qed.
  
End  safeexec_Hoare_composition_rules.

