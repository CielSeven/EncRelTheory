Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import MonadLib.StateRelMonad.StateRelBasic.
Require Import Coq.Lists.List.
Import SetsNotation.
From FP Require Import SetsFixedpoints.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Definition Hoare {Σ A: Type}
  (P: Σ -> Prop)
  (c: program Σ A)
  (Q: A -> Σ -> Prop): Prop := 
    forall s1 a s2, P s1 -> (s1, a, s2) ∈ c -> Q a s2.

Theorem Hoare_bind {Σ A B: Type}:
  forall (P: Σ -> Prop)
         (f: program Σ A)
         (Q: A -> Σ -> Prop)
         (g: A -> program Σ B)
         (R: B -> Σ -> Prop),
  Hoare P f Q ->
  (forall a, Hoare (Q a) (g a) R) ->
  Hoare P (bind f g) R.
Proof.
  intros.
  unfold Hoare, bind; simpl; sets_unfold; unfold StateRelMonad.bind.
  intros s1 b s3 ? [a [s2 [? ?]]].
  pose proof H _ _ _ H1 H2.
  pose proof H0 a _ _ _ H4 H3.
  tauto.
Qed.

Theorem Hoare_ret {Σ A: Type}:
  forall (P: A -> Σ -> Prop) (a0: A),
    Hoare (P a0) (ret a0) P.
Proof.
  intros.
  unfold Hoare, ret; simpl; sets_unfold; unfold StateRelMonad.ret.
  intros.
  destruct H0; subst; tauto.
Qed.

Theorem Hoare_step {Σ A: Type}:
  forall (P: Σ -> Prop) (f: program Σ A),
    Hoare P f (fun a s2 => exists s1, f s1 a s2 /\ P s1).
Proof.
  intros.
  unfold Hoare; simpl; sets_unfold; intros.
  eexists; eauto.
Qed.

Theorem Hoare_choice {Σ A: Type}:
  forall P (f g: program Σ A) Q,
    Hoare P f Q -> 
    Hoare P g Q ->
    Hoare P (choice f g) Q.
Proof.
  intros.
  unfold Hoare, choice; sets_unfold.
  intros ? ? ? ? [? | ?].
  + pose proof H _ _ _ H1 H2.
    tauto.
  + pose proof H0 _ _ _ H1 H2.
    tauto.
Qed.

Theorem Hoare_assume_bind {Σ A: Type}:
  forall P (Q: Σ -> Prop) (f: program Σ A) R,
    Hoare (fun s => Q s /\ P s) f R -> 
    Hoare P (assume Q;; f) R.
Proof.
  intros.
  eapply Hoare_bind; [| intros; apply H].
  unfold Hoare, test; sets_unfold.
  intros s1 _ s2 ? [? ?].
  subst; tauto.
Qed.

Theorem Hoare_assume {Σ: Type}:
  forall (P Q: Σ -> Prop),
    Hoare P (assume Q) (fun _ s => P s /\ Q s).
Proof.
  intros.
  unfold Hoare, test; sets_unfold.
  intros s1 _ s2 ? [? ?].
  subst; tauto.
Qed.

Theorem Hoare_assume' {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Prop),
    Hoare P (assume!! Q ) (fun _ s => P s /\ Q).
Proof.
  intros.
  unfold Hoare, test; sets_unfold.
  intros s1 _ s2 ? [? ?].
  subst; tauto.
Qed.

Theorem Hoare_assume_bind' {Σ A: Type}:
  forall P (Q: Prop) (f: program Σ A) R,
    (Q -> Hoare P f R)-> 
    Hoare P (assume!! Q ;; f) R.
Proof.
  intros; revert H.
  unfold Hoare, test, bind; simpl. 
  unfold StateRelMonad.bind; sets_unfold.
  intros.
  firstorder; subst.
  specialize (H x0 a s2).
  tauto.
Qed.

Theorem Hoare_any {Σ A: Type}:
  forall (P: Σ -> Prop),
    Hoare P (any A) (fun _ => P).
Proof.
  unfold Hoare, any; sets_unfold.
  intros.
  subst; tauto.
Qed.

Theorem Hoare_any_bind {Σ A B: Type}:
  forall (P: Σ -> Prop) (f: A -> program Σ B) (Q: B -> Σ -> Prop),
    (forall a, Hoare P (f a) Q) ->
    Hoare P (a <- any A;; f a) Q.
Proof.
  intros.
  eapply Hoare_bind.
  apply Hoare_any.
  simpl; auto.
Qed.

Theorem Hoare_get {A Σ: Type}:
  forall (P: Σ -> Prop) (Pa: Σ -> A -> Prop),
    Hoare P (get Pa) (fun a s2 => Pa s2 a /\ P s2).
Proof.
  unfold Hoare, get; sets_unfold; intros.
  destruct H0; subst; tauto.
Qed.

Theorem Hoare_update {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Σ -> Σ -> Prop),
    Hoare P (update Q) (fun a s2 => exists s1, Q s1 s2 /\ P s1).
Proof.
  intros.
  unfold update.
  apply Hoare_step.
Qed.

Theorem Hoare_conseq {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    (forall s, P1 s -> P2 s) ->
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare P2 f Q2 ->
    Hoare P1 f Q1.
Proof.
  intros.
  unfold Hoare.
  intros.
  apply H0.
  apply (H1 s1 a s2).
  + apply H; tauto.
  + tauto.
Qed.

Theorem Hoare_conseq_pre {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall s, P1 s -> P2 s) ->
    Hoare P2 f Q ->
    Hoare P1 f Q.
Proof.
  intros.
  unfold Hoare.
  intros.
  apply (H0 s1 a s2).
  + apply H; tauto.
  + tauto.
Qed.

Theorem Hoare_conseq_post {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare P f Q2 ->
    Hoare P f Q1.
Proof.
  intros.
  unfold Hoare.
  intros.
  apply H.
  apply (H0 s1 a s2); tauto.
Qed.

Theorem Hoare_conj {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    Hoare P f Q1 ->
    Hoare P f Q2 ->
    Hoare P f (fun a s => Q1 a s /\ Q2 a s).
Proof.
  intros.
  unfold Hoare; intros.
  split.
  + apply (H _ _ _ H1 H2).
  + apply (H0 _ _ _ H1 H2).
Qed.

Theorem Hoare_disj {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q: A -> Σ -> Prop),
    Hoare P1 f Q ->
    Hoare P2 f Q ->
    Hoare (fun s => P1 s \/ P2 s) f Q.
Proof.
  intros; unfold Hoare; intros.
  destruct H1.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed. 

Theorem Hoare_forall {Σ A: Type}:
  forall (X: Type) (P: Σ -> Prop) f (Q: X -> A -> Σ -> Prop),
    (forall x, Hoare P f (Q x)) ->
    Hoare P f (fun a s => forall x, Q x a s).
Proof.
  intros.
  unfold Hoare.
  intros.
  apply (H x _ _ _ H0 H1).
Qed.

Theorem Hoare_pre_ex {Σ A: Type}:
  forall (X: Type) (P: X -> Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall x, Hoare (P x) f Q) ->
    Hoare (fun s => exists x, P x s) f Q.
Proof.
  intros.
  unfold Hoare.
  intros s1 a s2 [x ?] ?.
  apply (H x _ _ _ H0 H1).
Qed.

Theorem hoare_bind_forall {Σ A: Type}:
  forall (X: Type) (P: Σ -> Prop) f (Q: X -> A -> Σ -> Prop),
    (forall x, Hoare P f (Q x)) <->
    Hoare P f (fun r s => forall x, Q x r s).
Proof.
  intros.
  unfold Hoare; sets_unfold; split; intros.
  - apply (H _ s1); auto.
  - apply (H s1); auto.
Qed.

Theorem Hoare_ret' {Σ A: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (a0: A),
    (forall s, P s -> Q a0 s) ->
    Hoare P (ret a0) Q.
Proof.
  intros.
  unfold Hoare, ret; simpl; sets_unfold; unfold StateRelMonad.ret.
  intros.
  destruct H1; subst.
  apply H. tauto.
Qed.

Definition continue_case {Σ A B: Type} : CntOrBrk A B -> program Σ A :=
  fun x =>
    match x with
    | by_continue a => ret a
    | by_break _ => ∅
    end.

Definition break_case {Σ A B: Type} : CntOrBrk A B -> program Σ B :=
  fun x =>
    match x with
    | by_continue _ => ∅
    | by_break b => ret b
    end.
  
Lemma Hoare_sum {Σ A B: Type}:
  forall (P: Σ -> Prop) (c: program Σ (CntOrBrk A B)) (Q: A -> Σ -> Prop) (R: B -> Σ -> Prop),
    Hoare P (x <- c;; continue_case x) Q ->
    Hoare P (x <- c;; break_case x) R ->
    Hoare P c (fun x s => match x with
                          | by_continue a => Q a s
                          | by_break b => R b s
                          end).
Proof.
  unfold Hoare in *; intros.
  destruct a.
  - specialize (H s1 a s2 H1).
    apply H; clear H.
    unfold bind; simpl.
    unfold StateRelMonad.bind; sets_unfold.
    exists (by_continue a); exists s2.
    simpl; unfold ret; simpl; unfold StateRelMonad.ret; simpl.
    sets_unfold in H2; tauto.
  - specialize (H0 s1 b s2 H1).
    apply H0; clear H0.
    unfold bind; simpl.
    unfold StateRelMonad.bind; sets_unfold.
    exists (by_break b); exists s2.
    simpl; unfold ret; simpl; unfold StateRelMonad.ret; simpl.
    sets_unfold in H2; tauto.
Qed.

Lemma Hoare_empty {Σ A: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    Hoare P ∅ Q.
Proof.
  unfold Hoare; sets_unfold; tauto.
Qed.

Lemma Hoare_cnt_cnt {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (a: A),
    (forall s, P s -> Q a s) ->
    Hoare P (@continue_case Σ A B (by_continue a)) Q.
Proof.
  intros.
  unfold Hoare, continue_case; unfold_monad; sets_unfold.
  intros.
  destruct H1; subst; auto.
Qed.

Lemma Hoare_brk_brk {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: B -> Σ -> Prop) (b: B),
    (forall s, P s -> Q b s) ->
    Hoare P (@break_case Σ A B  (by_break b)) Q.
Proof.
  intros.
  unfold Hoare, break_case; unfold_monad; sets_unfold.
  intros.
  destruct H1; subst; auto.
Qed.

Lemma Hoare_brk_cnt {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: B -> Σ -> Prop) (a: A),
    Hoare P (@break_case Σ A B  (by_continue a)) Q.
Proof.
  intros.
  unfold Hoare, break_case; simpl.
  intros; tauto.
Qed.

Lemma Hoare_cnt_brk {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (b: B),
    Hoare P (@continue_case Σ A B (by_break b)) Q.
Proof.
  intros.
  unfold Hoare, continue_case; simpl.
  intros; tauto.
Qed.

Lemma Hoare_proequiv:
  forall {A Σ: Type} (c1 c2: program Σ A) (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    c1 == c2 ->
    Hoare P c1 Q -> Hoare P c2 Q.
Proof.
  unfold Hoare; intros.
  specialize (H0 s1 a s2 H1).
  rewrite H in H0.
  auto.
Qed.

Lemma Hoare_skip:
  forall {A Σ B} P (c: program Σ A) (f: A -> program Σ B) Q,
    (forall a, Hoare (fun _ => True) (f a) Q) ->
    Hoare P (bind c f) Q.
Proof.
  unfold Hoare; intros.
  sets_unfold in H1.
  unfold bind in H1; simpl in H1.
  unfold StateRelMonad.bind in H1.
  destruct H1 as (? & ? & ? & ?).
  specialize (H x x0 a s2 I).
  tauto.
Qed.

Lemma Hoare_stateless:
  forall {A Σ} (P: Prop) (c: program Σ A) Q,
    (P -> Hoare (fun _ => True) c Q) ->
    Hoare (fun _ => P) c Q.
Proof.
  unfold Hoare; intros.
  sets_unfold; intros.
  eapply H; eauto.
Qed.

Lemma Hoare_stateless':
  forall {A Σ} (P: Prop) (P': Σ -> Prop) (c: program Σ A) Q,
    (P -> Hoare P' c Q) <->
    Hoare (fun s => P' s /\ P) c Q.
Proof.
  unfold Hoare; intros.
  sets_unfold; intros.
  split; intros.
  - eapply H; eauto; tauto.
  - eapply H; eauto.
Qed.

Theorem Hoare_update_bind {Σ A: Type}:
  forall (P: Σ -> Prop) (f: Σ -> Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall s1,  P s1 -> Hoare (fun s2 => f s1 s2) c Q) ->
    Hoare P (update f;; c) Q.
Proof.
  intros.
  eapply Hoare_bind.
  apply Hoare_update.
  simpl.
  intros _.
  apply Hoare_pre_ex.
  intros.
  apply Hoare_stateless'.
  apply H.
Qed.

#[export] Instance Hoare_programequiv_iff_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (Sets.equiv ==> eq ==> iff) (@Hoare Σ A P).
Proof.
  unfold Proper, respectful; intros.
  subst x0; split; intros.
  - apply Hoare_proequiv with x; easy.
  - apply Hoare_proequiv with y; easy.
Qed.

Lemma Hoare_equiv_iff {Σ A: Type}:
  forall (P: Σ -> Prop) (c1 c2: program Σ A) (Q: A -> Σ -> Prop),
    c1 == c2 ->
    Hoare P c1 Q <-> Hoare P c2 Q.
Proof.
  intros; rewrite H; easy.
Qed.

(** Hoare rules with the state introed  *)

Lemma Hoare_state_intro {A Σ}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall s0, P s0 -> Hoare (fun s => s = s0) c Q)->
    Hoare P c Q.
Proof.
  unfold Hoare; intros.
  eapply H; eauto.
Qed.

Lemma Hoare_step_s {A Σ}:
  forall (s0: Σ) (c: program Σ A),
    Hoare (fun s => s = s0) c (fun a s1 => c s0 a s1).
Proof.
  unfold Hoare; intros.
  subst; auto.
Qed.

Lemma Hoare_update_s {Σ}:
  forall (s0: Σ) (f: Σ -> Σ -> Prop),
    Hoare (fun s => s = s0) (update f) (fun _ s1 => f s0 s1).
Proof.
  unfold Hoare; intros.
  subst; auto.
Qed.

Lemma Hoare_update' {Σ}:
  forall (s0: Σ) (f: Σ -> Σ),
    Hoare (fun s => s = s0) (update' f) (fun _ s1 => s1 = f s0).
Proof.
  unfold Hoare; intros.
  subst; auto.
Qed.

Lemma Hoare_assume_s {Σ}:
  forall (s0: Σ) (Q: Σ -> Prop),
    Hoare (fun s => s = s0) (assume Q) (fun _ s1 => s1 = s0 /\ Q s0).
Proof.
  intros.
  eapply Hoare_conseq_post.
  2:apply Hoare_assume.
  simpl; intros.
  destruct H; subst; tauto.
Qed.

Lemma Hoare_get_s {Σ A}:
  forall (s0: Σ) (Pa: Σ -> A -> Prop),
    Hoare (fun s => s = s0) (get Pa) (fun a s1 => s1 = s0 /\ Pa s0 a).
Proof.
  unfold Hoare; intros.
  unfold get in H0; sets_unfold in H0.
  destruct H0; subst; tauto.
Qed.

Lemma Hoare_get' {Σ A}:
  forall (s0: Σ) (fa: Σ -> A),
    Hoare (fun s => s = s0) (get' fa) (fun a s1 => s1 = s0 /\ a = fa s0).
Proof.
  unfold Hoare; intros.
  unfold get' in H0; sets_unfold in H0.
  destruct H0; subst; tauto.
Qed.
  
(** Hoare Tactics *)

Tactic Notation "hoare_bind" uconstr(H) :=
  eapply Hoare_bind; [eapply H |]; intros.

(* for unit type *)
Tactic Notation "hoare_bind'" uconstr(H) :=
  eapply Hoare_bind; [eapply H |]; simpl; intros _.

Ltac hoare_conj :=
  match goal with
    | |- Hoare _  _ (fun _ _ => _ /\ _) => apply Hoare_conj; [try hoare_conj | try hoare_conj]
  end.

Ltac hoare_intros :=
  apply Hoare_pre_ex; intros.

Ltac stateless_intros :=
  repeat (apply Hoare_stateless'; intros);
  try apply Hoare_stateless; intros.

Ltac intro_state :=
  apply Hoare_state_intro; intros.

Ltac hoare_step :=
  unfold continue, break, If, if_else;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_step
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_step
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_left 
    | |- Hoare _ (bind (any _) _) _ => apply Hoare_any_bind; intros
    | |- Hoare _ (bind (get _) _) _ => hoare_bind Hoare_get; intros
    | |- Hoare _ (bind (update _) _) _ => hoare_bind Hoare_update; apply Hoare_pre_ex; intros
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind'; intros
    | |- Hoare _ (assume _ ;; _) _ => apply Hoare_assume_bind
    | |- Hoare _ (bind _ _) _ => hoare_bind Hoare_step; apply Hoare_pre_ex; intros
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice
    | |- Hoare _ (ret _) _ => apply Hoare_ret'; intros 
    | |- Hoare _ (continue_case (by_continue _)) _ => apply Hoare_cnt_cnt; intros
    | |- Hoare _ (break_case (by_break _)) _ => apply Hoare_brk_brk; intros
    | |- Hoare _ (break_case (by_continue _)) _ => apply Hoare_brk_cnt
    | |- Hoare _ (continue_case (by_break _)) _ => apply Hoare_cnt_brk
  end.

Ltac hoare_auto :=
  unfold continue, break, If, if_else;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_auto
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_auto
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_left; try hoare_auto
    | |- Hoare _ (bind (any _) _) _ => apply Hoare_any_bind; intros; try hoare_auto
    | |- Hoare _ (bind (get _) _) _ => hoare_bind Hoare_get; intros; try hoare_auto
    | |- Hoare _ (bind (update _) _) _ => hoare_bind Hoare_update; apply Hoare_pre_ex; intros; try hoare_auto
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind'; intros; try hoare_auto
    | |- Hoare _ (assume _ ;; _) _ => apply Hoare_assume_bind; try hoare_auto
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice; try hoare_auto
    | |- Hoare _ (ret _) _ => apply Hoare_ret'; intros 
    | |- Hoare _ (continue_case (by_continue _)) _ => apply Hoare_cnt_cnt; intros
    | |- Hoare _ (break_case (by_break _)) _ => apply Hoare_brk_brk; intros
    | |- Hoare _ (break_case (by_continue _)) _ => apply Hoare_brk_cnt
    | |- Hoare _ (continue_case (by_break _)) _ => apply Hoare_cnt_brk
  end; auto.

Ltac hoare_single_s :=
  match goal with
  | |- Hoare _ (ret _) _ => apply Hoare_ret'
  | |- Hoare _ (any _) _ => apply Hoare_any
  | |- Hoare _ (get _) _ => apply Hoare_get_s
  | |- Hoare _ (get' _) _ => apply Hoare_get'
  | |- Hoare _ (update _) _ => apply Hoare_update_s
  | |- Hoare _ (update' _) _ => apply Hoare_update'
  | |- Hoare _ (assume!! _) _ => apply Hoare_assume'
  | |- Hoare _ (assume _) _ => apply Hoare_assume_s
  | |- Hoare _ (continue_case (by_continue _)) _ => apply Hoare_cnt_cnt
  | |- Hoare _ (break_case (by_break _)) _ => apply Hoare_brk_brk
  | |- Hoare _ (break_case (by_continue _)) _ => apply Hoare_brk_cnt
  | |- Hoare _ (continue_case (by_break _)) _ => apply Hoare_cnt_brk
  end; intros.


Ltac hoare_auto_s :=
  unfold continue, break, If, if_else;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_auto_s
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_auto_s
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_left; try hoare_auto_s
    | |- Hoare _ (bind (any _) _) _ => apply Hoare_any_bind; intros; try hoare_auto_s
    | |- Hoare _ (bind (get _) _) _ => hoare_bind Hoare_get_s; intros; apply Hoare_stateless'; intros; subst; try hoare_auto_s
    | |- Hoare _ (bind (get' _) _) _ => hoare_bind Hoare_get'; intros; apply Hoare_stateless'; intros; subst; try hoare_auto_s
    | |- Hoare _ (bind (update _) _) _ => hoare_bind' Hoare_update_s; apply Hoare_state_intro; intros; try hoare_auto_s
    | |- Hoare _ (bind (update' _) _) _ => hoare_bind' Hoare_update'; try hoare_auto_s
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind'; intros; try hoare_auto_s
    | |- Hoare _ (assume _ ;; _) _ => hoare_bind' Hoare_assume_s; intros; apply Hoare_stateless'; intros; try hoare_auto_s
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice; try hoare_auto_s
    | |- Hoare _ _ _ => hoare_single_s
  end; auto.

Ltac hoare_skip := repeat (apply Hoare_skip; intros; hoare_auto).

Ltac monad_law :=
  repeat (rewrite bind_assoc ||
          rewrite bind_ret_left ||
          rewrite bind_ret_right).

Ltac intro_bound :=
  unfold Sets.equiv; simpl; unfold Sets.lift_equiv; intros.

Ltac monad_equiv :=
  unfold continue, break, continue_case, break_case;
  repeat (monad_law; try easy;
          apply bind_equiv; try easy;
          intro_bound).

Ltac hoare_new_pre P :=
  apply Hoare_conseq_pre with (P2:= P).

Ltac hoare_new_post Q :=
  apply Hoare_conseq_post with (Q2:= Q).

Ltac hoare_new_pre_post P Q :=
  apply Hoare_conseq with (P2:= P) (Q2:= Q).

Tactic Notation "hoare_cons_pre" uconstr(H) :=
  eapply Hoare_conseq_pre; [| apply H]; simpl; try tauto.

Tactic Notation "hoare_cons_post" uconstr(H) :=
  eapply Hoare_conseq_post; [| apply H]; simpl; try tauto.

Tactic Notation "hoare_cons" uconstr(H) :=
  eapply Hoare_conseq_pre; [|eapply Hoare_conseq_post; [| apply H] ]; simpl; try tauto.

Tactic Notation "hoare_apply" uconstr(H) :=
  eapply Hoare_equiv_iff;
  [ | apply H; try tauto];
  monad_equiv.

Tactic Notation "hoare_bind_cons" uconstr(H) :=
  eapply Hoare_bind; [hoare_cons_pre H|]; intros.

(** Hoare rules for fixed points *) 

Theorem Hoare_fix {Σ A B: Type}:
forall (P: A -> Σ -> Prop)
       (Q: A -> B -> Σ -> Prop) 
       (F: (A -> program Σ B)-> (A -> program Σ B))
       (a: A),
  (forall W: A -> program Σ B,
    (forall a, Hoare (P a) (W a) (Q a)) ->
    (forall a, Hoare (P a) (F W a) (Q a))) ->  
  Hoare (P a) (Lfix F a) (Q a).
Proof.
  intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold repeat_break, Lfix.
  intros [n ?].
  revert a s1 b s2 H0 H1.
  change (forall a, Hoare (P a) (Nat.iter n F ∅ a) (Q a)).
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + apply H; apply IHn.
Qed.

(* Hoare_fix When function has no local variable *)
Theorem Hoare_fix' {Σ B: Type}:
forall (P: Σ -> Prop)
       (Q: B -> Σ -> Prop)
       (F: (program Σ B)-> program Σ B),
  (forall W: program Σ B, 
    Hoare P W Q ->
    Hoare P (F W) Q)->  
  Hoare P (Lfix F) Q.
Proof.
  intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold Lfix.
  intros [n ?].
  revert s1 b s2 H0 H1.
  change (Hoare P (Nat.iter n F ∅) Q).
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + apply H; apply IHn.
Qed.

Theorem Hoare_fix_logicv {Σ A B C: Type}:
forall (F: (A -> program Σ B)-> (A -> program Σ B))
       (P : A -> C -> Σ -> Prop)
       (Q : A -> C -> B -> Σ -> Prop) a c,
  (forall W: A -> program Σ B, 
    (forall a c, Hoare (P a c) (W a) (Q a c)) ->
    (forall a c, Hoare (P a c) (F W a) (Q a c))) ->  
  Hoare (P a c) (Lfix F a) (Q a c).
Proof.
  intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold repeat_break, Lfix.
  intros [n ?].
  revert a c s1 b s2 H0 H1.
  change (forall a c, Hoare (P a c) (Nat.iter n F ∅ a) (Q a c)).
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + apply H; apply IHn.
Qed.

Theorem Hoare_fix_logicv_conj {Σ A B C: Type}:
forall (F: (A -> program Σ B)-> (A -> program Σ B))
       (P1 : A -> C -> Σ -> Prop)
       (Q1 : A -> C -> B -> Σ -> Prop) 
       a c,
forall {D: Type}
       (P2 : A -> D -> Σ -> Prop) (Q2 : A -> D -> B -> Σ -> Prop),
  (forall a d, Hoare (P2 a d) (Lfix F a) (Q2 a d)) ->
  (forall W: A -> program Σ B, 
    (forall a d, Hoare (P2 a d) (W a) (Q2 a d)) ->
    (forall a c, Hoare (P1 a c) (W a) (Q1 a c)) ->
    (forall a c, Hoare (P1 a c) (F W a) (Q1 a c))) ->  
  (Hoare (P1 a c) (Lfix F a) (Q1 a c)).
Proof.
  intros *  HT1; intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold repeat_break, Lfix.
  intros [n ?].
  revert a c s1 b s2 H0 H1.
  change (forall a c, Hoare (P1 a c) (Nat.iter n F ∅ a) (Q1 a c)).
  assert (forall n a d, Hoare (P2 a d) (Nat.iter n F ∅ a) (Q2 a d)).
  { intros.
    specialize (HT1 a d).
    unfold Hoare.
    unfold Hoare, Lfix in HT1.
    intros.
    apply (HT1 _ _ s2 H0).
    exists n0.
    auto.
  }
  clear HT1. rename H0 into HT1.
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + apply H. 
    apply HT1.
    apply IHn.
Qed.

(** A stronger version *)
Theorem Hoare_fix_logicv_conj' {Σ A B C: Type}:
forall (F: (A -> program Σ B)-> (A -> program Σ B))
       (P1 : A -> C -> Σ -> Prop)
       (Q1 : A -> C -> B -> Σ -> Prop) 
       a c,
forall {D: Type}
       (P2 : A -> D -> Σ -> Prop) (Q2 : A -> D -> B -> Σ -> Prop),
  (forall a d, Hoare (P2 a d) (Lfix F a) (Q2 a d)) ->
  (forall W: A -> program Σ B, 
    (forall a d, Hoare (P2 a d) (W a) (Q2 a d)) ->
    (forall a c, Hoare (P1 a c) (W a) (Q1 a c)) ->
    (forall a c, Hoare (P2 a c) (F W a) (Q2 a c)) ->
    (forall a c, Hoare (P1 a c) (F W a) (Q1 a c))) ->  
  (Hoare (P1 a c) (Lfix F a) (Q1 a c)).
Proof.
  intros *  HT1; intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold Lfix.
  intros [n ?].
  revert a c s1 b s2 H0 H1.
  change (forall a c, Hoare (P1 a c) (Nat.iter n F ∅ a) (Q1 a c)).
  assert (forall n a d, Hoare (P2 a d) (Nat.iter n F ∅ a) (Q2 a d)).
  { intros.
    specialize (HT1 a d).
    unfold Hoare.
    unfold Hoare, Lfix in HT1.
    intros.
    apply (HT1 _ _ s2 H0).
    exists n0.
    auto.
  }
  clear HT1. rename H0 into HT1.
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + apply H. 
    apply HT1.
    apply IHn.
    specialize (HT1 (S n)).
    simpl in HT1.
    apply HT1.
Qed.

Theorem Hoare_fix_mutual_conj {Σ A B C: Type}:
forall (F: (A -> program Σ B)-> (A -> program Σ B))
       (P1 P2: A ->  Σ -> Prop)
       (Q1 Q2: A -> B ->  Σ -> Prop) 
       a,
  (forall (W: A -> program Σ B) a,
    (forall a, Hoare (P1 a) (W a) (Q1 a)) ->
    (forall a, Hoare (P2 a) (W a) (Q2 a)) ->
    Hoare (P1 a) (F W a) (Q1 a)) ->
  (forall (W: A -> program Σ B) a,
    (forall a, Hoare (P1 a) (W a) (Q1 a)) ->
    (forall a, Hoare (P2 a) (W a) (Q2 a)) ->
    Hoare (P2 a) (F W a) (Q2 a)) ->  
  (Hoare (P1 a) (Lfix F a) (Q1 a) /\ Hoare (P2 a) (Lfix F a) (Q2 a)).
Proof.
  intros.
  unfold Hoare; sets_unfold.
  assert ((forall (s1 : Σ) (a0 : B) (s2 : Σ),
    Lfix F a s1 a0 s2 ->
    (P1 a s1 ->  Q1 a a0 s2) /\ 
    (P2 a s1 -> Q2 a a0 s2))).
  2:{
    clear - H1.
    split; intros;
    specialize (H1 s1 a0 s2);
    tauto.
  }
  intros s1 b s2.
  unfold Lfix; sets_unfold; intros Hf.
  destruct Hf as [n Hf].
  revert Hf; revert a s1 b s2.
  induction n.
  - simpl; tauto.
  - simpl; intros.
    split; intros.
    + apply H in Hf; eauto;
      unfold Hoare; sets_unfold; intros;
      specialize (IHn a0 s0 a1 s3); tauto.
    + apply H0 in Hf; eauto;
      unfold Hoare; sets_unfold; intros;
      specialize (IHn a0 s0 a1 s3); tauto.
Qed.
    
(* we consider a recursive monadic program (A -> program Σ R) may have multiple specifications *)

Record monad_funcspec {Σ A R: Type}: Type := mk_mfs { 
  mFS_lv : Type;
  mFS_pre : A -> mFS_lv -> Σ -> Prop;
  mFS_Post : A -> mFS_lv -> R -> Σ -> Prop;
  }.
Definition monad_funcspecs {Σ A R: Type} : Type := list (@monad_funcspec Σ A R).
Definition monad_sat_funcspec  {Σ A R: Type} 
  (m: (A -> program Σ R)) (fs: monad_funcspec) : Prop :=
  forall (a: A) (lv: mFS_lv fs),
    Hoare ((mFS_pre fs) a lv) (m a) ((mFS_Post fs) a lv).

Theorem Hoare_fix_logicv_fspecs {Σ A R: Type}:
forall (F: (A -> program Σ R) -> (A -> program Σ R)) Fspecs fs,
  Forall (fun fs => monad_sat_funcspec (fun a => Lfix F a) fs) Fspecs ->
  (forall W: A -> program Σ R, 
    (Forall (fun fs => monad_sat_funcspec W fs) Fspecs) ->
    (forall a lv, Hoare ((mFS_pre fs) a lv) (W a) ((mFS_Post fs) a lv)) ->
    (forall a lv, Hoare ((mFS_pre fs) a lv) (F W a) ((mFS_Post fs) a lv))) ->  
  (forall (a: A) (lv: mFS_lv fs),
    Hoare ((mFS_pre fs) a lv) (Lfix F a) ((mFS_Post fs) a lv)).
Proof.
  intros *  HT1; intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold Lfix.
  intros [n ?].
  revert a lv s1 b s2 H0 H1.
  change (forall a lv, Hoare ((mFS_pre fs) a lv) (Nat.iter n F ∅ a) ((mFS_Post fs) a lv)).
  assert (forall n, Forall (fun fs => monad_sat_funcspec (fun a => Nat.iter n F ∅ a) fs) Fspecs).
  { clear - HT1. intros.
    apply Forall_forall.
    rewrite Forall_forall in HT1.
    unfold monad_sat_funcspec in *.
    intros fs H a lv.
    specialize (HT1 fs H a lv).
    unfold Hoare.
    unfold Hoare, Lfix in HT1.
    intros.
    apply (HT1 _ _ s2 H0).
    exists n.
    auto.
  }
  clear HT1. rename H0 into HT1.
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + apply H. 
    apply HT1.
    apply IHn.
Qed.

Ltac hoare_fix_nolv_auto A :=
   match goal with 
  | |- @Hoare ?Σ ?R ?P1 (Lfix ?F ?a) ?P2 =>
    let P := fresh "P" in evar (P: A -> Σ  -> Prop);
    let Q := fresh "Q" in evar (Q: A -> R -> Σ  -> Prop);
     let h := fresh "h" in assert (P = P) as h;[ 
       let P' := eval pattern (a) in P1 in
      match P' with  
      | ?P''  _ => exact (Logic.eq_refl P'') end | ];
    clear h;
    let h := fresh "h" in assert (Q = Q) as h;[
     let Q' := eval pattern (a) in P2 in
      match Q' with  
      | ?Q''  _ => exact (Logic.eq_refl Q'') end |];
    clear h;
    eapply Hoare_fix with (P:= P) (Q := Q);
    subst P Q
  end.

Ltac hoare_fix_lv_auto A C c:=
   match goal with 
  | |- @Hoare ?Σ ?R ?P1 (Lfix ?F ?a) ?Q1 =>
     let P := fresh "P" in evar (P: A -> C -> Σ  -> Prop);
     let Q := fresh "Q" in evar (Q: A -> C -> R -> Σ -> Prop);
     let h := fresh "h" in assert (P = P) as h;[ 
      let P0 := eval pattern (c) in P1 in
      match P0 with 
      | ?P0' _ => 
      let P' := eval pattern (a) in P0' in
      match P' with  
      | ?P'' _  => exact (Logic.eq_refl P'') end end| ];
     clear h;
     let h := fresh "h" in assert (Q = Q) as h;[ 
      let Q0 := eval pattern (c) in Q1 in
      match Q0 with 
      | ?Q0' _ => 
      let Q' := eval pattern (a) in Q0' in
      match Q' with  
      | ?Q'' _  => exact (Logic.eq_refl Q'') end end| ];
    clear h;
    eapply Hoare_fix_logicv with  (P:= P) (Q := Q); subst P Q
  end.

Ltac hoare_fix_lv_auto_conj A C c:=
  match goal with 
| |- @Hoare ?Σ ?R ?P (Lfix ?F ?a) ?Q =>
    let P1 := fresh "P" in evar (P1: A -> C -> Σ  -> Prop);
    let Q1 := fresh "Q" in evar (Q1: A -> C -> R -> Σ -> Prop);
    let h := fresh "h" in assert (P1 = P1) as h;[ 
    let P0 := eval pattern (c) in P in
    match P0 with 
    | ?P0' _ => 
    let P' := eval pattern (a) in P0' in
    match P' with  
    | ?P'' _  => exact (Logic.eq_refl P'') end end| ];
    clear h;
    let h := fresh "h" in assert (Q1 = Q1) as h;[ 
    let Q0 := eval pattern (c) in Q in
    match Q0 with 
    | ?Q0' _ => 
    let Q' := eval pattern (a) in Q0' in
    match Q' with  
    | ?Q'' _  => exact (Logic.eq_refl Q'') end end| ];
  clear h;
  eapply (Hoare_fix_logicv_conj _ P1 Q1 a c);
  subst P1 Q1
end.

Ltac hoare_fix_lv_auto_conj' A C c:=
  match goal with 
| |- @Hoare ?Σ ?R ?P (Lfix ?F ?a) ?Q =>
    let P1 := fresh "P" in evar (P1: A -> C -> Σ  -> Prop);
    let Q1 := fresh "Q" in evar (Q1: A -> C -> R -> Σ -> Prop);
    let h := fresh "h" in assert (P1 = P1) as h;[ 
    let P0 := eval pattern (c) in P in
    match P0 with 
    | ?P0' _ => 
    let P' := eval pattern (a) in P0' in
    match P' with  
    | ?P'' _  => exact (Logic.eq_refl P'') end end| ];
    clear h;
    let h := fresh "h" in assert (Q1 = Q1) as h;[ 
    let Q0 := eval pattern (c) in Q in
    match Q0 with 
    | ?Q0' _ => 
    let Q' := eval pattern (a) in Q0' in
    match Q' with  
    | ?Q'' _  => exact (Logic.eq_refl Q'') end end| ];
  clear h;
  eapply (Hoare_fix_logicv_conj' _ P1 Q1 a c);
  subst P1 Q1
end.

(** Hoare rules for loops *)

Theorem Hoare_while {Σ: Type} (cond: Σ -> Prop) 
  (body : program Σ unit) (P: Σ -> Prop):
  Hoare (fun s => cond s /\ P s) body (fun _ s => P s) ->
  Hoare P (while cond body) (fun _ s => P s /\ ~ cond s).
Proof.
  intros.
  unfold while.
  apply Hoare_fix'.
  intros; unfold while_f.
  hoare_auto; [| tauto].
  hoare_bind H; simpl; auto.
Qed.

Theorem Hoare_whileret {Σ A: Type} (cond: A -> Σ -> Prop) 
  (body : A -> program Σ A) (P: A -> Σ -> Prop) (a: A):
  (forall a, Hoare (fun s => cond a s /\ P a s) (body a) P) ->
  Hoare (P a) (whileret cond body a) (fun a s => P a s /\ ~ cond a s).
Proof.
  intros.
  unfold whileret.
  match goal with
  | |- Hoare _ _ ?P => apply Hoare_fix with (Q:= fun _ => P)
  end.
  intros.
  unfold whileret_f.
  hoare_auto.
  2:tauto.
  hoare_bind (H a0).
  apply H0.
Qed.
    
Theorem Hoare_repeat_break {Σ A B: Type}:
  forall (body: A -> program Σ (CntOrBrk A B))
         (P: A -> Σ -> Prop)
         (Q: B -> Σ -> Prop),
    (forall a, Hoare (P a) (body a) (fun x s => match x with
                                                | by_continue a => P a s
                                                | by_break b => Q b s
                                                end)) ->
    (forall a, Hoare (P a) (repeat_break body a) Q).
Proof.
  intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold repeat_break, Lfix.
  intros [n ?].
  revert a s1 b s2 H0 H1.
  change (forall a, Hoare (P a) (Nat.iter n (repeat_break_f body) ∅ a) Q).
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold repeat_break_f at 1.
    eapply Hoare_bind.
    - apply H.
    - intros [a0 | b0].
      * apply IHn.
      * apply Hoare_ret.
Qed.

Theorem Hoare_repeat_break' {Σ A B: Type}:
  forall (body: A -> program Σ (CntOrBrk A B))
         (P: A -> Σ -> Prop)
         (Q: B -> Σ -> Prop),
    (forall a, Hoare (P a) (x <- body a;; continue_case x) P) ->
    (forall a, Hoare (P a) (x <- body a;; break_case x) Q) -> 
    (forall a, Hoare (P a) (repeat_break body a) Q).
Proof.
  intros.
  apply Hoare_repeat_break.
  intros; apply Hoare_sum; auto.  
Qed.

(** P: Set -> Prop, require Prop P is proper *)
Theorem Hoare_forset {Σ A}
  (P: (A -> Prop) -> Σ -> Prop)
  (universe: A -> Prop)
  (body: A -> program Σ unit)
  (ProperP: Proper (Sets.equiv ==> eq ==> iff) P):
  (forall done a,
    done ⊆ universe ->
    a ∈ universe ->
    ~a ∈ done ->
    Hoare (P done) (body a) (fun _ s => P (done ∪ [a]) s)) ->
  Hoare (P ∅) (forset universe body) (fun _ s => P universe s).
Proof.
  intros.
  unfold forset.
  hoare_cons Hoare_fix.
  {
    instantiate (1 := fun todo s => P (fun a => a ∈ universe /\ ~ a ∈ todo ) s /\ todo ⊆ universe).
    simpl; intros.
    assert ((fun a : A => a ∈ universe /\ ~ a ∈ universe) == ∅).
    { sets_unfold; tauto. }
    rewrite H1; split; easy.
  }
  {
    instantiate (1 := fun _ _ s => P universe s).
    simpl; tauto.
  }
  simpl; intros W IH todo; unfold forset_f.
  intro_state.
  hoare_auto_s; subst.
  2:{
    assert ((fun a : A => a ∈ universe /\ ~ a ∈ todo) == universe).
    {
      sets_unfold; intros; split; try tauto.
      intros; split; auto.
      change (~ a ∈ todo).
      rewrite H1; tauto.
    }
    rewrite H2 in H0; tauto.
  }
  destruct H0.
  apply Hoare_conseq_pre with 
    (P2:= P (fun a : A => a ∈ universe /\ ~ a ∈ todo)).
  intros; subst; tauto.
  hoare_bind H.
  sets_unfold; tauto.
  apply H2; auto.
  sets_unfold; tauto.
  hoare_cons_pre IH.
  intros; split.
  2:{
    sets_unfold.
    intros; apply H2; tauto.
  }
  eapply ProperP; eauto.
  sets_unfold; intros.
  split; intros.
  - destruct H4.
    assert (~ todo a1 \/ a1 = a) by tauto. clear H5.
    destruct H6; auto.
  - destruct H4.
    split; tauto.
    subst; split; try tauto.
    apply H2; auto.
Qed.

Module StateRelMonadExample.

Example c1 {Σ: Type} (f g: StateRelMonad.M Σ nat) (p q: Σ -> Prop) (h: nat -> nat -> StateRelMonad.M Σ nat) :=
  x <- f;; assume(p);;
  y <- g;; assume(q);;
  h x y.

Example c2 {Σ: Type} (f g: StateRelMonad.M Σ nat) (p q: Σ -> Prop) (h: nat -> nat -> StateRelMonad.M Σ nat) :=
  '(x,y) <- (x <- f;; assume(p);;
             y <- g;; assume(q);;
             ret (x, y));; 
  h x y.

Lemma c1_c2_equiv{Σ: Type}: 
  @c1 Σ == c2.
Proof.
  unfold c1, c2.
  do 5 intro_bound.
  monad_equiv.
Qed.

Local Open Scope Z.

Example hailstone_body (x: Z): StateRelMonad.M unit (CntOrBrk Z Z):=
  choice 
   (assume!! (x <= 1);; break x)
   (assume!! (x > 1);; 
    choice
     (assume!! (exists k, x = 2 * k );; continue (x/2))
     (assume!! (exists k, x = 2 * k + 1);; continue (3 * x + 1))).

Lemma hailstone_Hoare(x:Z): 
  Hoare (fun _ => x >= 1) 
        (y <- hailstone_body x;; continue_case y)
        (fun y _ => y >= 1).
Proof.
  unfold hailstone_body.
  hoare_auto.
  - clear s; destruct H0 as [k ?].
    subst.
    rewrite Z.mul_comm.
    rewrite Z_div_mult; lia.
  - lia.
Qed. 

End StateRelMonadExample.
