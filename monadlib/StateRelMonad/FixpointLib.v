Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import SetsClass.SetsClass.
Import SetsNotation.
From FP Require Import SetsFixedpoints PartialOrder_Setoid.
Require Import StateRelBasic. 
Import Monad MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section mono_and_continuous_lemmas.

  Definition increasing {A: Type} {_SETS_A : Sets.SETS A} (T : nat -> A):= @sseq_mono A _SETS_A T.
  Definition mono {A: Type} {_SETS_A : Sets.SETS A}  {B: Type} {_SETS_B : Sets.SETS B}  
    (f : A -> B) := Proper (Sets.included ==> Sets.included) f.
  Definition continuous {A: Type} {_SETS_A : Sets.SETS A} {B: Type} {_SETS_B : Sets.SETS B} 
    (f : A -> B) := @sseq_continuous  A _SETS_A B _SETS_B f.
  Definition mono_cont {A: Type} {_SETS_A : Sets.SETS A} {B: Type} {_SETS_B : Sets.SETS B} 
    (f : A -> B) := mono f /\ continuous f.
  
  Lemma Lfix_fixpoint'{A} {_SETS_A: Sets.SETS A} {_SETS_Properties_A: SETS_Properties A}: 
    forall f,
      mono_cont f -> Lfix f == f (Lfix f).
  Proof.
    intros.
    hnf in H.
    apply Lfix_fixpoint; tauto.
  Qed.

  Lemma mono_Lfix {A B: Type} {_SETS_A: Sets.SETS A} {_SETS_B: Sets.SETS B} 
    {_SETS_PROP_A: SETS_Properties A} {_SETS_PROP_B: SETS_Properties B}:
    forall (f: A -> B -> B),
      (forall a, mono (f a)) ->
      (forall b, mono (fun W => f W b)) ->
      mono (fun W => (Lfix (f W))).
  Proof.
    unfold mono.
    unfold Proper, respectful.
    intros; apply Lfix_mono.
    - unfold Proper, respectful.
      intros; apply H; auto.
    - intros. apply H0; auto.
  Qed.
  
Lemma Lfix_seq_cont_general {A B} {SET_A: Sets.SETS A} {PROP_A: SETS_Properties A}
                          {SET_B: Sets.SETS B} {PROP_B: SETS_Properties B}:
forall (f: A -> B -> B)
        (Hf_mono: Proper (Sets.included ==> Sets.included ==> Sets.included) f)
        (Hfa_sseq: forall a, sseq_continuous (f a))
        (Hf_sseq: forall b, sseq_continuous (fun a => f a b)),
  sseq_continuous (fun a: A => Lfix (f a)).
Proof.
  intros. intros until 1. apply Sets_equiv_Sets_included. split.
  - apply Sets_indexed_union_included. intros n. induction n.
    + simpl. apply Sets_empty_included.
    + simpl. rewrite IHn. erewrite Hf_sseq;auto.
      apply Sets_indexed_union_included. intros m.
      erewrite Hfa_sseq.
      apply Sets_indexed_union_included. intros k.
      set(mk:= max m k). assert (Hk: T k ⊆ T mk).
      { apply sseq_mono_nat_le;auto. apply Max.le_max_r. }
      assert (Hm: T m ⊆ T mk).
      { apply sseq_mono_nat_le;auto. apply Max.le_max_l. }
      rewrite <- (Sets_included_indexed_union mk).
      rewrite (Lfix_fixpoint (f (T mk))).
      apply Hf_mono;auto. 
      apply Lfix_mono. apply Hf_mono. reflexivity.
      intros. apply Hf_mono;auto. reflexivity.
      apply Hf_mono. reflexivity. apply Hfa_sseq.
      unfold sseq_mono. intros. 
      apply Lfix_mono. apply Hf_mono. reflexivity.
      intros. apply Hf_mono;auto. reflexivity.
  - apply Sets_indexed_union_included. intros.
    apply Lfix_mono. apply Hf_mono;auto. reflexivity.
    intros. apply Hf_mono. rewrite <- (Sets_included_indexed_union (S n)).
    auto. reflexivity.
Qed.

  Context {Σ: Type}.

  Lemma increasing_mono_increasing:
  forall {A B: Type} {_SETS_A : Sets.SETS A}  {_SETS_B : Sets.SETS B}
         (f: A -> B)
         (l: nat -> A),
    increasing l -> mono f -> increasing (fun n => f (l n)).
  Proof.
    intros.
    unfold increasing, sseq_mono. intros.
    apply H0. apply H.
  Qed.

  Lemma increasing_program_plus : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    increasing c -> c n ⊆ c (n + m).
  Proof.
    induction m;intros.
    - assert (n + 0 = n) by lia. rewrite H0.
      reflexivity.
    - assert (n + S m = S (n + m)) by lia.
      rewrite H0.
      transitivity (c (n + m)).
      eapply IHm;auto.
      eapply H.
  Qed. 

  Lemma increasing_program_le : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    n <= m -> increasing c -> c n ⊆ c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus;auto.
  Qed.

  Lemma increasing_program_plus' : forall {B:Type} (m n: nat) (c: nat -> program Σ B), 
    increasing c -> c n ⊆ c (n + m).
  Proof.
    induction m;intros.
    - assert (n + 0 = n) by lia. rewrite H0.
      reflexivity.
    - assert (n + S m = S (n + m)) by lia.
      rewrite H0.
      transitivity (c (n + m)).
      eapply IHm;auto.
      eapply H.
  Qed. 

  Lemma increasing_program_le' : forall {B:Type} (m n: nat) (c: nat -> program Σ B), 
    n <= m -> increasing c -> c n ⊆ c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus';auto.
  Qed.
  
  Lemma mono_intro {A B: Type}:
    forall (f: (A -> program Σ B) -> A -> program Σ B),
      (forall a, mono (fun W => f W a)) ->
      mono f.
  Proof.
    unfold mono, Proper, respectful.
    sets_unfold; intros.
    eapply H; eauto.
  Qed.

  Lemma mono_bind {A B D: Type}:
    forall  (c1: (A -> program Σ B) -> program Σ D) (c2: (A -> program Σ B) -> D -> program Σ B),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: A -> program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono.
    unfold Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    destruct H2 as [d [s2 [H2 H3]]].
    exists d, s2.
    split; auto.
    eapply H; eauto.
    eapply H0; eauto.
  Qed.

  Lemma mono_bind' {B D: Type}:
    forall  (c1: (program Σ B) -> program Σ D) (c2: (program Σ B) -> D -> program Σ B),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono.
    unfold Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    destruct H2 as [d [s2 [H2 H3]]].
    exists d, s2.
    split; auto.
    eapply H; eauto.
    eapply H0; eauto.
  Qed.

  Lemma mono_choice {A B D: Type}:
    forall (c1 c2: (A -> program Σ B) -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful, choice.
    sets_unfold.
    intros.
    destruct H2.
    - left. eapply H; eauto.
    - right. eapply H0; eauto.
  Qed.

  Lemma mono_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful, choice.
    sets_unfold.
    intros.
    destruct H2.
    - left. eapply H; eauto.
    - right. eapply H0; eauto.
  Qed.

  Lemma continuous_intro {A B: Type}:
    forall (f: (A -> program Σ B) -> A -> program Σ B),
      (forall a, continuous (fun W => f W a)) ->
      continuous f.
  Proof.
    unfold continuous, sseq_continuous, sseq_mono.
    sets_unfold; intros.
    eapply H; eauto.
  Qed.

  Lemma continuous_const {A B C: Type}:
    forall (f: program Σ C),
      continuous (fun (W: A -> program Σ B) => f).
  Proof.
    intros.
    unfold continuous, sseq_continuous, sseq_mono.
    intros.
    sets_unfold; split; intros.
    - exists 0; auto.
    - destruct H0; auto.
  Qed.

  Lemma continuous_const' {B C: Type}:
    forall (f: program Σ C),
      continuous (fun (W: program Σ B) => f).
  Proof.
    intros.
    unfold continuous, sseq_continuous, sseq_mono.
    intros.
    sets_unfold; split; intros.
    - exists 0; auto.
    - destruct H0; auto.
  Qed.

  Lemma continuous_bind {A B D: Type}:
    forall  (c1: (A -> program Σ B) -> program Σ D) (c2: (A -> program Σ B) -> D -> program Σ B),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: A -> program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, continuous, sseq_continuous, Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    split; intros.
    - destruct H4 as [d [s2 [H4 H5]]].
      apply H0 in H4; eauto.
      apply H2 in H5; eauto.
      clear H0 H2.
      destruct H4 as [i1 H4].
      destruct H5 as [i2 H5].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d, s2.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        apply increasing_program_le; auto.
      + apply leb_complete_conv in Heq.
        exists i1, d, s2.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        apply increasing_program_le; [lia| auto].
    - destruct H4 as [i [d [s2 [H4 H5]]]].
      exists d, s2.
      split.
      + apply H0; auto.
        exists i; auto.
      + apply H2; auto.
        exists i; auto.
  Qed.

  Lemma continuous_bind' {B D: Type}:
    forall  (c1: program Σ B -> program Σ D) (c2: program Σ B -> D -> program Σ B),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, continuous, sseq_continuous, Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    split; intros.
    - destruct H4 as [d [s2 [H4 H5]]].
      apply H0 in H4; eauto.
      apply H2 in H5; eauto.
      clear H0 H2.
      destruct H4 as [i1 H4].
      destruct H5 as [i2 H5].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d, s2.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        apply increasing_program_le'; auto.
      + apply leb_complete_conv in Heq.
        exists i1, d, s2.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        apply increasing_program_le'; [lia| auto].
    - destruct H4 as [i [d [s2 [H4 H5]]]].
      exists d, s2.
      split.
      + apply H0; auto.
        exists i; auto.
      + apply H2; auto.
        exists i; auto.
  Qed.

  Lemma continuous_choice {A B D: Type}:
    forall (c1 c2: (A -> program Σ B) -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold continuous, sseq_continuous.
    unfold choice; sets_unfold; intros.
    split; intros.
    - destruct H2.
      + apply H in H2; auto.
        destruct H2.
        exists x; tauto.
      + apply H0 in H2; auto.
        destruct H2.
        exists x; tauto.
    - destruct H2 as [i [H2 | H2]].
      + left; apply H; auto.
        exists i; auto.
      + right; apply H0; auto.
        exists i; auto.
  Qed.

  Lemma continuous_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold continuous, sseq_continuous.
    unfold choice; sets_unfold; intros.
    split; intros.
    - destruct H2.
      + apply H in H2; auto.
        destruct H2.
        exists x; tauto.
      + apply H0 in H2; auto.
        destruct H2.
        exists x; tauto.
    - destruct H2 as [i [H2 | H2]].
      + left; apply H; auto.
        exists i; auto.
      + right; apply H0; auto.
        exists i; auto.
  Qed.

  Lemma mono_cont_intro {A B: Type}:
    forall (f: (A -> program Σ B) -> A -> program Σ B),
      (forall a, mono_cont (fun W => f W a)) ->
      mono_cont f.
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_intro.
      intros; apply H.
    - apply continuous_intro.
      intros; apply H.
  Qed.

  Lemma mono_cont_const {A B C: Type}:
    forall (f: program Σ C),
      mono_cont (fun (W: A -> program Σ B) => f).
  Proof.
    intros.
    unfold mono_cont.
    split; try easy.
    apply continuous_const.
  Qed.

  Lemma mono_cont_const' {B C: Type}:
    forall (f: program Σ C),
      mono_cont (fun (W:program Σ B) => f).
  Proof.
    intros.
    unfold mono_cont.
    split; try easy.
    apply continuous_const'.
  Qed.

  Lemma mono_cont_bind {A B D: Type}:
    forall  (c1: (A -> program Σ B) -> program Σ D) (c2: (A -> program Σ B) -> D -> program Σ B),
      mono_cont c1 ->
      (forall d, mono_cont (fun W => c2 W d)) ->
      mono_cont (fun (W: A -> program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_bind; try tauto.
      intros d; apply H0.
    - apply continuous_bind; try tauto;
      intros d; apply H0.
  Qed.

  Lemma mono_cont_bind' {B D: Type}:
    forall  (c1: program Σ B -> program Σ D) (c2: program Σ B -> D -> program Σ B),
      mono_cont c1 ->
      (forall d, mono_cont (fun W => c2 W d)) ->
      mono_cont (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_bind'; try tauto.
      intros d; apply H0.
    - apply continuous_bind'; try tauto;
      intros d; apply H0.
  Qed.

  Lemma mono_cont_choice {A B D: Type}:
    forall (c1 c2: (A -> program Σ B) -> program Σ D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_choice; tauto.
    - apply continuous_choice; tauto.
  Qed.

  Lemma mono_cont_choice' {B D: Type}:
    forall (c1 c2: (program Σ B) -> program Σ D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_choice'; tauto.
    - apply continuous_choice'; tauto.
  Qed.

  Lemma mono_cont_Lfix {A B: Type} {_SETS_A: Sets.SETS A} {_SETS_B: Sets.SETS B}
    {_SETS_Properties_A: SETS_Properties A} {_SETS_Properties_B: SETS_Properties B}:
    forall (f: A -> B -> B),
      (forall a, mono_cont (f a)) ->
      (forall b, mono_cont (fun W => f W b)) ->
      mono_cont (fun W => Lfix (f W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_Lfix; intros.
      apply H. apply H0.
    - apply Lfix_seq_cont_general; intros.
      unfold Proper, respectful.
      intros.
      etransitivity.
      apply H; eauto.
      apply H0; auto.
      apply H. apply H0.
  Qed.

End mono_and_continuous_lemmas.

Ltac mono_cont_auto :=
  match goal with
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) (a: ?A) => _) => apply mono_cont_intro; intros; mono_cont_auto
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => bind _ _) => apply mono_cont_bind; [try mono_cont_auto | intros; try mono_cont_auto]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => choice _ _) => apply mono_cont_choice; [try mono_cont_auto | try mono_cont_auto]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => Lfix _) => apply mono_cont_Lfix; intros; try mono_cont_auto
  | |- mono_cont (bind _) => (apply mono_cont_bind || apply mono_cont_bind'); [try mono_cont_auto | intros; try mono_cont_auto]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => _) => try apply mono_cont_const; try easy
  | |- mono_cont (fun (W: program ?Σ ?B) => bind _ _) => apply mono_cont_bind'; [try mono_cont_auto | intros; try mono_cont_auto]
  | |- mono_cont (fun (W: program ?Σ ?B) => choice _ _) => apply mono_cont_choice'; [try mono_cont_auto | try mono_cont_auto]
  | |- mono_cont (fun (W: program ?Σ ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto
  | |- mono_cont (fun (W: program ?Σ ?B) => Lfix _) => apply mono_cont_Lfix; intros; try mono_cont_auto
  | |- mono_cont (fun (W: program ?Σ ?B) => _) => try apply mono_cont_const'; try easy
  end.

Section loop_unfold.
Context {Σ: Type}.

Lemma while_unfold: forall (cond: Σ -> Prop) (body : program Σ unit), 
    while cond body == choice 
                         (assume cond;; body;; while cond body)
                         (assume (fun s => ~ cond s);; ret tt).
  Proof.
    intros.
    unfold while.
    apply (Lfix_fixpoint' (while_f cond body)).
    unfold while_f.
    mono_cont_auto.
  Qed.

  Lemma whileret_unfold: forall {A: Type} (cond: A -> Σ -> Prop) (body : A -> (program Σ A))  (a: A), 
    whileret cond body == 
    fun a => 
      choice (assume (fun s => cond a s);; a' <- body a;; whileret cond body a') 
             (assume (fun s => ~ cond a s);; ret a).
  Proof.
    intros.
    unfold whileret.
    apply (Lfix_fixpoint' (whileret_f cond body)).
    unfold whileret_f.
    mono_cont_auto.
  Qed.

  Lemma Repeat_unfold (body : (program Σ unit)):
    Repeat body == (body;; Repeat body).
  Proof.
    unfold Repeat, Repeat_f.
    apply (Lfix_fixpoint' (Repeat_f body)).
    unfold Repeat_f.
    mono_cont_auto.
  Qed.

  Lemma repeat_break_unfold:
    forall {A B} (body: A -> program Σ (CntOrBrk A B)),
    repeat_break body == fun a =>
                         x <- body a;; 
                         match x with
                         | by_continue a0 => repeat_break body a0
                         | by_break b0 => ret b0
                         end.
  Proof.
    intros.
    unfold repeat_break.
    apply (Lfix_fixpoint' (repeat_break_f body)).
    unfold repeat_break_f.
    mono_cont_auto.
  Qed.

  Lemma forset_unfold_aux {A: Prop}
    (body: A -> program Σ unit):
    Lfix (forset_f body) == fun universe =>
    choice (a <- get (fun _ a => a ∈ universe);; 
            body a;;
            forset (fun x => x ∈ universe /\ x <> a) body)
           (assume!! (universe == ∅);;
            ret tt).
  Proof.
    apply (Lfix_fixpoint' (forset_f body)).
    unfold forset_f.
    mono_cont_auto.
  Qed.

  Lemma forset_unfold {A: Prop}
    (universe: A -> Prop)
    (body: A -> program Σ unit):
    forset universe body ==
    choice (a <- get (fun _ a => a ∈ universe);; 
            body a;;
            forset (fun x => universe x /\ x <> a) body)
           (assume!! (universe == ∅);;
            ret tt).
  Proof.
    unfold forset.
    pose proof (forset_unfold_aux body).
    apply H.
  Qed.

End loop_unfold.
