Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import SetsClass.SetsClass.
Import SetsNotation.
From FP Require Import SetsFixedpoints PartialOrder_Setoid.
Require Import SetBasic. 
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

  Lemma increasing_program_plus : forall {A B:Type} (m n: nat) (c: nat -> A -> program B), 
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

  Lemma increasing_program_le : forall {A B:Type} (m n: nat) (c: nat -> A -> program B), 
    n <= m -> increasing c -> c n ⊆ c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus;auto.
  Qed.

  Lemma increasing_program_plus' : forall {B:Type} (m n: nat) (c: nat -> program B), 
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

  Lemma increasing_program_le' : forall {B:Type} (m n: nat) (c: nat -> program B), 
    n <= m -> increasing c -> c n ⊆ c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus';auto.
  Qed.
  
  Lemma mono_intro {A B: Type}:
    forall (f: (A -> program B) -> A -> program B),
      (forall a, mono (fun W => f W a)) ->
      mono f.
  Proof.
    unfold mono, Proper, respectful.
    sets_unfold; intros.
    eapply H; eauto.
  Qed.

  Lemma mono_bind {A B D: Type}:
    forall  (c1: (A -> program B) -> program D) (c2: (A -> program B) -> D -> program B),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: A -> program B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono.
    unfold Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    destruct H2 as [d [H2 H3]].
    exists d.
    split; auto.
    eapply H; eauto.
    eapply H0; eauto.
  Qed.

  Lemma mono_bind' {B D: Type}:
    forall  (c1: (program B) -> program D) (c2: (program B) -> D -> program B),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: program B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono.
    unfold Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    destruct H2 as [d [H2 H3]].
    exists d.
    split; auto.
    eapply H; eauto.
    eapply H0; eauto.
  Qed.

  Lemma mono_choice {A B D: Type}:
    forall (c1 c2: (A -> program B) -> program D),
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
    forall (c1 c2: program B -> program D),
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
    forall (f: (A -> program B) -> A -> program B),
      (forall a, continuous (fun W => f W a)) ->
      continuous f.
  Proof.
    unfold continuous, sseq_continuous, sseq_mono.
    sets_unfold; intros.
    eapply H; eauto.
  Qed.

  Lemma continuous_const {A B C: Type}:
    forall (f: program C),
      continuous (fun (W: A -> program B) => f).
  Proof.
    intros.
    unfold continuous, sseq_continuous, sseq_mono.
    intros.
    sets_unfold; split; intros.
    - exists 0; auto.
    - destruct H0; auto.
  Qed.

  Lemma continuous_const' {B C: Type}:
    forall (f: program C),
      continuous (fun (W: program B) => f).
  Proof.
    intros.
    unfold continuous, sseq_continuous, sseq_mono.
    intros.
    sets_unfold; split; intros.
    - exists 0; auto.
    - destruct H0; auto.
  Qed.

  Lemma continuous_bind {A B D: Type}:
    forall  (c1: (A -> program B) -> program D) (c2: (A -> program B) -> D -> program B),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: A -> program B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, continuous, sseq_continuous, Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    split; intros.
    - destruct H4 as [d [H4 H5]].
      apply H0 in H4; eauto.
      apply H2 in H5; eauto.
      clear H0 H2.
      destruct H4 as [i1 H4].
      destruct H5 as [i2 H5].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        apply increasing_program_le; auto.
      + apply leb_complete_conv in Heq.
        exists i1, d.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        apply increasing_program_le; [lia| auto].
    - destruct H4 as [i [d [H4 H5]]].
      exists d.
      split.
      + apply H0; auto.
        exists i; auto.
      + apply H2; auto.
        exists i; auto.
  Qed.

  Lemma continuous_bind' {B D: Type}:
    forall  (c1: program B -> program D) (c2: program B -> D -> program B),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: program B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, continuous, sseq_continuous, Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    split; intros.
    - destruct H4 as [d [H4 H5]].
      apply H0 in H4; eauto.
      apply H2 in H5; eauto.
      clear H0 H2.
      destruct H4 as [i1 H4].
      destruct H5 as [i2 H5].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        apply increasing_program_le'; auto.
      + apply leb_complete_conv in Heq.
        exists i1, d.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        apply increasing_program_le'; [lia| auto].
    - destruct H4 as [i [d [H4 H5]]].
      exists d.
      split.
      + apply H0; auto.
        exists i; auto.
      + apply H2; auto.
        exists i; auto.
  Qed.

  Lemma continuous_choice {A B D: Type}:
    forall (c1 c2: (A -> program B) -> program D),
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
    forall (c1 c2: program B -> program D),
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
    forall (f: (A -> program B) -> A -> program B),
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
    forall (f: program C),
      mono_cont (fun (W: A -> program B) => f).
  Proof.
    intros.
    unfold mono_cont.
    split; try easy.
    apply continuous_const.
  Qed.

  Lemma mono_cont_const' {B C: Type}:
    forall (f: program C),
      mono_cont (fun (W:program B) => f).
  Proof.
    intros.
    unfold mono_cont.
    split; try easy.
    apply continuous_const'.
  Qed.

  Lemma mono_cont_bind {A B D: Type}:
    forall  (c1: (A -> program B) -> program D) (c2: (A -> program B) -> D -> program B),
      mono_cont c1 ->
      (forall d, mono_cont (fun W => c2 W d)) ->
      mono_cont (fun (W: A -> program B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_bind; try tauto.
      intros d; apply H0.
    - apply continuous_bind; try tauto;
      intros d; apply H0.
  Qed.

  Lemma mono_cont_bind' {B D: Type}:
    forall  (c1: program B -> program D) (c2: program B -> D -> program B),
      mono_cont c1 ->
      (forall d, mono_cont (fun W => c2 W d)) ->
      mono_cont (fun (W: program B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_bind'; try tauto.
      intros d; apply H0.
    - apply continuous_bind'; try tauto;
      intros d; apply H0.
  Qed.

  Lemma mono_cont_choice {A B D: Type}:
    forall (c1 c2: (A -> program B) -> program D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_choice; tauto.
    - apply continuous_choice; tauto.
  Qed.

  Lemma mono_cont_choice' {B D: Type}:
    forall (c1 c2: (program B) -> program D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_choice'; tauto.
    - apply continuous_choice'; tauto.
  Qed.

End mono_and_continuous_lemmas.

Ltac mono_cont_auto_aux :=
  match goal with
  | |- mono_cont (fun (W: ?A -> program ?B) (a: ?A) => _) => apply mono_cont_intro; intros; mono_cont_auto_aux
  | |- mono_cont (fun (W: ?A -> program ?B) => bind _ _) => apply mono_cont_bind; [try mono_cont_auto_aux | intros; try mono_cont_auto_aux]
  | |- mono_cont (fun (W: ?A -> program ?B) => choice _ _) => apply mono_cont_choice; [try mono_cont_auto_aux | try mono_cont_auto_aux]
  | |- mono_cont (fun (W: ?A -> program ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto_aux
  | |- mono_cont (fun (W: ?A -> program ?B) => _) => try apply mono_cont_const; try easy
  end.

Ltac mono_cont_auto_aux' :=
  match goal with
  | |- mono_cont (fun (W: program ?B) => bind _ _) => apply mono_cont_bind'; [try mono_cont_auto_aux' | intros; try mono_cont_auto_aux']
  | |- mono_cont (fun (W: program ?B) => choice _ _) => apply mono_cont_choice'; [try mono_cont_auto_aux' | try mono_cont_auto_aux']
  | |- mono_cont (fun (W: program ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto_aux'
  | |- mono_cont (fun (W: program ?B) => _) => try apply mono_cont_const'; try easy
  end.

Ltac mono_cont_auto :=
  match goal with
  | |- mono_cont (fun (W: ?A -> program ?B) (a: ?A) => _) => mono_cont_auto_aux 
  | |- mono_cont (fun (W: ?A -> program ?B) => _) => mono_cont_auto_aux
  | |- mono_cont (fun (W: program ?B) => _) => mono_cont_auto_aux'
  end.

Section loop_unfold.

  Lemma repeat_break_unfold {A B: Type}:
    forall (body: A -> program (CntOrBrk A B)),
      repeat_break body ==
      fun a =>
        x <- body a;;
        match x with
        | by_continue a' => repeat_break body a'
        | by_break b => ret b
        end.
  Proof.
    intros.
    unfold repeat_break.
    apply (Lfix_fixpoint' (repeat_break_f body)).
    unfold repeat_break_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_unfold_aux {A: Type}:
    forall (hi: nat) (body: nat -> A -> program A),
      (fun '(lo, a) => range_iter lo hi body a) ==
      fun '(lo, a) =>
        choice
        (assume (lo < hi);;
        a' <- body lo a;;
        range_iter (lo+1) hi body a')
        (assume (lo >= hi);;
        ret a).
  Proof.
    intros.
    unfold range_iter.
    assert ((fun '(lo, a) => Lfix (range_iter_f hi body) (lo, a))
      == Lfix (range_iter_f hi body)).
    constructor; destruct a; auto.
    rewrite H.
    apply (Lfix_fixpoint' (range_iter_f hi body)).
    unfold range_iter_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_unfold {A: Type}:
    forall (lo hi: nat) (body: nat -> A -> program A),
      range_iter lo hi body ==
      fun a =>
        choice
        (assume (lo < hi);;
        a' <- body lo a;;
        range_iter (lo+1) hi body a')
        (assume (lo >= hi);;
        ret a).
  Proof.
    intros.
    unfold range_iter.
    pose proof (range_iter_unfold_aux hi body).
    hnf in H.
    intros a.
    specialize (H (lo, a)).
    auto.
  Qed.

  Lemma range_iter_break_unfold_aux {A B: Type}:
    forall (hi: nat) (body: nat -> A -> program (CntOrBrk A B)),
      (fun '(i, a) => range_iter_break i hi body a) ==
      fun '(i, a) =>
        choice
        (assume (i < hi);;
          res <- body i a;;
          match res with
          | by_continue a' => range_iter_break (i+1) hi body a' 
          | by_break b => break b
          end)
        (assume (i >= hi);;
        continue a).
  Proof.
    intros.
    unfold range_iter_break.
    assert ((fun '(i, a) => Lfix (range_iter_break_f hi body) (i, a))
      == Lfix (range_iter_break_f hi body)).
    constructor; destruct a; auto.
    rewrite H.
    apply (Lfix_fixpoint' (range_iter_break_f hi body)).
    unfold range_iter_break_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_break_unfold {A B: Type}:
    forall (lo hi: nat) (body: nat -> A -> program (CntOrBrk A B)),
      (fun a => range_iter_break lo hi body a) ==
      fun a =>
        choice
        (assume (lo < hi);;
          res <- body lo a;;
          match res with
          | by_continue a' => range_iter_break (lo+1) hi body a' 
          | by_break b => break b
          end)
        (assume (lo >= hi);;
        continue a).
  Proof.
    intros.
    unfold range_iter_break.
    pose proof (range_iter_break_unfold_aux hi body).
    hnf in H.
    intros a.
    specialize (H (lo, a)).
    auto.
  Qed.

End loop_unfold.
