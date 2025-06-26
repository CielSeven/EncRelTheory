Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From MonadLib.MonadErr Require Import MonadErrBasic.

Import Monad MonadNotation SetsNotation.
Local Open Scope sets.
Local Open Scope monad.
Export CPO_lift.
Local Open Scope order_scope.

(*************************************************************************************************************)
(**********************************          monad program registerd         *********************************)
(**********************************                program Σ A               *********************************)
(**********************************   class                                  *********************************)
(**********************************     1 : Order                            *********************************)
(**********************************       1.1 : Transitive                   *********************************)
(**********************************       1.2 : Reflexiitive                 *********************************)
(**********************************     2 : PartialOrder_Setoid              *********************************)
(**********************************     3 : OmegaCompletePartialOrder_Setoid *********************************)
(*************************************************************************************************************)

#[export] Instance oLub_program {Σ A: Type} : OmegaLub (MonadErr.M Σ A) :=
  ProgramPO.indexed_union.

#[export] Instance bot_program {Σ A: Type} : Bot (MonadErr.M Σ A) :=
  ProgramPO.bot.

#[export] Instance oCPO_program {Σ A: Type} : CompletePartialOrder_Setoid (MonadErr.M Σ A).
Proof.
  split.
  + apply program_PO.
  + unfold seq_mono, seq_least_upper_bound, seq_upper_bound.
    unfold omega_lub, order_rel, program_order, oLub_program; simpl.
    intros T H.
    split.
    - intros n.
      specialize (H n) as [H H1].
      constructor;simpl in *. 
      * sets_unfold. intros.
        exists n.
        tauto.
      * sets_unfold. intros.
        exists n.
        tauto.
    - intros a H0.
      constructor;simpl in *.
      * sets_unfold.
        intros.
        destruct H1 as [n ?].
        specialize (H0 n) as [H0 _]. eapply H0;eauto.
      * sets_unfold.
        intros.
        destruct H1 as [n ?].
        specialize (H0 n) as [_ H0]. eapply H0;eauto.
  + unfold least_element.
    unfold bot, order_rel, program_order, bot_program; simpl.
    intros a.
    constructor;simpl.
    sets_unfold. 
    tauto.
    sets_unfold. 
    tauto.
Qed.

(*************************************************************************************************************)
(**********************************     lift monad program registerd         *********************************)
(**********************************           B -> program Σ A               *********************************)
(**********************************   class                                  *********************************)
(**********************************     1 : Order                            *********************************)
(**********************************       1.1 : Transitive                   *********************************)
(**********************************       1.2 : Reflexiitive                 *********************************)
(**********************************     2 : PartialOrder_Setoid              *********************************)
(**********************************     3 : OmegaCompletePartialOrder_Setoid *********************************)
(*************************************************************************************************************)
#[export] Instance Transitive_lift  {A: Type} {B: Type} {RB: Order B} {TB: Transitive (@order_rel B _) } 
  : Transitive (@order_rel (A -> B) _ ).
Proof.
  unfold Transitive, order_rel, R_lift, LiftConstructors.lift_rel2.
  intros.
  etransitivity;eauto.
Qed.

#[export] Instance Reflexive_lift  {A: Type} {B: Type} {RB: Order B} {ReflB: Reflexive (@order_rel B _) } 
  : Reflexive (@order_rel (A -> B) _ ).
Proof.
  unfold Reflexive, order_rel, R_lift, LiftConstructors.lift_rel2.
  intros.
  reflexivity.
Qed.



(*************************************************************************************************************)
(**********************************     mono and continuous_lemmas           *********************************)
(*************************************************************************************************************)
Section mono_and_continuous_lemmas.
  Import MonadErr.
  Import MonadNotation.
  Context {Σ: Type}.

  Notation " ⋃  a " := (omega_lub a): order_scope.

  Definition increasing {A: Type} {RA: Order A } (T : nat -> A):= @seq_mono A RA T.

  Definition mono {A: Type} {RA: Order A}  {B: Type} {RB: Order B}  
    (f : A -> B) := Proper (order_rel ==> order_rel) f.
  Definition continuous {A: Type} {RA: Order A} {oLubA: OmegaLub A}
          {B: Type} {EB: Equiv B} {oLubB: OmegaLub B}
    (f : A -> B) := @seq_continuous  A RA oLubA B EB oLubB f.
  Definition mono_cont {A: Type} {RA: Order A} {oLubA: OmegaLub A} {B: Type} {RB: Order B} {EB: Equiv B} {oLubB: OmegaLub B}
    (f : A -> B) := mono f /\ continuous f.

  Lemma BW_fixpoint'{A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Setoid A} f:
    mono_cont f ->
    BW_fix f == f (BW_fix f).
  Proof.
    unfold mono_cont; intros.
    apply BourbakiWitt_fixpoint; tauto.
  Qed.

  Lemma increasing_program_plus : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    increasing c -> c n <= c (n + m).
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
    (n <= m)%nat ->  increasing c  -> c n <= c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus;auto.
  Qed.

  Lemma increasing_program_plus' : forall {B:Type} (m n: nat) (c: nat -> program Σ B), 
    increasing c -> c n <= c (n + m).
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
    (n <= m)%nat ->  increasing c  -> c n <= c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus' ;auto.
  Qed.

  Lemma mono_intro {A B: Type}:
    forall (f: (A -> program Σ B) -> A -> program Σ B),
      (forall a, mono (fun W => f W a)) ->
      mono f.
  Proof.
    unfold mono, Proper, respectful.
    unfold order_rel, R_lift, LiftConstructors.lift_rel2, order_rel.
    sets_unfold; intros.
    eapply H; auto.
  Qed.

  Lemma mono_bind {A B D: Type}:
    forall  (c1: (A -> program Σ B) -> program Σ D) (c2: (A -> program Σ B) -> D -> program Σ B),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: A -> program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful.
    intros.
    specialize (H x y H1).
    inversion H. 
    constructor; unfold_monad. 
    - unfold nrm_nrm.
      intros s0 b s2 [d [s1 [Hc1 Hc2]]].
      apply nrmle in Hc1.
      specialize (H0 d x y H1).
      inversion H0.
      apply nrmle0 in Hc2.
      exists d, s1.
      tauto.
    - unfold nrm_err; sets_unfold.
      intros s [? | [d [s1 [Hn He]]]].
      + apply errle in H2; tauto.
      + specialize (H0 d x y H1).
        inversion H0.
        apply nrmle in Hn.
        apply errle0 in He.
        right; exists d, s1.
        tauto.
  Qed.

  Lemma mono_bind' {B D: Type}:
    forall  (c1: (program Σ B) -> program Σ D) (c2: (program Σ B) -> D -> program Σ B),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful.
    intros.
    specialize (H x y H1).
    inversion H. 
    constructor; simpl; unfold_monad. 
    - unfold nrm_nrm.
      intros s0 b s2 [d [s1 [Hc1 Hc2]]].
      apply nrmle in Hc1.
      specialize (H0 d x y H1).
      inversion H0.
      apply nrmle0 in Hc2.
      exists d, s1.
      tauto.
    - unfold nrm_err; sets_unfold.
      intros s [? | [d [s1 [Hn He]]]].
      + apply errle in H2; tauto.
      + specialize (H0 d x y H1).
        inversion H0.
        apply nrmle in Hn.
        apply errle0 in He.
        right; exists d, s1.
        tauto.
  Qed.

  Lemma mono_choice {A B D: Type}:
    forall (c1 c2: (A -> program Σ B) -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful, choice.
    intros.
    specialize (H x y H1).
    specialize (H0 x y H1).
    constructor; simpl; sets_unfold.
    - intros s0 d s1 [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
    - intros s [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
  Qed.

  Lemma mono_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful, choice.
    intros.
    specialize (H x y H1).
    specialize (H0 x y H1).
    constructor; simpl; sets_unfold.
    - intros s0 d s1 [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
    - intros s [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
  Qed.

  Lemma continuous_intro {A B: Type}:
    forall (f: (A -> program Σ B) -> A -> program Σ B),
      (forall a, continuous (fun W => f W a)) ->
      continuous f.
  Proof.
    unfold continuous, seq_continuous, seq_mono.
    intros.
    do 2 constructor; intros; apply H in H1; tauto.
  Qed.

  Lemma continuous_const {A B C: Type}:
    forall (f: program Σ C),
      continuous (fun (W: A -> program Σ B) => f).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono.
    intros.
    do 2 constructor; 
    unfold omega_lub, oLub_program, ProgramPO.indexed_union;
    sets_unfold; simpl; intros.
    exists 0; auto.
    destruct H0; auto.
    exists 0; auto.
    destruct H0; auto.
  Qed.

  Lemma continuous_const' {B C: Type}:
    forall (f: program Σ C),
      continuous (fun (W: program Σ B) => f).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono.
    intros.
    do 2 constructor; 
    unfold omega_lub, oLub_program, ProgramPO.indexed_union;
    sets_unfold; simpl; intros.
    exists 0; auto.
    destruct H0; auto.
    exists 0; auto.
    destruct H0; auto.
  Qed.

  Lemma continuous_bind {A B D: Type}:
    forall  (c1: (A -> program Σ B) -> program Σ D) (c2: (A -> program Σ B) -> D -> program Σ B),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: A -> program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, continuous, seq_continuous, Proper, respectful.
    unfold_monad; intros.
    specialize (H0 T H3).
    constructor; 
    unfold nrm_nrm, nrm_err;
    simpl;
    sets_unfold; [intros s0 b s2 | intros s]; split.
    - intros [d [s1 [Hc1 Hc2]]].
      specialize (H2 d T H3).
      apply H0 in Hc1; simpl in Hc1; sets_unfold in Hc1.
      apply H2 in Hc2; simpl in Hc2; sets_unfold in Hc2.
      destruct Hc1 as [i1 Hc1].
      destruct Hc2 as [i2 Hc2].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d, s1.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        apply increasing_program_le; auto.
      + exists i1, d, s1.
        apply leb_complete_conv in Heq.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        apply increasing_program_le; [lia| auto].
    - intros [i [d [s1 [Hc1 Hc2]]]].
      exists d, s1.
      split.
      apply H0.
      econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
    - intros [Hc1 | [d [s1 [Hc1 Hc2]]]].
      {
        apply H0 in Hc1.
        inversion Hc1.
        exists x; tauto.
      }
      apply H0 in Hc1.
      apply H2 in Hc2; auto.
      inversion Hc1.
      inversion Hc2; rename x0 into y.
      destruct (x <=? y) eqn:Heq.
      + apply leb_complete in Heq.
        exists y; right.
        exists d, s1.
        split; auto.
        apply H with (x:= T x); auto.
        apply increasing_program_le; auto.
      + apply leb_complete_conv in Heq.
        exists x; right.
        exists d, s1.
        split; auto.
        apply H1 with (x:= T y); auto.
        apply increasing_program_le; [lia | auto].
    - intros [i [Hc1 | [d [s1 [Hc1 Hc2]]]]].
      {
        left; apply H0.
        econstructor; eauto.
      }
      right; exists d, s1.
      split.
      apply H0; econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
  Qed.

  Lemma continuous_bind' {B D: Type}:
    forall  (c1: program Σ B -> program Σ D) (c2: program Σ B -> D -> program Σ B),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, continuous, seq_continuous, Proper, respectful.
    unfold_monad; intros.
    specialize (H0 T H3).
    constructor; 
    unfold nrm_nrm, nrm_err;
    simpl;
    sets_unfold; [intros s0 b s2 | intros s]; split.
    - intros [d [s1 [Hc1 Hc2]]].
      specialize (H2 d T H3).
      apply H0 in Hc1; simpl in Hc1; sets_unfold in Hc1.
      apply H2 in Hc2; simpl in Hc2; sets_unfold in Hc2.
      destruct Hc1 as [i1 Hc1].
      destruct Hc2 as [i2 Hc2].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d, s1.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        apply increasing_program_le'; auto.
      + exists i1, d, s1.
        apply leb_complete_conv in Heq.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        apply increasing_program_le'; [lia| auto].
    - intros [i [d [s1 [Hc1 Hc2]]]].
      exists d, s1.
      split.
      apply H0.
      econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
    - intros [Hc1 | [d [s1 [Hc1 Hc2]]]].
      {
        apply H0 in Hc1.
        inversion Hc1.
        exists x; tauto.
      }
      apply H0 in Hc1.
      apply H2 in Hc2; auto.
      inversion Hc1.
      inversion Hc2; rename x0 into y.
      destruct (x <=? y) eqn:Heq.
      + apply leb_complete in Heq.
        exists y; right.
        exists d, s1.
        split; auto.
        apply H with (x:= T x); auto.
        apply increasing_program_le'; auto.
      + apply leb_complete_conv in Heq.
        exists x; right.
        exists d, s1.
        split; auto.
        apply H1 with (x:= T y); auto.
        apply increasing_program_le'; [lia | auto].
    - intros [i [Hc1 | [d [s1 [Hc1 Hc2]]]]].
      {
        left; apply H0.
        econstructor; eauto.
      }
      right; exists d, s1.
      split.
      apply H0; econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
  Qed.

  Lemma continuous_choice {A B D: Type}:
    forall (c1 c2: (A -> program Σ B) -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold continuous, seq_continuous.
    unfold choice; intros.
    specialize (H T H1).
    specialize (H0 T H1).
    do 2 constructor; simpl; sets_unfold.
    - intros [? | ?].
      + apply H in H2.
        inversion H2.
        eexists; eauto.
      + apply H0 in H2.
        inversion H2.
        eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
    - intros [? | ?].
      apply H in H2.
      inversion H2.
      eexists; eauto.
      apply H0 in H2.
      inversion H2.
      eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
  Qed.

  Lemma continuous_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold continuous, seq_continuous.
    unfold choice; intros.
    specialize (H T H1).
    specialize (H0 T H1).
    do 2 constructor; simpl; sets_unfold.
    - intros [? | ?].
      + apply H in H2.
        inversion H2.
        eexists; eauto.
      + apply H0 in H2.
        inversion H2.
        eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
    - intros [? | ?].
      apply H in H2.
      inversion H2.
      eexists; eauto.
      apply H0 in H2.
      inversion H2.
      eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
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

End mono_and_continuous_lemmas.

Ltac mono_cont_auto_aux :=
  match goal with
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => bind _ _) => apply mono_cont_bind; [try mono_cont_auto_aux | intros; try mono_cont_auto_aux]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => choice _ _) => apply mono_cont_choice; [try mono_cont_auto_aux | try mono_cont_auto_aux]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto_aux
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => _) => try apply mono_cont_const; try easy
  end.

Ltac mono_cont_auto_aux' :=
  match goal with
  | |- mono_cont (fun (W: program ?Σ ?B) => bind _ _) => apply mono_cont_bind'; [try mono_cont_auto_aux' | intros; try mono_cont_auto_aux']
  | |- mono_cont (fun (W: program ?Σ ?B) => choice _ _) => apply mono_cont_choice'; [try mono_cont_auto_aux' | try mono_cont_auto_aux']
  | |- mono_cont (fun (W: program ?Σ ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto_aux'
  | |- mono_cont (fun (W: program ?Σ ?B) => _) => try apply mono_cont_const'; try easy
  end.

Ltac mono_cont_auto :=
  match goal with
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) _ => _) => apply mono_cont_intro; intros; mono_cont_auto_aux
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => _) => mono_cont_auto_aux
  | |- mono_cont (fun (W: program ?Σ ?B) => _) => mono_cont_auto_aux'
  end.

(*************************************************************************************************************)
(**********************************          while op for state monad        *********************************)
(**********************************                 program Σ A              *********************************)
(**********************************   1. while cond body :                   *********************************)
(**********************************            program Σ unit                *********************************)
(**********************************   2. whileret cond body :                *********************************)
(**********************************            A -> program Σ A              *********************************)
(**********************************   3. repeat_break body :                   *********************************)
(**********************************            A -> program Σ B              *********************************)
(*************************************************************************************************************)

Section  while_monad.

  Context {Σ: Type}.

  Definition while_f (cond: (program Σ bool))  (body : (program Σ unit)) 
                     (W : (program Σ unit)) 
                        : (program Σ unit) :=
  (x <- cond ;; (match x with 
  | true => body;; W
  | false => ret tt
  end)).

  Definition while (cond: (program Σ bool)) (body : program Σ unit)  := BW_fix (while_f cond body).

  Definition whileret_f {A: Type}  (cond: A -> (program Σ bool)) (body : A -> (program Σ A)) 
                     (W :  A -> program Σ A) 
                        : A -> program Σ A :=
  fun a => (x <- (cond a) ;; match x with 
  | true =>  bind (body a) W
  | false => (ret a)
  end).

  Definition continue {A B: Type} (a: A): (program Σ (CntOrBrk A B)) := (ret (by_continue a)).
  Definition break {A B: Type} (b: B): (program Σ (CntOrBrk A B)) := (ret (by_break b)).

  Definition whileret {A: Type}  (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  := BW_fix (whileret_f cond body).

  Definition repeat_break_f {A B: Type} (body: A -> program Σ (CntOrBrk A B)) (W: A -> program Σ B): A -> program Σ B :=
    fun a =>
      x <- body a;;
      match x with
      | by_continue a' => W a'
      | by_break b => ret b
      end.

  Definition repeat_break {A B: Type} (body: A -> program Σ (CntOrBrk A B)): A -> program Σ B :=
    BW_fix (repeat_break_f body).

  Definition range_iter_f {A: Type} (hi: Z) (body: Z -> A -> program Σ A) (W: (Z * A) -> program Σ A): (Z * A) -> program Σ A :=
    fun '(lo, a0) => 
      choice
        (assume!! (lo < hi)%Z;;
         a1 <- body lo a0;;
         W ((lo + 1)%Z, a1))
        (assume!! (lo >= hi)%Z;;
         ret a0).

  Definition range_iter {A: Type} (lo hi: Z) (body: Z -> A -> program Σ A): A -> program Σ A :=
    fun a => BW_fix (range_iter_f hi body) (lo, a).

  Definition range_iter_break_f {A B: Type} (hi: Z) 
    (body: Z -> A -> program Σ (CntOrBrk A B)) 
    (W: Z * A -> program Σ (CntOrBrk A B)): 
      Z * A -> program Σ (CntOrBrk A B) :=
    fun '(lo, a0) => 
      choice
        (assume!! (lo < hi)%Z;;
         ab <- body lo a0;;
         match ab with
         | by_continue a1 => W ((lo + 1)%Z, a1)
         | by_break b => break b
         end)
        (assume!! (lo >= hi)%Z;;
         continue a0).

  Definition range_iter_break {A B: Type} (lo hi: Z) 
    (body: Z -> A -> program Σ (CntOrBrk A B)): 
      A -> program Σ (CntOrBrk A B) :=
    fun a => BW_fix (range_iter_break_f hi body) (lo, a).

  Definition Repeat_f  (body : (program Σ unit)) 
                      (W : (program Σ unit)) 
                          : (program Σ unit) :=
    W ;; body.

  Definition Repeat (body : (program Σ unit))  := BW_fix (Repeat_f body).

  Definition ret_some {A: Type} (a: option A): program Σ bool :=
    match a with 
    | Some _ => ret true
    | None => ret false
    end.

  Lemma while_unfold: forall (cond: (program Σ bool)) (body : program Σ unit), 
  while cond body == (x <- cond ;;
                      match x with
                      | true => body ;; (while cond body)
                      | false => ret tt
                      end).
  Proof.
    intros.
    unfold while.
    apply (BW_fixpoint' (while_f cond body)).
    unfold while_f.
    mono_cont_auto.
  Qed.
  
  Lemma whileret_unfold: forall {A: Type} (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  (a: A), 
    whileret cond body == fun a => (x <- (cond a);; 
                             match x with 
                             | true => y <- body a ;; whileret cond body y
                             | false => ret a
                             end).
  Proof.
    intros.
    unfold whileret.
    apply (BW_fixpoint' (whileret_f cond body)).
    unfold whileret_f.
    mono_cont_auto.
  Qed.

  Lemma repeat_break_unfold {A B: Type}:
    forall (body: A -> program Σ (CntOrBrk A B)),
    repeat_break body == fun a =>
                        x <- body a;; 
                        match x with
                        | by_continue a0 => repeat_break body a0
                        | by_break b0 => ret b0
                        end.
  Proof.
    intros.
    unfold repeat_break.
    apply (BW_fixpoint' (repeat_break_f body)).
    unfold repeat_break_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_unfold_aux:
    forall {A: Type} (hi: Z) (body: Z -> A -> program Σ A),
    (fun '(lo, a) => range_iter lo hi body a) ==
    fun '(lo, a) => choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      range_iter (lo + 1)%Z hi body b)
      (assume!! (lo >= hi)%Z;;
      ret a).
  Proof.
    intros. unfold range_iter.
    assert ((fun '(lo, a) => BW_fix (range_iter_f hi body) (lo, a))
      == BW_fix (range_iter_f hi body)).
    constructor; destruct a; easy.
    rewrite H.
    apply (BW_fixpoint' (range_iter_f hi body)).
    unfold range_iter_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_unfold:
    forall {A: Type} (hi: Z) (body: Z -> A -> program Σ A) lo a,
    range_iter lo hi body a ==
    choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      range_iter (lo + 1)%Z hi body b)
      (assume!! (lo >= hi)%Z;;
      ret a).
  Proof.
    intros.
    pose proof (range_iter_unfold_aux hi body).
    unfold equiv in H; simpl in H.
    unfold Equiv_lift, LiftConstructors.lift_rel2 in H.
    specialize (H (lo, a)).
    auto.
Qed.

  Lemma range_iter_break_unfold_aux:
    forall {A B: Type} (hi: Z) (body: Z -> A -> program Σ (CntOrBrk A B)),
    (fun '(lo, a) => range_iter_break lo hi body a) ==
    fun '(lo, a) => choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      match b with
      | by_continue a' => range_iter_break (lo + 1)%Z hi body a'
      | by_break b' => break b'
      end)
      (assume!! (lo >= hi)%Z;;
      continue a).
  Proof.
    intros. unfold range_iter_break.
    assert ((fun '(lo, a) => BW_fix (range_iter_break_f hi body) (lo, a))
      == BW_fix (range_iter_break_f hi body)).
    constructor; destruct a; easy.
    rewrite H.
    apply (BW_fixpoint' (range_iter_break_f hi body)).
    unfold range_iter_break_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_break_unfold:
    forall {A B: Type} (hi: Z) (body: Z -> A -> program Σ (CntOrBrk A B)) lo a,
    range_iter_break lo hi body a ==
    choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      match b with
      | by_continue al => range_iter_break (lo + 1)%Z hi body al
      | by_break br => break br
      end)
      (assume!! (lo >= hi)%Z;;
      continue a).
  Proof.
    intros.
    pose proof (range_iter_break_unfold_aux hi body).
    unfold equiv in H; simpl in H.
    unfold Equiv_lift, LiftConstructors.lift_rel2 in H.
    specialize (H (lo, a)).
    auto.
  Qed.

End  while_monad.

Ltac unfold_loop H :=
  rewrite (while_unfold _ _ ) in H ||
  rewrite (repeat_break_unfold _ _) in H ||
  rewrite range_iter_unfold in H ||
  rewrite range_iter_break_unfold in H.
