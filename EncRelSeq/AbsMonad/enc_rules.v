From SetsClass Require Import SetsClass.
Require Import MonadLib.MonadLib.
Import StateRelMonad.
From EncRelSeq.AbsMonad Require Import hoarelogic encrel.
From EncRelSeq.Basics Require Import semantics basicasrt.


Module NormalDenoAbsMonadEncRules.

Export  EncNormalDenoAbsMonad.

Ltac my_destruct Σₗ Σₕ H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | Σₗ => let σₗ := fresh "σₗ" in destruct H as [σₗ H];my_destruct Σₗ Σₕ H
              | Σₕ => let σₕ := fresh "σₕ" in destruct H as [σₕ H];my_destruct Σₗ Σₕ H
              | program _ _ => let s := fresh "s" in destruct H as [s H];my_destruct Σₗ Σₕ H
              | _ => destruct H as [? H];my_destruct Σₗ Σₕ H
              end
  | (@exp _ ?t ?P) _ => match t with 
              | Σₗ => let σₗ := fresh "σₗ" in destruct H as [σₗ H];my_destruct Σₗ Σₕ H
              | Σₕ => let σₕ := fresh "σₕ" in destruct H as [σₕ H];my_destruct Σₗ Σₕ H
              | program _ => let s := fresh "s" in destruct H as [s H];my_destruct Σₗ Σₕ H
              | _ => destruct H as [? H];my_destruct Σₗ Σₕ H
              end 
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              my_destruct Σₗ Σₕ H;
              my_destruct Σₗ Σₕ H0
  | _ \/ _ => destruct H as [H | H];
              my_destruct Σₗ Σₕ H
  | _ => (discriminate || contradiction  || idtac)
  end.

Local Open Scope asrt_scope. 
(**********************************************************************************)
(*    encode asrt rules                                                           *)
(**********************************************************************************)

Section  EncodeRules.
  Context {Σₗ Σₕ: Type}.
  Context {A: Type}.


Local Open Scope sets_scope.

Ltac destructs H := my_destruct Σₗ Σₕ H.

Lemma alst_hlst_sat : forall  (P: @asrt Σₗ) (P' : @asrt Σₕ)  σₗ σₕ (s: program Σₕ A) , 
 (Alst P && Ahst P') (σₗ, σₕ, s) <-> P σₗ /\ P' σₕ.
Proof.
  unfold Alst, Ahst, andp;split;intros;auto.
Qed.

Lemma aspec_alst_hlst_sat : forall (P: @asrt Σₗ) (P' : @asrt Σₕ) (s: program Σₕ A) σₗ σₕ s', 
 (Aspec s && Alst P && Ahst P') (σₗ, σₕ, s') <-> P σₗ /\ P' σₕ /\ s'= s.
Proof.
  unfold Aspec, Alst, Ahst, andp;split;intros;tauto.
Qed.


Lemma encode_derives: forall X (P: @relasrt Σₗ Σₕ (program Σₕ A)) (P' : @relasrt Σₗ Σₕ (program Σₕ A)),
P |-- P' -> [|P|](X) |-- [|P'|](X).
Proof.
  intros.
  unfold derivable1, encode_asrt.
  intros.
  destructs H0.
  do 2 eexists.
  split;eauto. 
Qed.

Lemma encode_ex_derives: forall {B: Type} X (P: B -> @relasrt Σₗ Σₕ (program Σₕ A)) (P' : B -> @relasrt Σₗ Σₕ (program Σₕ A)),
(forall b, P b |--  P' b) -> EX b, [|P b |](X) |-- EX b,  [|P' b|](X).
Proof.
  unfold exp.
  intros.
  unfold derivable1, encode_asrt.
  intros.
  destructs H0.
  do 3 eexists.
  split;eauto.
  eapply H. eauto. 
Qed.

Lemma encode_alst_andp: forall X (P: @asrt Σₗ) (P' : @asrt Σₕ) (s: program Σₕ A),
 [|Aspec s && Alst P && Ahst P'|](X) --||--  !! (safeExec P' s X) && P. (*// safeexec *)
Proof.
  intros;split.
  { unfold derivable1, andp, coq_prop, encode_asrt, andp, Alst, Ahst, Aspec, safeExec, safe.
  intros.
  destructs H.
  simpl in *.
  subst s0.
  split;auto.
  eexists;
  split;eauto. }

  unfold derivable1, andp, coq_prop, encode_asrt, andp, Alst, Ahst, Aspec, safeExec, safe.
  intros.
  destructs H.
  simpl in *.
  do 2 eexists.
  split;eauto.
Qed.

Lemma encode_andp_split : forall X (x y: @relasrt Σₗ Σₕ (program Σₕ A)), [| x && y |](X) |-- [| x |](X) && [| y |](X).
Proof.
  intros.
  unfold derivable1, encode_asrt, andp.
  intros.
  destructs H.
  split.
  all :do 2 eexists;
      split;eauto. 
Qed.

Lemma encode_andp_merge : forall X (x y: @relasrt Σₗ Σₕ (program Σₕ A)), [| x |](X) && [| y |](X) |-- [| x && y |](X).
Proof.
  intros. 
  unfold derivable1, encode_asrt, andp.
  intros.
  destructs H.
  do 2 eexists;
      split;eauto. 
Abort.
(* ATTENTION : THE REVERSE IS WRONG *)


Lemma encode_exp_intro : forall {A: Type} X (P : A ->  @relasrt Σₗ Σₕ (program Σₕ A)), EX v, [|P v|](X) |-- [|EX v, (P v)|](X) .
Proof.
  intros.
  unfold derivable1, encode_asrt, exp.
  intros.
  destructs H.
  do 2 eexists.
  split;eauto.
Qed.

Lemma encode_expunit_equiv : forall X (P :  @relasrt Σₗ Σₕ (program Σₕ A)), EX (v : unit), [|P|](X) --||-- [|P|](X) .
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


Lemma encode_exp_equiv : forall {A: Type} X (P : A ->  @relasrt Σₗ Σₕ (program Σₕ A)), EX v, [|P v|](X) --||-- [|EX v, (P v)|](X) .
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

Lemma encode_prop_andp : forall (B: Prop) X (P:  @relasrt Σₗ Σₕ (program Σₕ A)), [| !! B && P |](X) --||--  !! B && [| P |](X).
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

(**********************************************************************************)
(*    relation asrt rules                                                         *)
(**********************************************************************************)
Lemma derives_imply_lderi : forall (P P' : @relasrt Σₗ Σₕ (program Σₕ A)) ,
 P |-- P' ->
 (forall X,  [| P |] (X)  |-- [| P' |] (X) ).
Proof.
  unfold derivable1, encode_asrt.
  intros.
  destructs H0.
  do 2 eexists;split;eauto. 
Qed.


Lemma lderi_imply_derives : forall P (P': @asrt Σₗ),
 P |-- P' ->
 @Alst Σₗ Σₕ A P  |-- Alst P' .
Proof.
  unfold derivable1,  Alst.
  intros.
  destruct st as ((? & ?) & ?).
  auto.
Qed.

Lemma hderi_imply_derives : forall P P',
 P |-- P' ->
 @Ahst Σₗ Σₕ A P  |-- Ahst P' .
Proof.
  unfold derivable1,  Ahst.
  intros. destruct st as ((? & ?) & ?). auto.
Qed.

Lemma rhasrt_purelow_equiv : forall B (P: @asrt Σₗ) Ps (Pfrm: @relasrt Σₗ Σₕ (program Σₕ A)) , 
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

Lemma rhasrt_purehigh_equiv : forall B P Ps (Pfrm: @relasrt Σₗ Σₕ (program Σₕ A)), 
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

Lemma rhasrt_exlow_equiv : forall {A: Type} (P: A -> ( Σₗ -> Prop ) ) Ps (Pfrm: @relasrt Σₗ Σₕ (program Σₕ A)), 
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

Lemma rhasrt_exhigh_equiv : forall {A: Type} P (Ps : A -> (Σₕ -> Prop)) (Pfrm: @relasrt Σₗ Σₕ (program Σₕ A)), 
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


Lemma rhasrt_exsepc_equiv : forall {A: Type} (P : A -> @relasrt Σₗ Σₕ (program Σₕ A)) s, 
  EX x,  Aspec s && P x --||--  Aspec s && (EX x, P x).
Proof.
  unfold exp, andp, Aspec, logic_equiv;split;intros;destruct st as ((? & ?) & ?).
  - destructs H.
    splits;auto.
    eexists;eauto.
  - destructs H.
    eexists;splits;eauto.
Qed. 

Lemma rhasrt_propsepc_equiv : forall (P : Prop) s (Pfrm: @relasrt Σₗ Σₕ (program Σₕ A)), 
  !! P && Aspec s && Pfrm --||--  Aspec s && (!! P && Pfrm).
Proof.
  unfold coq_prop, andp, Aspec, logic_equiv;split;intros;destruct st as ((? & ?) & ?).
  - destructs H.
    splits;auto.
  - tauto.
Qed. 

Lemma rh_ex_elim_both : forall {A: Type} (P Q : A -> @relasrt Σₗ Σₕ (program Σₕ A)),
  (forall v, P v |-- Q v) -> EX v, P v |--  EX v, Q v.
Proof.
  unfold exp, derivable1;intros * H * HP.
  destruct st as ((? & ?) & ?).
  destructs HP.
  eexists.
  eapply H;eauto.
Qed.

Lemma rh_prop_andp_andp1: forall P Q (R: @relasrt Σₗ Σₕ (program Σₕ A)),
  (!! P && Q) && R  --||-- !! P && (Q && R).
Proof.
  unfold coq_prop, andp, logic_equiv;intros.
  split;intros.
  + destructs H.
    split;auto.
  + destructs H.
    splits;eauto.
Qed.

End  EncodeRules.

(**********************************************************************************)
(*    hoare rules                                                                 *)
(**********************************************************************************)
Import normaldeno.
Import HoareNormalDeno.
Section  HoareRules.
  Context {Σₗ Σₕ: Type}.
  Context {A: Type}.

  Local Open Scope sets_scope.

  Ltac destructs H := my_destruct Σₗ Σₕ H.



Lemma rh_hoare_conseq : forall c (P P': @relasrt Σₗ Σₕ (program Σₕ A)) Q Q',
  P |-- P' ->
  Q' |--  Q  ->
  ⊢ₑ ⟨ P' ⟩ c ⟨ Q' ⟩ ->
  ⊢ₑ ⟨ P ⟩ c ⟨ Q ⟩.
Proof.
  unfold valid_reltriple, valid_relT; simpl. intros * HP' HQ' HT.
  intros.
  specialize (HT X).
  eapply hoare_conseq;[ | | exact HT].
  eapply encode_derives;eauto.
  eapply encode_derives;eauto.
Qed.

Lemma rh_hoare_exists_l : forall c (A : Type) (P : A -> @relasrt Σₗ Σₕ (program Σₕ A)) P',
  (forall v,  ⊢ₑ ⟨ (P v) ⟩ c ⟨ P' ⟩) ->
  ⊢ₑ ⟨ (exp P) ⟩ c ⟨ P' ⟩.
Proof.
  unfold valid_reltriple, valid_relT, encode_asrt; simpl. intros * HT X.
  unfold valid_triple; intros * HP.
  my_destruct Σₗ Σₕ HP.
  specialize (HT x X st1). 
  assert ((fun σₗ : Σₗ =>
  exists (σₕ : Σₕ) (cₕ : program Σₕ A0),
    safe σₕ cₕ X /\ P x (σₗ, σₕ, cₕ)) st1).
  { do 2 eexists.
    split;eauto.
  }
  specialize (HT H0) as HT.
  auto.
Qed.

Lemma rh_hoare_exists_r : forall c (B : Type) (v : B) P (P' : B ->  @relasrt Σₗ Σₕ (program Σₕ A)),
  ⊢ₑ ⟨ P ⟩ c ⟨ (P' v) ⟩ ->
  ⊢ₑ ⟨ P ⟩ c ⟨ (EX v, P' v) ⟩.
Proof.
  unfold valid_reltriple, valid_relT, encode_asrt; simpl. intros * HT X.
  unfold valid_triple; intros * HP.
  destructs HP. 
  specialize (HT X st1 (ltac:(do 2 eexists; exact (conj HP H)))) as HT.
  intros.
  specialize (HT _ H0) as [? [? ?]].
  destructs H1.
  do 3 eexists;splits;eauto.
  eexists. eauto.
Qed.



(**********************************************************************************)
(*    trans reltriple into hoare triple                                           *)
(**********************************************************************************)
Lemma  reltriple_triple_equiv : forall (P: @asrt Σₗ) Ps (s: program Σₕ A) c Q Ps' s' ,
  ⊢ₑ ⟨ Aspec s && ⌊ P ⌋ && ⌈ Ps ⌉ ⟩ c ⟨ Aspec s' && ⌊ Q ⌋ && ⌈ Ps' ⌉ ⟩ <->
  (forall X : A -> Σₕ -> Prop, 
    ⊢∀ {{!! safeExec Ps s X && P}} c {{!! safeExec Ps' s' X && Q}}).
Proof.
  intros;split.
  - intros.
  specialize (H X).
  eapply hoare_conseq;eauto.
  eapply (logic_equiv_derivable1_2 (encode_alst_andp X P Ps s)).
  apply (logic_equiv_derivable1_1 (encode_alst_andp X Q Ps' s')).
  - unfold valid_reltriple, valid_relT; intros.
    specialize (H X).
    eapply hoare_conseq;eauto.
    apply (logic_equiv_derivable1_1 (encode_alst_andp X P Ps s)).
    apply (logic_equiv_derivable1_2 (encode_alst_andp X Q Ps' s')).
Qed.

Lemma  reltriple_triple_equiv1 : forall (P: @asrt Σₗ) Ps (s: program Σₕ A) c Q,
  ⊢ₑ ⟨ Aspec s && ⌊ P ⌋ && ⌈ Ps ⌉ ⟩ c ⟨ Q ⟩ <->
  (forall X : A -> Σₕ -> Prop,
    ⊢∀ {{!! safeExec Ps s X && P}} c {{[|Q|](X)}}).
Proof.
  intros;split.
  - intros.
  specialize (H X).
  eapply hoare_conseq;eauto.
  apply (logic_equiv_derivable1_2 (encode_alst_andp X P Ps s)).
  reflexivity.
  - unfold valid_reltriple, valid_relT; intros.
    specialize (H X).
    eapply hoare_conseq;eauto.
    apply (logic_equiv_derivable1_1 (encode_alst_andp X P Ps s)).
    reflexivity.
Qed.

End HoareRules.

Section  composition_rules.

  Context {Σₗ Σₕ: Type}.
  Context {A: Type}.

  Local Open Scope asrt_scope.
  Import MonadNotation.
  Local Open Scope monad.
  Import HoareNormalDeno.
  

  Definition link {Σₗ Σₕ: Type} (P: @binasrt Σₗ Σₕ) (P': @asrt Σₕ) : @asrt Σₗ:=
    fun σₗ =>  exists σₕ, P (σₗ, σₕ) /\  P' σₕ.


(*************************************************************************************)
(*    vertical composition rule                                                      *)
(*                                                                                   *)
(*  ⟨ P * cₕ ⟩  c  ⟨ ∃ a. Q a * (return a) ⟩                   { Pₕ } cₕ {λ a. Qₕ a }   *)
(* ________________________________________________________________________________  *)
(* {λ σₗ. ∃ σₕ. P(σₗ, σₕ) /\ Pₕ' (σₕ) } c {λ σₗ. ∃ σₕ a. Q a (σₗ, σₕ) /\ Qₕ a (σₕ) }        *)
(*************************************************************************************)
Lemma rh_hoare_vc :forall (s: @denosem Σₗ) (sₕ : program Σₕ A) P Q Pₕ Qₕ,
 valid_reltriple  (lift P sₕ) s ( EX x, lift (Q x) (return x)) ->
 Hoare Pₕ sₕ Qₕ ->
 valid_triple ( link P Pₕ) 
                s 
                (EX x, link (Q x) (Qₕ x)).
Proof.
  unfold valid_reltriple; intros * HRT HHT.
  unfold valid_triple.
  intros *  HP.
  destruct HP as [σₕ [? HPH]].
  (*将high level 终止状态指定为满足条件的初始状态经过从cₕ能到达的集合*)
  specialize (HRT (fun r (x: Σₕ) => sₕ σₕ r x) st1 ).
  assert (([|lift P sₕ|](fun (r : A) (x : Σₕ) => sₕ σₕ r x)) st1).
  { unfold encode_asrt, lift.
    exists σₕ, sₕ.
    split;auto.
    unfold safe;auto. }
  specialize (HRT H0) as HRT. clear H0.
  intros * Hceval.
  specialize (HRT _ Hceval) as  [a HRQ].
  unfold encode_asrt, lift in *.
  destruct HRQ as  [cₕ' [? [? [? ?]]]]. subst cₕ'.
  unfold safe in H0.
  do 2 eexists.
  split;eauto.
  eapply HHT;eauto.
  apply H0.
  unfold_monad;auto.
Qed.


End composition_rules.
End  NormalDenoAbsMonadEncRules.
  

  











