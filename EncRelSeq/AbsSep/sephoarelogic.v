From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import semantics basicasrt safeexec_lib hoarelogic encrel.



Import SetsNotation.
Local Open Scope sets_scope.
Local Open Scope asrt_scope.


Module SepHoareLogic.

Import HoarePracticalDeno.
Section  seplogic.

  Context {Σ : Type}.
  Context `{mc: @JoinM Σ}.

  Definition safety_mono (c: (@denosem Σ)) : Prop :=
    forall m mf n, 
      join m mf n -> 
      ((~ c.(err) m) -> (~ c.(err) n)) /\
      ((exists m', c.(nrm) m m') ->
      (exists n', c.(nrm) n n')).
  
  Definition frame_property (c: (@denosem Σ)) : Prop :=
    forall m mf n n', 
      join m mf n -> 
      (~ c.(err) m) ->
      c.(nrm) n n' ->
      exists m', c.(nrm) m m' /\ join m' mf n'.

  Lemma hoare_frame : forall c (P Q F: @asrt Σ),
    safety_mono c -> frame_property c ->
    ⊢∀ {{P}} c  {{ Q}} -> 
    ⊢∀ {{P ** F}} c  {{ Q ** F}}.
  Proof.
    intros * Hsafe Hframe.
    unfold valid_triple, basicasrt.sepcon. simpl.
    intros.
    destruct H0 as [st2 [st3 [? [? ?]]]].
    specialize (H st2 H1) as [? ?].
    split.
    - eapply Hsafe;eauto.
    - intros.
      specialize (Hframe _ _ _ _ H0 H H4) as [st4 [? ?]].
      do 2 eexists.
      split;eauto.
  Qed.


End  seplogic.
End SepHoareLogic.




Module SepRelHoarePracticalDeno.

Export HoarePracticalDeno.

Section  seprelational.
  Context {Σ₁ Σ₂: Type}.
  Context `{mc: @JoinM Σ₂}.
  Context `{jma: @JoinMAxioms Σ₂ mc}.

Definition valid_quadruples  (P: @binasrt Σ₁ Σ₂ ) (c₁: denosem) (c₂: denosem) (Q: @binasrt Σ₁ Σ₂) :=
  forall st1 st1', 
    forall stm stf, join stm stf st1' ->
    P (st1, stm) -> (c₁.(err) st1 -> c₂.(err) st1') /\
  forall st2, c₁.(nrm) st1 st2 -> (c₂.(err) st1' \/ 
    exists st2', c₂.(nrm) st1' st2' /\ 
    exists stm2, join stm2 stf st2' /\ Q (st2, stm2) ).


Definition sem_eval {Σ: Type} (σ₁ : Σ) (c₁: @denosem Σ) (σ₂ : Σ) (c₂: @denosem Σ) : Prop :=
  (forall σ₃, c₂.(nrm) σ₂ σ₃ -> c₁.(nrm) σ₁ σ₃) /\ 
  (c₂.(err) σ₂ -> c₁.(err) σ₁).

Notation " '(-' x , y '-)' '↪' '(-' u , z '-)'" := (sem_eval x y u z).

Definition valid_RelTriples (P: @relasrt Σ₁ Σ₂ (@denosem Σ₂)) (c₁: @denosem Σ₁) (Q: @relasrt Σ₁ Σ₂ (@denosem Σ₂)) :=
  forall st1 st1' (c₂: (@denosem Σ₂)) ,
    forall stm stf, join stm stf st1' ->
    P (st1, stm, c₂) -> (c₁.(err) st1 -> c₂.(err) st1') /\
  forall st2, c₁.(nrm) st1 st2 -> (c₂.(err) st1' \/ 
    exists st2' c₂', (- st1', c₂ -) ↪ (- st2', c₂' -) /\ 
    exists stm2, join stm2 stf st2' /\ Q (st2, stm2, c₂')).

Notation " '⊢' '{{' P '}}' cₗ '≾' cₕ '{{' Q '}}'" := (valid_quadruples P cₗ cₕ Q) (at level 71, no associativity).
Notation " '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_RelTriples P c Q) (at level 71, no associativity).

Import PracticalDenoConstructs.
Lemma quadruple2reltriple : forall (P: @binasrt Σ₁ Σ₂ ) (cₗ: (@denosem Σ₁))  (cₕ: @denosem Σ₂ )  (Q :  @binasrt Σ₁ Σ₂),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ ⟨ lift P cₕ ⟩ cₗ ⟨ lift Q skip ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      intros HQ lst1 hst1 cₕ' hstm hstf Hjoin [HP ?].
      subst.
      specialize (HQ _ _ _ _ Hjoin HP) as [HQerr HQnrm].
      split;auto.
      intros lst2 Hleval.
      specialize (HQnrm _ Hleval) as [ | (hst2 & Hheval & [stm2 [Hjoin' HQ]])];auto.
      right.
      unfold lift.
      do 2 eexists.
      split;eauto.
      unfold sem_eval.
      split.
      + intros.
        cbn in H.
        sets_unfold in H. subst.
        auto.
      + cbn. sets_unfold. tauto.  
    - unfold valid_RelTriples, valid_quadruples, lift.
      intros HT lst1 hst1 hstm hstf Hjoin HP.
      specialize (HT lst1 hst1 _ hstm hstf Hjoin (ltac:(split;auto))) as [HTerr HTnrm].
      split;auto.
      intros lst2 Hleval.
      specialize (HTnrm _ Hleval) as [ | (hst2 & ? & Hheval & stm2 & Hjoin' & HQ & ?)];[auto | right].
      subst.
      eexists.
      split;eauto.
      eapply Hheval.
      cbn. sets_unfold. auto.
  Qed.

  Lemma relHoare_frame {A: Type}: 
    forall P Ps Q Qs F c (cₕ cₕ': @denosem Σ₂ ) (B: A -> Prop),
    ⊢ ⟨ Aspec cₕ && ⌊ P ⌋ && ⌈ Ps  ⌉ ⟩ 
        c 
      ⟨EX (a: A), !! (B a) && Aspec cₕ' && ⌊ Q a ⌋ && ⌈ Qs a⌉ ⟩ ->
    ⊢ ⟨ Aspec cₕ && ⌊ P ⌋ && ⌈ Ps ** F ⌉ ⟩ 
        c 
      ⟨EX (a: A), !! (B a) && Aspec cₕ' && ⌊ Q a ⌋ && ⌈ (Qs a) ** F ⌉ ⟩.
  Proof.
    intros.
    unfold valid_RelTriples.
    intros lst1 hst1 cₕ'' hstm hstf Hjoin HP.
    apply aspec_alst_hlst_sat in HP.
    destruct HP as [? [? ?]].
    subst.
    unfold sepcon in H1.
    destruct H1 as [hstm1 [hstmf [Hjoin1 [? ?]]]].
    unfold valid_RelTriples in H.
    pose proof (join_assoc _ _ _ _ _ Hjoin1 Hjoin) as [hstmff [? ?]].
    specialize (H lst1 hst1 cₕ hstm1 hstmff H4).
    assert ((Aspec cₕ && ⌊ P ⌋ && ⌈ Ps ⌉) (lst1, hstm1, cₕ)). { apply aspec_alst_hlst_sat;auto. }
    specialize (H H5) as [Herr Hnrm]. clear H5.
    split;auto.
    intros lst2 Heval.
    specialize (Hnrm lst2 Heval) as [? | Hnrm].
    left;auto.
    right.
    destruct Hnrm as [hst2 [cₕ'' [? [ hst2m [Hjoin2 ? ]]]]].
    unfold basicasrt.exp, basicasrt.coq_prop, basicasrt.andp, Alst, Ahst, Aspec in H5.
    destruct H5 as [a [[[? ?] ?] ?]].
    subst.
    exists hst2 , cₕ'.
    split;auto.
    apply join_comm in Hjoin2. apply join_comm in H3.
    pose proof (join_assoc _ _ _ _ _ H3 Hjoin2) as [hst2mf [? ?]].
    apply join_comm in H9.
    exists hst2mf.
    split;auto.
    unfold basicasrt.exp, basicasrt.coq_prop, basicasrt.andp, basicasrt.sepcon, Alst, Ahst, Aspec.
    exists a.
    split;eauto.
    exists hst2m ,hstmf.
    split;auto.
    apply join_comm;auto.
  Qed.

End seprelational.

End SepRelHoarePracticalDeno.   


Module SepPracticalDenoExecLib.
Import practicaldeno.
Import SepHoareLogic.
(*************************************************************************************************************)
(******************************* safe termination states set (safe σ c X)   **********************************)
(*************************************************************************************************************)
Definition weakestpre {Σ: Type} (c: @denosem Σ) X : Σ -> Prop :=
    fun σ => ~ c.(err) σ /\ forall σ', c.(nrm) σ σ' -> σ' ∈ X.


Definition safe {Σ: Type}  (σ : Σ) (c: @denosem Σ) X := 
    ~ c.(err) σ /\
    forall σ', c.(nrm) σ σ' -> σ' ∈ X.
    
Lemma safe_equiv_weakestpre: forall {Σ: Type} (c: @denosem Σ) X (σ : Σ) ,
   (weakestpre c X) σ <-> safe σ c X.
Proof.
  unfold weakestpre, safe.
  intros.
  reflexivity.
Qed.

Definition needExec {state: Type} (P: state -> Prop) (s: @denosem state) (X: state -> Prop) :=
  exists σₕ, P σₕ /\ safe σₕ s X.


(**********************************************************************************)
(*    safe exec  rules                                                            *)
(**********************************************************************************)
Section  safe_rules.
  Context {Σ : Type}.
  Context `{mc: @JoinM Σ}.
  Context `{jma: @JoinMAxioms Σ mc}.
  
  Local Ltac my_destruct Σ H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | Σ => let σ := fresh "σₕ" in destruct H as [σ H];my_destruct Σ H
              | @denosem Σ => let s := fresh "s" in destruct H as [s H];my_destruct Σ H
              | _ => destruct H as [? H];my_destruct Σ H
              end
  | (@exp _ ?t ?P) _ => match t with 
              | Σ => let σ := fresh "σₕ" in destruct H as [σ H];my_destruct Σ H
              | @denosem Σ => let s := fresh "s" in destruct H as [s H];my_destruct Σ H
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

  Ltac destructs  H:= my_destruct Σ H. 
  

  Lemma needExec_pure : forall B (P: @asrt Σ) s X,
    needExec ( !! B && P) s X <-> B /\ needExec P s X.
  Proof.
    unfold needExec,safe, basicasrt.andp, basicasrt.coq_prop.
    intros. split;intros.
    - destructs H.
      split;auto.
      eexists.
      split;eauto.
    - destructs H.
      eexists.
      splits;eauto.
  Qed.

End  safe_rules. 
End  SepPracticalDenoExecLib.


Module SepEncPracticalDeno.
Import practicaldeno.
Export SepPracticalDenoExecLib.
Section  encoding.
  Context {Σₗ Σₕ : Type}.
  Context `{mc: @JoinM Σₕ}.
  Context `{jma: @JoinMAxioms Σₕ mc}.
  Context {deno : Type}.
  Context {valid_t: @HT_validity Σₗ deno}.

  Definition assertion_encoding (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (X: Σₕ -> Prop) (PF: Σₕ -> Prop): 
    @asrt Σₗ :=
  fun σₗ => exists (σₕ: Σₕ) (cₕ: (@denosem Σₕ)),  
            exists σmₕ σfₕ, join σmₕ σfₕ σₕ /\
            P (σₗ, σmₕ, cₕ) /\ PF σfₕ /\ (weakestpre cₕ X) σₕ.

  Definition encode_asrt  (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (X: Σₕ -> Prop) (PF: Σₕ -> Prop): @asrt Σₗ :=
  fun σₗ => exists (σₕ: Σₕ) (cₕ: (@denosem Σₕ)),  
            exists σmₕ σfₕ, join σmₕ σfₕ σₕ /\
           safe σₕ cₕ X /\  P (σₗ, σmₕ, cₕ) /\ PF σfₕ.

  Lemma  assertion_encoding_equiv_encode_asrt: forall (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (X PF: Σₕ -> Prop), 
    logic_equiv (assertion_encoding P X PF) (encode_asrt P X PF).
  Proof.
    intros.
    unfold logic_equiv, assertion_encoding, encode_asrt.
    intros.
    split;intros [? [? [? [? [? [? [? ?]]]]]]].
    erewrite safe_equiv_weakestpre in H2. do 3 eexists. splits; eauto.
    erewrite <- safe_equiv_weakestpre in H0. do 3 eexists. splits; eauto.
  Qed.

  Definition valid_relT (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: deno) (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)) := 
  forall X PF, valid_t 
                    (encode_asrt P X PF)
                    cₗ 
                    (encode_asrt Q X PF).
End  encoding.

Definition lift {Σₗ Σₕ : Type} (P: @binasrt Σₗ Σₕ ) (cₕ': (@denosem Σₕ)) : @relasrt Σₗ Σₕ (@denosem Σₕ):=
 fun '(σₗ, σₕ, cₕ) => P (σₗ, σₕ) /\ cₕ = cₕ'.
 Notation " '[|' P '|]' '(' X , MF ')' " := (encode_asrt P X MF)  (at level 20, no associativity). 

Import RelHoarePracticalDeno.
Definition valid_reltriple {Σₗ Σₕ : Type} `{mc: @JoinM Σₕ} := @valid_relT Σₗ Σₕ mc  (@denosem Σₗ)  (@valid_triple Σₗ).
Notation " '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_reltriple P c Q) (at level 71, no associativity).
(*************************************************************************************************************)
(*******************************     soundness proof for valid_reltriple    **********************************)
(*************************************************************************************************************)
Require Import Coq.Logic.Classical_Prop.

Section practical_validity_soundness.
  Context {Σₗ Σₕ : Type}.
  Context `{mc: @JoinM Σₕ}.
  Context `{jma: @JoinMAxioms Σₕ mc}.

  Theorem encoding_correctness : forall (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: (@denosem Σₗ))  (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)),
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_reltriple, valid_relT, valid_triple.
      intros HT X MF st1 HP.
      unfold encode_asrt in *.
      destruct HP as (σₕ & cₕ & σmₕ & σfₕ & Hjoin & [Hherr Hhnrm] & HP & HF).
      specialize (HT _ _ _ HP) as [Herr Hnrm].
      split.
      + unfold not in *. intros. apply Hherr. intuition auto.
      +  
      intros st2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as [ | (σₕ' & cₕ' & [Hheval Hhevalerr] & HQ) ];[contradiction | ].
      subst.
      do 2 eexists. split;eauto.
      unfold safe.
      split;[cbn;auto | ].
      cbn;intros.
      sets_unfold in H. subst.
      eapply Hhnrm;eauto.
    - unfold valid_RelTriples, valid_reltriple,valid_relT, valid_triple.
      intros HT st1 σₕ cₕ HP.
      specialize (HT (fun x => cₕ.(nrm) σₕ x) st1).
      split.
      + intros.
        (* excluded middle used *)
        pose proof classic (cₕ.(err) σₕ) as [ | ];[auto | ].
        assert (([|P|](fun x : Σₕ => nrm cₕ σₕ x)) st1).
        { unfold encode_asrt.
          do 2 eexists. split;eauto.
          unfold safe.
          split;auto. 
        }
        specialize (HT H1) as [? ?].
        contradiction.
      + intros st2 Heval.
        (* excluded middle used *)
        pose proof classic (cₕ.(err) σₕ) as [ | ];[auto | ].
        right.
        assert ( ([|P|](fun x : Σₕ => nrm cₕ σₕ x)) st1).
        { unfold encode_asrt, lift.
          do 2 eexists. split;eauto.
          unfold safe.
          split;auto. 
        }
        specialize (HT H0) as [? ?].
        specialize (H2 _ Heval). 
        unfold encode_asrt in *.
        destruct H2 as [σₕ' [cₕ' [? ?]]];subst.
        do 2 eexists.
        split;eauto.
        unfold sem_eval;cbn;sets_unfold.
        split.
        { intros. 
        unfold safe in H2.
        destruct H2 as [_ ?].
        cbn in H2.
        sets_unfold in H2. 
        auto. }
        intros.
        unfold safe in H2.
        destruct H2 as [? _].
        contradiction.
  Qed. 

  Import PracticalDenoConstructs.
  Theorem validity_conrrectness : forall (P: @binasrt Σₗ Σₕ ) (cₗ: (@denosem Σₗ)) (cₕ: (@denosem Σₕ))  (Q : @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ₑ ⟨ lift P cₕ ⟩ cₗ ⟨ lift Q skip ⟩.
  Proof.
    intros.
    split;intros.
    eapply encoding_correctness.
    eapply quadruple2reltriple;auto.

    eapply quadruple2reltriple.
    eapply encoding_correctness;auto.
  Qed.

Section  refinement_soundness.
  
  Variable R : (Σₗ * Σₕ) -> Prop.


  Record denote_refine (LD : @denosem Σₗ) (HD : @denosem Σₕ): Prop := {
  nrm_refine: forall lst1 lst2 hst1, (LD).(nrm) lst1 lst2 -> 
                                      R (lst1, hst1) -> 
                                      (exists hst2, (HD).(nrm) hst1 hst2 /\ R (lst2, hst2)) \/ 
                                      ((HD).(err) hst1);
  err_refine: forall lst hst, (LD).(err) lst -> R (lst, hst) -> ((HD).(err) hst)
  }.
  
  (*************************************************************************************)
  (*    refinement rule                                                                *)
  (*                                                                                   *)
  (* valid_reltriple (R * cₕ) c (R * (CSkip)) and refinement                            *)
  (*                                                                                   *)
  (*************************************************************************************)

  Lemma lh_refinement : 
    forall (s: @denosem Σₗ) (sₕ :@denosem Σₕ),
    ⊢ₑ ⟨ lift R sₕ ⟩ s  ⟨ lift R skip ⟩ ->
    denote_refine s sₕ.
  Proof.
    unfold valid_reltriple, valid_triple, valid_relT, encode_asrt; intros * HRT.
    constructor.
    - intros σ σ' σₕ HevL HR.
    specialize (HRT (fun x => (nrm sₕ) σₕ x) σ).
    pose proof classic (err sₕ σₕ) as [Herr | Hnerr ].
    + right. auto.
    + left.
      assert  (exists (σₕ0 : Σₕ) cₕ,
      safe σₕ0 cₕ (fun x : Σₕ => nrm sₕ σₕ x) /\ (lift R sₕ) (σ, σₕ0, cₕ)).
      { exists σₕ, sₕ.
        unfold safe, lift.
        split;
        auto. }
      specialize (HRT H) as [? ?].
      specialize (H1 σ' HevL) as  [σₕ' [cₕ' [? [? ?]]]].
      subst cₕ'.
      unfold safe, skip in H1.
      destruct H1. simpl in H3.
      specialize (H3 σₕ').
      simpl in H3.
      sets_unfold in H3.
      specialize (H3 (Logic.eq_refl _ )).
      eexists; split; eauto.
    -  intros σ σₕ Heval HR.
    pose proof classic (err sₕ σₕ) as [Herr | Hnerr ];[ eauto | ].
    specialize (HRT (fun x => (nrm sₕ) σₕ x)  σ ).
    assert  (exists (σₕ0 : Σₕ) cₕ,
    safe σₕ0 cₕ (fun x : Σₕ => nrm sₕ σₕ x) /\ (lift R sₕ) (σ, σₕ0, cₕ)) .
    { exists σₕ, sₕ.
      unfold safe,lift.
      split;
      auto.  }
    specialize (HRT H) as [? _].
    contradiction. 
  Qed.

End  refinement_soundness.
End  practical_validity_soundness.




End  EncPracticalDeno.



