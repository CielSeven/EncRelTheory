From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import semantics basicasrt safeexec_lib hoarelogic encrel.



Import SetsNotation.
Local Open Scope sets_scope.
Local Open Scope asrt_scope.


Module SepRelHoareNormalDeno.

Export HoareNormalDeno.

Section  seprelational.
  Context {Σ₁ Σ₂: Type}.
  Context `{mc: @JoinM Σ₂}.
  Context `{jma: @JoinMAxioms Σ₂ mc}.

Definition valid_quadruples  (P: @binasrt Σ₁ Σ₂ ) (c₁: denosem) (c₂: denosem) (Q: @binasrt Σ₁ Σ₂) :=
  forall st1 st1', 
    forall stm stf, join stm stf st1' ->
    P (st1, stm) -> 
  forall st2, c₁.(nrm) st1 st2 -> (
    exists st2', c₂.(nrm) st1' st2' /\ 
    exists stm2, join stm2 stf st2' /\ Q (st2, stm2) ).


Definition sem_eval {Σ: Type} (σ₁ : Σ) (c₁: @denosem Σ) (σ₂ : Σ) (c₂: @denosem Σ) : Prop :=
  (forall σ₃, c₂.(nrm) σ₂ σ₃ -> c₁.(nrm) σ₁ σ₃).

Notation " '(-' x , y '-)' '↪' '(-' u , z '-)'" := (sem_eval x y u z).

Definition valid_RelTriples (P: @relasrt Σ₁ Σ₂ (@denosem Σ₂)) (c₁: @denosem Σ₁) (Q: @relasrt Σ₁ Σ₂ (@denosem Σ₂)) :=
  forall st1 st1' (c₂: (@denosem Σ₂)) ,
    forall stm stf, join stm stf st1' ->
    P (st1, stm, c₂) -> 
  forall st2, c₁.(nrm) st1 st2 -> ( 
    exists st2' c₂', (- st1', c₂ -) ↪ (- st2', c₂' -) /\ 
    exists stm2, join stm2 stf st2' /\ Q (st2, stm2, c₂')).
End seprelational.

Notation " '⊢' '{{' P '}}' cₗ '≾' cₕ '{{' Q '}}'" := (valid_quadruples P cₗ cₕ Q) (at level 71, no associativity).
Notation " '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_RelTriples P c Q) (at level 71, no associativity).

Import NormalDenoConstructs.
Section  relcorrect.
  Context {Σ₁ Σ₂: Type}.
  Context `{mc: @JoinM Σ₂}.
  Context `{jma: @JoinMAxioms Σ₂ mc}.
Lemma quadruple2reltriple : forall (P: @binasrt Σ₁ Σ₂ ) (cₗ: (@denosem Σ₁))  (cₕ: @denosem Σ₂ )  (Q :  @binasrt Σ₁ Σ₂),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ ⟨ lift P cₕ ⟩ cₗ ⟨ lift Q skip ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      intros HQnrm lst1 hst1 cₕ' hstm hstf Hjoin [HP ?].
      subst.
      specialize (HQnrm _ _ _ _ Hjoin HP).
      intros lst2 Hleval.
      specialize (HQnrm _ Hleval) as (hst2 & Hheval & [stm2 [Hjoin' HQ]]).
      unfold lift.
      do 2 eexists.
      split;eauto.
      unfold sem_eval.
      intros.
      cbn in H.
      sets_unfold in H. subst.
      auto.
    - unfold valid_RelTriples, valid_quadruples, lift.
      intros HT lst1 hst1 hstm hstf Hjoin HP.
      specialize (HT lst1 hst1 _ hstm hstf Hjoin (ltac:(split;auto))).
      intros lst2 Hleval.
      specialize (HT _ Hleval) as (hst2 & ? & Hheval & stm2 & Hjoin' & HQ & ?).
      subst.
      eexists.
      split;eauto.
      eapply Hheval.
      cbn. sets_unfold. auto.
  Qed.

  Lemma relHoare_frame {A: Type}: 
    forall (P:@asrt Σ₁)  Ps Q Qs F c (cₕ cₕ': @denosem Σ₂ ) (B: A -> Prop),
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
    specialize (H H5). clear H5.
    intros lst2 Heval.
    specialize (H lst2 Heval).
    destruct H as [hst2 [cₕ'' [? [ hst2m [Hjoin2 ? ]]]]].
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

End  relcorrect.

End SepRelHoareNormalDeno.   


Module SepNormalDenoExecLib.
Import normaldeno.
(*************************************************************************************************************)
(******************************* safe termination states set (safe σ c X)   **********************************)
(*************************************************************************************************************)
Definition weakestpre {Σ: Type} (c: @denosem Σ) X : Σ -> Prop :=
    fun σ =>  forall σ', c.(nrm) σ σ' -> σ' ∈ X.


Definition safe {Σ: Type}  (σ : Σ) (c: @denosem Σ) X := 
    forall σ', c.(nrm) σ σ' -> σ' ∈ X.
    
Lemma safe_equiv_weakestpre: forall {Σ: Type} (c: @denosem Σ) X (σ : Σ) ,
   (weakestpre c X) σ <-> safe σ c X.
Proof.
  unfold weakestpre, safe.
  intros.
  reflexivity.
Qed.

Definition needExec {state: Type} `{mc: @JoinM state} 
  (P: state -> Prop) (s: @denosem state)  :=
  fun '(X, MF) =>
    exists σₕ, (P ** MF) σₕ /\ safe σₕ s X.


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
    intros B P s [X PF].
    unfold needExec,safe, basicasrt.andp, basicasrt.coq_prop, basicasrt.sepcon.
    intros. split;intros.
    - destructs H.
      split;auto.
      eexists.
      split;eauto.
    - destructs H.
      eexists.
      splits;eauto.
      eexists.
      splits;eauto.
  Qed.

  Lemma needExec_sepcon : forall (P PF: @asrt Σ) s X MF,
    needExec (P ** PF) s (X, MF) <-> needExec P s (X, (PF ** MF)).
  Proof.
    unfold needExec,safe, basicasrt.andp, basicasrt.coq_prop, basicasrt.sepcon.
    intros. split;intros.
    - destructs H.
      pose proof join_assoc _ _ _ _ _ H1 H.
      destructs H5. clear H H1.
      eexists.
      splits;eauto.
      do 2 eexists.
      splits;eauto.
    - destructs H.
      apply join_comm in H, H2.
      pose proof join_assoc _ _ _ _ _ H2 H.
      destructs H5. clear H2 H.
      exists σₕ.
      split;eauto.
      apply join_comm in H5. apply join_comm in H6.
      eexists.
      splits;eauto.
      eexists.
      splits;eauto.
  Qed.

End  safe_rules. 
End  SepNormalDenoExecLib.


Module SepEncNormalDeno.
Import normaldeno.
Export SepNormalDenoExecLib.
Section  encoding.
  Context {Σₗ Σₕ : Type}.
  Context `{mc: @JoinM Σₕ}.
  Context `{jma: @JoinMAxioms Σₕ mc}.
  Context {deno : Type}.
  Context {valid_t: @HT_validity Σₗ deno}.

  Definition assertion_encoding (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) : 
  ((Σₕ -> Prop) * (Σₕ -> Prop))%type -> @asrt Σₗ :=
  fun '(X,PF) σₗ => exists (σₕ: Σₕ) (cₕ: (@denosem Σₕ)),  
            exists σmₕ σfₕ, join σmₕ σfₕ σₕ /\
            P (σₗ, σmₕ, cₕ) /\ PF σfₕ /\ (weakestpre cₕ X) σₕ.

  Definition encode_asrt  (P: @relasrt Σₗ Σₕ (@denosem Σₕ)): ((Σₕ -> Prop) * (Σₕ -> Prop))%type -> @asrt Σₗ :=
  fun '(X,PF) σₗ => exists (σₕ: Σₕ) (cₕ: (@denosem Σₕ)),  
            exists σmₕ σfₕ, join σmₕ σfₕ σₕ /\
           safe σₕ cₕ X /\  P (σₗ, σmₕ, cₕ) /\ PF σfₕ.

  Lemma  assertion_encoding_equiv_encode_asrt: forall (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) X, 
    logic_equiv (assertion_encoding P X) (encode_asrt P X).
  Proof.
    intros P [X PF].
    unfold logic_equiv, assertion_encoding, encode_asrt.
    intros.
    split;intros [? [? [? [? [? [? [? ?]]]]]]].
    erewrite safe_equiv_weakestpre in H2. do 3 eexists. splits; eauto.
    erewrite <- safe_equiv_weakestpre in H0. do 3 eexists. splits; eauto.
  Qed.

  Definition valid_relT (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: deno) (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)) := 
  forall X, valid_t 
                    (encode_asrt P X)
                    cₗ 
                    (encode_asrt Q X).
End  encoding.

Definition lift {Σₗ Σₕ : Type} (P: @binasrt Σₗ Σₕ ) (cₕ': (@denosem Σₕ)) : @relasrt Σₗ Σₕ (@denosem Σₕ):=
 fun '(σₗ, σₕ, cₕ) => P (σₗ, σₕ) /\ cₕ = cₕ'.
 Notation " '[|' P '|]' '(' X  ')' " := (encode_asrt P X)  (at level 20, no associativity). 
 Notation " '[|' P '|]' '(' X , MF ')' " := (encode_asrt P (X, MF))  (at level 20, no associativity). 

Import SepRelHoareNormalDeno.
Definition valid_reltriple {Σₗ Σₕ : Type} `{mc: @JoinM Σₕ} := @valid_relT Σₗ Σₕ mc  (@denosem Σₗ)  (@valid_triple Σₗ).
Notation " '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_reltriple P c Q) (at level 71, no associativity).
(*************************************************************************************************************)
(*******************************     soundness proof for valid_reltriple    **********************************)
(*************************************************************************************************************)

Section Normal_validity_soundness.
  Context {Σₗ Σₕ : Type}.
  Context `{mc: @JoinM Σₕ}.
  Context `{jma: @JoinMAxioms Σₕ mc}.

  Theorem encoding_correctness : forall (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: (@denosem Σₗ))  (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)),
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_reltriple, valid_relT, valid_triple.
      intros HT [X MF] st1 HP.
      unfold encode_asrt in *.
      destruct HP as (σₕ & cₕ & σmₕ & σfₕ & Hjoin & Hhnrm & HP & HF).
      specialize (HT _ _ _ _ _ Hjoin HP).
      intros st2 Heval.
      specialize (HT _ Heval) as (σₕ' & cₕ' & Hheval  & (σmₕ' & Hjoin' & HQ)).
      do 4 eexists. splits;eauto.
      unfold safe.
      cbn;intros.
      sets_unfold in H. subst.
      eapply Hhnrm;eauto.
    - unfold valid_RelTriples, valid_reltriple,valid_relT, valid_triple.
      intros HT st1 σₕ cₕ σmₕ σfₕ Hjoin HP.
      specialize (HT ((fun x => cₕ.(nrm) σₕ x), [σfₕ]) st1).
      intros st2 Heval.
      assert (([|P|](fun x : Σₕ => nrm cₕ σₕ x, [σfₕ])) st1).
      { unfold encode_asrt.
        do 4 eexists.
        splits;eauto.
        2: sets_unfold; auto.
        unfold safe.
        intros. auto. 
      }
      specialize (HT H). clear H.
      specialize (HT _ Heval). 
      unfold encode_asrt in *.
      destruct HT as [σₕ' [cₕ' [σmₕ' [σfₕ' [? [? [? ?]]]]]]].
      sets_unfold in H2. subst.
      do 2 eexists.
      split;eauto.
  Qed. 

  Import NormalDenoConstructs.
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
 
End  Normal_validity_soundness.


Section  EncodeRules.
  Context {Σₗ Σₕ : Type}.
  Context `{mc: @JoinM Σₕ}.
  Context `{jma: @JoinMAxioms Σₕ mc}.

  Lemma encode_alst_andp: forall X MF (P: @asrt Σₗ) (P' : @asrt Σₕ) s,
  [|Aspec s && Alst P && Ahst P'|](X, MF) --||--  !! (needExec P' s (X, MF)) && P. 
  Proof.
    intros;split.
    { unfold derivable1, andp, coq_prop, encode_asrt, andp, Alst, Ahst, Aspec, needExec, safe, sepcon.
    intros.
    destruct H as (σₕ & cₕ & σmₕ & σfₕ & Hjoin & Hnrm  & ((? & ?) & ?) & ? ).
    simpl in *.
    subst s.
    split;auto.
    eexists;
    split;eauto. }

    unfold derivable1, andp, coq_prop, encode_asrt, andp, Alst, Ahst, Aspec, needExec, safe, sepcon.
    intros.
    destruct H.
    destruct H as (σₕ & (σmₕ & σfₕ & Hjoin & HP & Hnrm)  & ? ).
    simpl in *.
    do 4 eexists.
    split;eauto.
  Qed.


End EncodeRules.
End  SepEncNormalDeno.



