From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import semantics basicasrt relasrt.
From EncRelSeq.UBError Require Import errsem hoarelogic relhoarelogic.
Require Import Coq.Relations.Relations.

Import SetsNotation.
Local Open Scope sets.

Definition small_step_nrm {code: Type} {Σ : Type} : Type :=
  (code * Σ) -> (code * Σ) -> Prop.

Definition small_step_err {code: Type} {Σ : Type} : Type :=
  (code * Σ) -> Prop.

Class smallstepM {stmts: Type} {code: Type} {Σ : Type} := {
  snrm : @small_step_nrm code Σ;
  serr : @small_step_err code Σ;
  finished: code;
  focused : stmts -> code;
  finished_notfocused : forall s, focused s <> finished;
  finished_nostep: forall σ, forall s, ~ snrm (finished,σ) s
}.

Definition multi_step {code: Type} {Σ : Type} (sstep: small_step_nrm) : 
  (code * Σ) -> (code * Σ) -> Prop  :=
  clos_refl_trans (code * Σ) sstep.

Import practicaldeno.

Class denoteM {stmts: Type} {Σ : Type} := {
  dsem : stmts -> @denosem Σ; 
}.


Definition stmts_multi_step_nrm_equiv (stmts: Type) (code: Type) (Σ : Type) `{s: @smallstepM stmts code Σ } `{d: @denoteM stmts Σ} : Prop :=
  forall (c: stmts) (σ₁ σ₂: Σ),  multi_step snrm (focused c, σ₁) (finished, σ₂) <->  (@dsem stmts Σ d c).(nrm) σ₁ σ₂.

Definition stmts_multi_step_err_equiv (stmts: Type) (code: Type) (Σ : Type) `{s: @smallstepM stmts code Σ } `{d: @denoteM stmts Σ} : Prop :=
  forall (c: stmts) (σ₁: Σ), ((multi_step snrm) ∘ serr) (focused c, σ₁)  <->  (@dsem stmts Σ d c).(err) σ₁.


Import RelHoarePracticalDeno.  
Section normal_smallstep2deno.
  Context {stmtsₗ stmtsₕ : Type}.
  Context {codeₗ codeₕ : Type}.
  Context {Σₗ Σₕ : Type}.
  Context (ssemMₗ : @smallstepM stmtsₗ codeₗ Σₗ).
  Context (ssemMₕ : @smallstepM stmtsₕ codeₕ Σₕ).
  Context (dsemMₗ : @denoteM stmtsₗ Σₗ).
  Context (dsemMₕ : @denoteM stmtsₕ Σₕ).

  Variable (stmts_multi_step_nrm_equiv1: stmts_multi_step_nrm_equiv stmtsₗ codeₗ Σₗ).
  Variable (stmts_multi_step_nrm_equiv2: stmts_multi_step_nrm_equiv stmtsₕ codeₕ Σₕ).
  Variable (stmts_multi_step_err_equiv1: stmts_multi_step_err_equiv stmtsₗ codeₗ Σₗ).
  Variable (stmts_multi_step_err_equiv2: stmts_multi_step_err_equiv stmtsₕ codeₕ Σₕ).

  CoInductive small_step_sim :  codeₗ -> Σₗ -> codeₕ -> Σₕ -> (@binasrt Σₗ Σₕ) -> Prop :=
    | stepsim : forall (cₗ: codeₗ) (σₗ : Σₗ) (cₕ: codeₕ) (σₕ : Σₕ) (ϕ: (@binasrt Σₗ Σₕ)),
              ( cₗ = finished ->
                ((multi_step snrm) ∘ serr) (cₕ, σₕ) \/ 
                (exists σₕ', 
                  multi_step snrm (cₕ, σₕ ) (finished, σₕ') /\ 
                  ϕ (σₗ, σₕ')))  ->
              ( serr (cₗ, σₗ) -> 
                (exists cₕ' σₕ', 
                multi_step snrm (cₕ, σₕ ) (cₕ', σₕ') /\ 
                serr (cₕ', σₕ'))  )  ->
              ( cₗ <> finished ->
                (exists cₗ' σₗ', snrm (cₗ, σₗ) (cₗ', σₗ')) -> 
                serr (cₕ, σₕ) \/ 
                (forall cₗ' σₗ', snrm (cₗ, σₗ) (cₗ', σₗ') ->
                (exists cₕ' σₕ', 
                  multi_step snrm (cₕ, σₕ ) (cₕ', σₕ') /\ 
                  small_step_sim cₗ' σₗ' cₕ' σₕ' ϕ )) )     
              -> small_step_sim cₗ σₗ cₕ σₕ ϕ.

  Definition small_step_quadruples  (p: (@binasrt Σₗ Σₕ)) (sₗ: stmtsₗ) (sₕ: stmtsₕ) (q: (@binasrt Σₗ Σₕ)) :=
    forall (σₗ : Σₗ) (σₕ : Σₕ), p (σₗ, σₕ) -> small_step_sim (focused sₗ) σₗ (focused sₕ) σₕ q.


  Theorem quadruples_equiv : forall p sₗ sₕ q, 
    small_step_quadruples p sₗ sₕ q <-> valid_quadruples p (dsem sₗ) (dsem sₕ) q.
  Proof.
    intros. unfold small_step_quadruples, valid_quadruples; split.
    - (* smallstep -> denotational *)
      intros.
      split.
      + intros.
        apply stmts_multi_step_err_equiv1 in H1.
        sets_unfold in H1.
        destruct H1 as (b & Hnrm & Herr).
        unfold multi_step in Hnrm.
        specialize (H _ _ H0).
        clear p H0.
        inversion H;subst.
        clear H0. 
        apply clos_rt_rt1n in Hnrm.
        inversion Hnrm.
        * subst. 
          specialize (H1 Herr) as (? & ? & ? & ?).
          eapply  stmts_multi_step_err_equiv2.
          sets_unfold.
          eexists. split;eauto.
        * subst. clear Hnrm.  
          rename H0 into Hstep. rename H3 into Hclos.
          clear H1.  
          destruct y eqn:?.
          specialize (H2 (finished_notfocused _ ) (ltac: (do 2 eexists;exact Hstep))) as [ | ].
          { eapply stmts_multi_step_err_equiv2.
            sets_unfold.
            eexists. split;eauto.
            eapply rt_refl.
          }
          specialize (H0 _ _ Hstep)  as (cₕ' & σₕ' & Hhnrm & Hsim).
          rewrite <- Heqp in *.
          apply clos_rt1n_step in Hstep.
          revert c σ  Heqp cₕ' σₕ'  Hhnrm Hsim.
          induction Hclos.
          ** intros. subst. inversion Hsim;subst.
             specialize (H1 Herr) as (cₕ'' & σₕ'' & Hhnrm0 & Hherr).
             eapply stmts_multi_step_err_equiv2.
             sets_unfold.
             exists ((cₕ'', σₕ'')). split;auto.
             eapply rt_trans;eauto.
          ** intros. subst. 
             inversion Hsim;subst.
             assert (c = finished \/ c <> finished) as [ | ] by tauto.
             { subst. exfalso. eapply finished_nostep in H0;eauto. }
             destruct y.
             specialize (H3 H4 (ltac: (do 2 eexists;exact H0))) as [ | ].
             {  eapply stmts_multi_step_err_equiv2.
             sets_unfold.
             eexists. split;eauto.
             }
             specialize (H3 _ _ H0) as (cₕ'' & σₕ'' & Hhnrm0 & Hherr). clear H4 H1.
             assert (clos_refl_trans_1n (codeₗ * Σₗ) snrm (focused sₗ, st1) (c0, σ0)).
             { apply clos_rt_rt1n. eapply rt_trans.
               eapply clos_rt1n_rt. eauto. 
               eapply rt_step. eauto.  
             }
             specialize (IHHclos Herr H1 _ _ (ltac:(auto))).
             eapply IHHclos. 2: eauto.
             eapply rt_trans;eauto.
      + intros.
        eapply stmts_multi_step_nrm_equiv1 in H1.
        specialize (H _ _ H0).
        inversion H.
        subst.
        clear H H2 H3.
        apply clos_rt_rt1n in H1.
        inversion H1.
        {  eapply finished_notfocused in H2. contradiction. }
        subst. rename H into Hstep. rename H2 into Hclos. clear H1.
        clear p H0.
        destruct y eqn:?.
        specialize (H4 (finished_notfocused _ ) (ltac: (do 2 eexists;exact Hstep))) as [ | ].
        { left. 
          eapply stmts_multi_step_err_equiv2.
          sets_unfold.
          eexists. split;eauto.
          apply rt_refl.  }
        specialize (H _ _ Hstep) as [cₕ' [σₕ' [Hhnrm Hsim]]].
        rewrite <- Heqp in *.
        remember ((finished, st2)) as b.
        apply clos_rt1n_step in Hstep.
        revert c σ Heqp cₕ' σₕ' Hhnrm Hsim st2 Heqb.
        induction Hclos.
        * intros;subst. inversion Heqb. subst.
          inversion Hsim;subst.
          specialize (H (ltac:(auto))) as [? | [? [? ?]]].
          { left.
            apply stmts_multi_step_err_equiv2.
            sets_unfold in H.
            destruct H as [? [? ?]].
            sets_unfold.
            eexists.
            split;[ | eauto].
            eapply rt_trans;eauto. 
          }
          subst.
          right. eexists. split;eauto.
          eapply stmts_multi_step_nrm_equiv2.
          eapply rt_trans;eauto.
        * intros;subst.
          inversion Hsim;subst.
          assert (c = finished \/ c <> finished) as [ | ] by tauto.
          { subst. exfalso. eapply finished_nostep in H;eauto. }
          destruct y.
          specialize (H2 H3  (ltac: (do 2 eexists;exact H))) as [ | ].
          { left. 
            eapply stmts_multi_step_err_equiv2.
            sets_unfold.
            eexists. split;eauto.  }
          specialize (H2 _ _ H) as (cₕ'' & σₕ'' & Hhnrm0 & Hherr). clear H3 H1 H0.
          assert (clos_refl_trans_1n (codeₗ * Σₗ) snrm (focused sₗ, st1) (c0, σ0)).
          { apply clos_rt_rt1n. eapply rt_trans.
            apply clos_rt1n_rt;eauto.
            apply rt_step;eauto. 
          }
          specialize (IHHclos H0 _ _ (ltac:(auto))).
          eapply IHHclos.
          2,3: eauto.
          eapply rt_trans;eauto.
    - intros.
      specialize (H _ _ H0).
      clear p H0.
      destruct H as  [Herrsim Hnrmsim].
      constructor.
      + intros. apply finished_notfocused in H. contradiction.
      + intros.
        assert (err (dsem sₗ) σₗ ).
        { eapply stmts_multi_step_err_equiv1.
          sets_unfold.
          eexists.
          split;eauto.
          apply rt_refl. }
        specialize (Herrsim H0). clear H0.
        eapply stmts_multi_step_err_equiv2 in Herrsim.
        sets_unfold in Herrsim.
        destruct (Herrsim) as [[? ?] [? ?]].
        eauto.
      + intros.
        clear H H0.
        right.
        intros.
        eexists (focused sₕ), σₕ.
        split;[ apply rt_refl | ].
        apply clos_rtn1_step in H.
        revert cₗ' σₗ' H.
        cofix Hcofix.
        intros.
        constructor.
        * intros. subst. 
          eapply clos_rtn1_rt in H.
          eapply stmts_multi_step_nrm_equiv1 in H.
          specialize (Hnrmsim _ H).
          destruct Hnrmsim.
          { apply stmts_multi_step_err_equiv2 in H0.
            left. auto. }
          right.
          destruct H0 as [? [? ?]].
          apply stmts_multi_step_nrm_equiv2 in H0.
          eexists.
          split;eauto.
        * intros.
          assert (err (dsem sₗ) σₗ).
          { eapply stmts_multi_step_err_equiv1.
            sets_unfold.
            apply clos_rtn1_rt in H.
            eexists.
            split;eauto.
          }
          specialize (Herrsim H1). clear H1.
          apply stmts_multi_step_err_equiv2 in Herrsim.
          sets_unfold in Herrsim.
          destruct Herrsim as [[? ?] [? ?]].
          eauto.
        * intros.
          right.
          intros.
          eexists (focused sₕ), σₕ.
          split;[ apply rt_refl | ].
          eapply Hcofix.
          eapply Relation_Operators.rtn1_trans;eauto.
  Qed.

End normal_smallstep2deno.