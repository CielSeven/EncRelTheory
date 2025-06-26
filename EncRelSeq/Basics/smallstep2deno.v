From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import semantics basicasrt relasrt hoarelogic relhoarelogic.
Require Import Coq.Relations.Relations.

Import SetsNotation.
Local Open Scope sets.

Definition small_step_nrm {code: Type} {Σ : Type} : Type :=
  (code * Σ) -> (code * Σ) -> Prop.


Class smallstepM {stmts: Type} {code: Type} {Σ : Type} := {
  snrm : @small_step_nrm code Σ;
  finished: code;
  focused : stmts -> code;
  finished_notfocused : forall s, focused s <> finished;
  finished_nostep: forall σ, forall s, ~ snrm (finished,σ) s
}.

Definition multi_step {code: Type} {Σ : Type} (sstep: small_step_nrm) : 
  (code * Σ) -> (code * Σ) -> Prop  :=
  clos_refl_trans (code * Σ) sstep.

Import normaldeno.

Class denoteM {stmts: Type} {Σ : Type} := {
  dsem : stmts -> @denosem Σ; 
}.


Definition stmts_multi_step_nrm_equiv (stmts: Type) (code: Type) (Σ : Type) `{s: @smallstepM stmts code Σ } `{d: @denoteM stmts Σ} : Prop :=
  forall (c: stmts) (σ₁ σ₂: Σ),  multi_step snrm (focused c, σ₁) (finished, σ₂) <->  (@dsem stmts Σ d c).(nrm) σ₁ σ₂.

Section  relational_hoare_triples_based_on_small_steps.
    Context {stmtsₗ stmtsₕ : Type}.
    Context {codeₗ codeₕ : Type}.
    Context {Σₗ Σₕ : Type}.
    Context (ssemMₗ : @smallstepM stmtsₗ codeₗ Σₗ).
    Context (ssemMₕ : @smallstepM stmtsₕ codeₕ Σₕ).

    CoInductive small_step_sim :  codeₗ -> Σₗ -> codeₕ -> Σₕ -> (@binasrt Σₗ Σₕ) -> Prop :=
    | stepsim : forall (cₗ: codeₗ) (σₗ : Σₗ) (cₕ: codeₕ) (σₕ : Σₕ) (ϕ: (@binasrt Σₗ Σₕ)),
              ( cₗ = finished ->
                (exists σₕ', 
                  multi_step snrm (cₕ, σₕ ) (finished, σₕ') /\ 
                  ϕ (σₗ, σₕ')))  ->
              ( cₗ <> finished ->
                (exists cₗ' σₗ', snrm (cₗ, σₗ) (cₗ', σₗ')) -> 
                (forall cₗ' σₗ', snrm (cₗ, σₗ) (cₗ', σₗ') ->
                (exists cₕ' σₕ', 
                  multi_step snrm (cₕ, σₕ ) (cₕ', σₕ') /\ 
                  small_step_sim cₗ' σₗ' cₕ' σₕ' ϕ )) )     
              -> small_step_sim cₗ σₗ cₕ σₕ ϕ.

    Definition small_step_quadruples  (p: (@binasrt Σₗ Σₕ)) (sₗ: stmtsₗ) (sₕ: stmtsₕ) (q: (@binasrt Σₗ Σₕ)) :=
      forall (σₗ : Σₗ) (σₕ : Σₕ), p (σₗ, σₕ) -> small_step_sim (focused sₗ) σₗ (focused sₕ) σₕ q.
    
    CoInductive small_step_reltriple_wp :  codeₗ -> Σₗ -> codeₕ -> Σₕ -> (@relasrt Σₗ Σₕ codeₕ) -> Prop :=
    | T_stepsim : forall (cₗ: codeₗ) (σₗ : Σₗ) (cₕ: codeₕ) (σₕ : Σₕ) (ϕ: (@relasrt Σₗ Σₕ codeₕ)),
              ( cₗ = finished ->
                (exists σₕ' cₕ', 
                  multi_step snrm (cₕ, σₕ ) (cₕ', σₕ') /\ 
                  ϕ (σₗ, σₕ', cₕ')))  ->
              ( cₗ <> finished ->
                (exists cₗ' σₗ', snrm (cₗ, σₗ) (cₗ', σₗ')) -> 
                (forall cₗ' σₗ', snrm (cₗ, σₗ) (cₗ', σₗ') ->
                (exists cₕ' σₕ', 
                  multi_step snrm (cₕ, σₕ ) (cₕ', σₕ') /\ 
                  small_step_reltriple_wp cₗ' σₗ' cₕ' σₕ' ϕ )) )     
              -> small_step_reltriple_wp cₗ σₗ cₕ σₕ ϕ. 

    Definition small_step_reltriples  (p: (@relasrt Σₗ Σₕ codeₕ)) (sₗ: stmtsₗ) (q: (@relasrt Σₗ Σₕ codeₕ)) :=
      forall (σₗ : Σₗ) (σₕ : Σₕ) (cₕ : codeₕ), p (σₗ, σₕ, cₕ) -> 
                          small_step_reltriple_wp (focused sₗ) σₗ (cₕ) σₕ q.


End  relational_hoare_triples_based_on_small_steps.



Import RelHoareNormalDeno.  
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


  Theorem quadruples_equiv : forall (p: (@binasrt Σₗ Σₕ)) (sₗ: stmtsₗ) (sₕ: stmtsₕ) (q: (@binasrt Σₗ Σₕ)), 
    small_step_quadruples ssemMₗ ssemMₕ p sₗ sₕ q <-> valid_quadruples p (dsem sₗ) (dsem sₕ) q.
  Proof.
    intros. unfold small_step_quadruples, valid_quadruples; split.
    - (* smallstep -> denotational *)
      intros.
      eapply stmts_multi_step_nrm_equiv1 in H1.
      specialize (H _ _ H0).
      inversion H.
      subst.
      clear H H2.
      apply clos_rt_rt1n in H1.
      inversion H1.
      {  eapply finished_notfocused in H2. contradiction. }
      subst. rename H into Hstep. rename H2 into Hclos. clear H1.
      clear p H0.
      destruct y eqn:?.
      specialize (H3 (finished_notfocused _ ) (ltac: (do 2 eexists;exact Hstep))).
      specialize (H3 _ _ Hstep) as [cₕ' [σₕ' [Hhnrm Hsim]]].
      rewrite <- Heqp in *.
      remember ((finished, st2)) as b.
      apply clos_rt1n_step in Hstep.
      revert c σ Heqp cₕ' σₕ' Hhnrm Hsim st2 Heqb.
      induction Hclos.
      * intros;subst. inversion Heqb. subst.
        inversion Hsim;subst.
        specialize (H (ltac:(auto))) as [? [? ?]].
        subst.
        eexists. split;eauto.
        eapply stmts_multi_step_nrm_equiv2.
        eapply rt_trans;eauto.
      * intros;subst.
        inversion Hsim;subst.
        assert (c = finished \/ c <> finished) as [ | ] by tauto.
        { subst. exfalso. eapply finished_nostep in H;eauto. }
        destruct y.
        specialize (H1 H2  (ltac: (do 2 eexists;exact H))).
        specialize (H1 _ _ H) as (cₕ'' & σₕ'' & Hhnrm0 & Hherr). 
        assert (clos_refl_trans_1n (codeₗ * Σₗ) snrm (focused sₗ, st1) (c0, σ0)).
        { apply clos_rt_rt1n. eapply rt_trans.
          apply clos_rt1n_rt;eauto.
          apply rt_step;eauto. 
        }
        specialize (IHHclos H1 _ _ (ltac:(auto))).
        eapply IHHclos.
        2,3: eauto.
        eapply rt_trans;eauto.
    - intros.
      specialize (H _ _ H0).
      clear p H0.
      rename  H into Hnrmsim.
      constructor.
      + intros. apply finished_notfocused in H. contradiction.
      + intros.
        clear H H0. rename H1 into H.
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
          destruct Hnrmsim as [? [? ?]].
          apply stmts_multi_step_nrm_equiv2 in H0.
          eexists.
          split;eauto.
        * intros.
          eexists (focused sₕ), σₕ.
          split;[ apply rt_refl | ].
          eapply Hcofix.
          eapply Relation_Operators.rtn1_trans;eauto.
  Qed.

End normal_smallstep2deno.