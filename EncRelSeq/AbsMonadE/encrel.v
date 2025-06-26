From SetsClass Require Import SetsClass.
Require Import MonadLib.MonadLib.
Import StateRelMonadErr.
From EncRelSeq Require Import semantics basicasrt.
From EncRelSeq.AbsMonadE Require Import hoarelogic.

Require Import Coq.Logic.Classical_Prop.

Module EncPracticalDenoAbsMonad.
Import practicaldeno.

Local Open Scope asrt_scope.

Section  encoding.
  Context {Σₗ Σₕ: Type}.
  Context {deno : Type}.
  Context {valid_t: @HT_validity Σₗ deno}.


  Definition encode_asrt {A: Type}  (P: @relasrt Σₗ Σₕ (program Σₕ A)) (X: A -> Σₕ -> Prop): @basicasrt.asrt Σₗ :=
  fun σₗ => exists (σₕ: Σₕ) (cₕ: (program Σₕ A)),  
           safe σₕ cₕ X /\  P (σₗ, σₕ, cₕ).

  Definition valid_relT  {A: Type}  (P: @relasrt Σₗ Σₕ (program Σₕ A)) (cₗ: deno) (Q : @relasrt Σₗ Σₕ (program Σₕ A)) := 
  forall X, valid_t 
                    (encode_asrt P X)
                    cₗ 
                    (encode_asrt Q X).
End  encoding.

Notation " '[|' P '|]' '(' x ')' " := (encode_asrt P x)  (at level 20, no associativity). 

Import RelHoarePracticalDenoAsbMonad.
Definition valid_reltriple {Σₗ Σₕ A: Type}:= @valid_relT Σₗ Σₕ (@denosem Σₗ) (@valid_triple Σₗ) A.
Notation " '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_reltriple P c Q) (at level 71, no associativity).

(*************************************************************************************************************)
(*******************************     soundness proof for valid_reltriple    **********************************)
(*************************************************************************************************************)
Import MonadNotation.
Local Open Scope monad.
Section normal_validity_soundness.
  Context {Σₗ Σₕ: Type}.

  Theorem validity_lemma : forall {A: Type} (P: @relasrt Σₗ Σₕ (program Σₕ A)) (cₗ: denosem)  (Q :  @relasrt Σₗ Σₕ (program Σₕ A)),
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_reltriple, valid_relT, valid_triple.
      intros HT X st1 HP.
      unfold encode_asrt in *.
      destruct HP as (σₕ & cₕ & [Hherr Hhnrm] & HP).
      specialize (HT _ _ _ HP) as [Herr Hnrm].
      split.
      + unfold not. intros.
        apply Hherr. apply Herr. auto.
      + 
      intros st2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as [ | (σₕ' & cₕ' &  Hheval  & HQ)];[ contradiction | ].
      do 2 eexists. split;[ | eauto].
      destruct Hheval as [Hheval1 Hheval2].
      unfold safe.
      split.
      * intros ?. eapply Hherr. eapply Hheval2. eauto.
      * intros.
      eapply Hhnrm;eauto.
    - unfold valid_RelTriples, valid_reltriple,valid_relT, valid_triple.
      intros HT st1 σₕ cₕ HP.
      specialize (HT (fun r x => cₕ.(nrm) σₕ r x) st1).
      split.
      + intros. 
        pose proof classic (cₕ.(err) σₕ) as [ | ];[auto | ].
        assert (([|P|](fun (r : A) (x : Σₕ) => cₕ.(nrm) σₕ r x)) st1).
        { unfold encode_asrt, lift.
          do 2 eexists. split;[ | eauto].
          unfold safe;split;auto.
        }
        specialize (HT H1) as [? _].
        contradiction.
      + intros lst2 Hleval.
        pose proof classic (cₕ.(err) σₕ) as [ | ];[auto | ].
        assert (([|P|](fun (r : A) (x : Σₕ) => cₕ.(nrm) σₕ r x)) st1).
        { unfold encode_asrt, lift.
          do 2 eexists. split;[ | eauto].
          unfold safe;split;auto.
        }
        specialize (HT H0) as [_ HT].
        specialize (HT _ Hleval).
        destruct HT as [σₕ' [cₕ' [? ?]]];subst.
        right.
        do 2 eexists.
        split;eauto.
        destruct H1.
        unfold sem_eval.
        split.
        * intros.
          eapply H3;eauto.
        * intros.
          contradiction. 
  Qed. 

  Theorem validity_conrrectness : forall {A: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: denosem)  (cₕ: program Σₕ A)  (Q : A -> @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ₑ ⟨ lift P cₕ ⟩ cₗ ⟨ EX x, lift (Q x) (return x) ⟩.
  Proof.
    intros.
    split;intros.
    eapply validity_lemma.
    eapply quadruple2reltriple;auto.

    eapply quadruple2reltriple.
    eapply validity_lemma;auto.
  Qed.

End normal_validity_soundness.
End EncPracticalDenoAbsMonad.
