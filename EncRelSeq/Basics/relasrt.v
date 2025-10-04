(**
 * @file relhoarelogic.v
 * @brief Provides relational assertions and their lifting to relational assertions
**)
From EncRelSeq.Basics Require Import basicasrt.

(* A binary assertion relates a pair of local and high states. *)
Definition binasrt {Σₗ Σₕ : Type} : Type := @asrt (Σₗ * Σₕ)%type.
(* A relational assertion relates local/high state pairs and  high-level programs *)
Definition relasrt {Σₗ Σₕ : Type} {stmsₕ: Type} : Type :=  @asrt (Σₗ * Σₕ * stmsₕ)%type.


Section  RAssertion.
  Context {Σₗ Σₕ stmsₕ: Type}.

  (* Lifting a binary assertion to a relational one *)
  Definition lift (P: @binasrt Σₗ Σₕ): @relasrt Σₗ Σₕ stmsₕ:=
    fun '(σₗ, σₕ, cₕ) => P (σₗ, σₕ).
  (* [Alst P] lifts an assertion over the low-level state to a relational assertion. *)
  Definition Alst (P : Σₗ -> Prop ): @relasrt Σₗ Σₕ (stmsₕ):= fun '(σₗ, σₕ, cₕ) => P σₗ.
  (* [Ahst P] lifts an assertion over the high-level state to a relational assertion. *)
  Definition Ahst (P : Σₕ -> Prop ): @relasrt Σₗ Σₕ (stmsₕ):= fun '(σₗ, σₕ, cₕ) =>  P σₕ.
  (* [Aspec c] is a relational assertion that specifies the behavior of a high-level program [c]. *)
  Definition Aspec (cₕ : stmsₕ) : @relasrt Σₗ Σₕ (stmsₕ):= fun '(σₗ, σₕ, c) =>  c = cₕ.

  Local Open Scope asrt_scope.
  Lemma alst_hlst_sat : forall (P: @asrt Σₗ) (P' : @asrt Σₕ)  σₗ σₕ s , 
  (Alst P && Ahst P') (σₗ, σₕ, s) <-> P σₗ /\ P' σₕ.
  Proof.
    unfold Alst, Ahst, andp;split;intros;auto.
  Qed.

  Lemma decomposed_sat : forall (P: @asrt Σₗ) (P' : @asrt Σₕ) s σₗ σₕ s', 
  ( Alst P && Ahst P' && Aspec s) (σₗ, σₕ, s') <-> P σₗ /\ P' σₕ /\ s'= s.
  Proof.
    unfold Aspec, Alst, Ahst, andp;split;intros;tauto.
  Qed.

  Lemma lderi_imply_derives : forall P (P': @asrt Σₗ),
  P |-- P' ->
  Alst  P  |-- Alst P' .
  Proof.
    unfold derivable1,  Alst.
    intros.
    destruct st as ((? & ?) & ?).
    auto.
  Qed.

  Lemma hderi_imply_derives : forall P P',
  P |-- P' ->
  Ahst P  |-- Ahst P' .
  Proof.
    unfold derivable1,  Ahst.
    intros. destruct st as ((? & ?) & ?). auto.
  Qed.
End RAssertion.

Notation " ↑ P " := (lift P) (at level 22, no associativity).
Notation " ⌊ P ⌋ " := (Alst P) (at level 22, no associativity).
Notation " ⌈ P ⌉ " := (Ahst P) (at level 22, no associativity).
(* use [ₕ ]ₕ since [ ] has been used for lists *)
Notation " [ₕ c ]ₕ " := (Aspec c) (at level 22, no associativity).

Ltac rel_destruct Σₗ Σₕ Progₗ Progₕ H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | Σₗ => let σₗ := fresh "σₗ" in destruct H as [σₗ H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              | Σₕ => let σₕ := fresh "σₕ" in destruct H as [σₕ H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              | Progₗ => let c := fresh "cₗ" in destruct H as [c H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              | Progₕ => let c := fresh "cₕ" in destruct H as [c H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              | _ => destruct H as [? H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              end
  | (@exp _ ?t ?P) _ => match t with 
              | Σₗ => let σₗ := fresh "σₗ" in destruct H as [σₗ H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              | Σₕ => let σₕ := fresh "σₕ" in destruct H as [σₕ H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              | Progₗ => let c := fresh "cₗ" in destruct H as [c H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              | Progₕ => let c := fresh "cₕ" in destruct H as [c H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              | _ => destruct H as [? H];rel_destruct Σₗ Σₕ Progₗ Progₕ H
              end 
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              rel_destruct Σₗ Σₕ Progₗ Progₕ H;
              rel_destruct Σₗ Σₕ Progₗ Progₕ H0
  | _ \/ _ => destruct H as [H | H];
              rel_destruct Σₗ Σₕ Progₗ Progₕ H
  | _ => (discriminate || contradiction  || idtac)
  end.

Definition lift_eq {Σ: Type} (P: @asrt Σ) : @binasrt Σ Σ :=
  fun '(σ1, σ2) => σ1 = σ2 /\ P σ2.
(* Composes two binary assertions  *)
Definition comp {Σ₁ Σ₂ Σ₃: Type} (P1: @binasrt Σ₁ Σ₂) (P2: @binasrt Σ₂ Σ₃) : @binasrt Σ₁ Σ₃ :=
  fun '(σ₁, σ₃) =>  exists σ₂, P1 (σ₁, σ₂) /\  P2 (σ₂, σ₃).
(* Left projection of a binary assertion *)
Definition proj1 {Σ₁ Σ₂: Type} (P: @binasrt Σ₁ Σ₂): @asrt Σ₁ := 
  fun σ₁ =>  exists σ₂, P (σ₁, σ₂).
(* Right projection of a binary assertion *)
Definition proj2 {Σ₁ Σ₂: Type} (P: @binasrt Σ₁ Σ₂): @asrt Σ₂ := 
  fun σ₂ =>  exists σ₁, P (σ₁, σ₂).
(* Projects a binary assertion P1 : Σ₁ × Σ₂ with a unary assertion P2 : Σ₂ → Prop
 *        into a unary precondition over Σ₁. *)
Definition comp_proj {Σ₁ Σ₂: Type} (P1: @binasrt Σ₁ Σ₂)  (P2: @asrt Σ₂) : @asrt Σ₁ :=
  proj1 (comp P1 (lift_eq P2)).

Notation " P '⋈' Q" := (comp P Q) (at level 28, left associativity).
Notation " P '⋈_π' Q" := (comp_proj P Q) (at level 28, left associativity).

Local Open Scope asrt_scope.

Lemma comp_proj_equiv {Σ₁ Σ₂: Type} (P1: @binasrt Σ₁ Σ₂) (P2: @asrt Σ₂):
    EX σ₂, !! P2 σ₂ && (fun σ₁ => P1 (σ₁, σ₂)) --||--  P1 ⋈_π P2.
Proof.
  intros. unfold logic_equiv, exp, coq_prop, andp, comp_proj, proj1, comp, lift_eq.
  split;intros [? ?].
  - exists x, x. tauto.
  - destruct H as [? [? [? ?]]]. subst.
    eauto.
Qed. 
