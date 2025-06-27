
From EncRelSeq.Basics Require Import basictacs basicasrt.
Require Import Logic.LogicGenerator.demo932.Interface2.

Module Type sepRuleSig (Names: sepLang).
  Include sepLang.
  Axiom unit_join : (forall n : state, exists u : state, is_unit u /\ join n u n) .
  Axiom unit_spec : (forall n m u : state, is_unit u -> join n u m -> n = m) .
  Axiom join_comm : (forall m1 m2 m : state, join m1 m2 m -> join m2 m1 m) .
  Axiom join_assoc : (forall mx my mz mxy mxyz : state, join mx my mxy -> join mxy mz mxyz -> exists myz : state, join my mz myz /\ join mx myz mxyz) .
End sepRuleSig.
Module sep_rules (L: sepLang) (PL: sepRuleSig L).
  Export PL.

  #[global] Instance  mc : @JoinM state := {|
    basicasrt.join := join;
    basicasrt.is_unit := is_unit
  |}.

  #[global] Instance  mcaxioms : @JoinMAxioms state mc := {|
    basicasrt.unit_join := unit_join;
    basicasrt.unit_spec := unit_spec;
    basicasrt.join_comm := join_comm;
    basicasrt.join_assoc := join_assoc;
  |}.

  Module asrts <: LanguageSig.

  Definition expr :=  expr.
  (* derived types *)
  (* primitive judgements *)
  Definition derivable1 : expr -> expr -> Prop := @derivable1 state.
  (* primitive connectives *)
  Definition impp (e1 e2 : expr) : expr := impp e1 e2.
  Definition andp (e1 e2 : expr) : expr := andp e1 e2.
  Definition orp  (e1 e2 : expr) : expr := orp e1 e2.
  Definition exp {A : Type} (p : A -> expr) : expr := @exp state A p.
  Definition allp {A : Type} (p : A -> expr) : expr := @allp state A p.
  Definition sepcon (P: expr) (Q: expr) : expr :=  sepcon P Q.
  Definition wand (P: expr) (Q: expr) : expr :=  wand P Q.
  Definition emp : expr := emp.
  Definition coq_prop (P: Prop) : expr := coq_prop P.
  Definition truep : expr := truep.
  Definition logic_equiv : (expr -> expr -> Prop) := logic_equiv.
  End asrts.

  Module sepPrimitiveRule <: PrimitiveRuleSig asrts.
  Include DerivedNames asrts.
  Lemma shallow_exp_right : (forall (A : Type) (P : expr) (Q : A -> expr) (x : A), derivable1 P (Q x) -> derivable1 P (exp A Q)).
  Proof. apply shallow_exp_right. Qed.
  Lemma shallow_exp_left : (forall (A : Type) (P : A -> expr) (Q : expr), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp A P) Q) .
  Proof. apply shallow_exp_left. Qed.
  Lemma shallow_allp_right : (forall (A : Type) (P : expr) (Q : A -> expr), (forall x : A, derivable1 P (Q x)) -> derivable1 P (allp A Q)) .
  Proof. apply shallow_allp_right. Qed.
  Lemma shallow_allp_left : (forall (A : Type) (P : A -> expr) (Q : expr) (x : A), derivable1 (P x) Q -> derivable1 (allp A P) Q) . 
  Proof. apply shallow_allp_left. Qed.
  Lemma derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) .
  Proof. apply derivable1_orp_intros1. Qed.
  Lemma derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) .
  Proof. apply derivable1_orp_intros2. Qed.
  Lemma derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) .
  Proof. apply derivable1_orp_elim. Qed.
  Lemma sepcon_emp_left : (forall x : expr, derivable1 (sepcon x emp) x) .
  Proof. apply sepcon_emp_left. Qed. 

  Lemma sepcon_emp_right : (forall x : expr, derivable1 x (sepcon x emp)) .
  Proof. apply sepcon_emp_right. Qed.

  Lemma derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Proof. apply derivable1_sepcon_comm.  Qed.

  Lemma derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Proof. apply derivable1_sepcon_assoc1. Qed.

  Lemma derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Proof. apply derivable1_sepcon_mono. Qed.

  Lemma derivable1_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) .
  Proof. apply derivable1_wand_sepcon_adjoint. Qed.

  Lemma derivable1_andp_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) .
  Proof. apply derivable1_andp_intros. Qed.
  Lemma derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) .
  Proof. apply derivable1_andp_elim1. Qed.

  Lemma derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) .
  Proof. apply derivable1_andp_elim2. Qed.

  Lemma derivable1_impp_andp_adjoint : (forall x y z : expr, derivable1 x (impp y z) <-> derivable1 (andp x y) z) .
  Proof. apply derivable1_impp_andp_adjoint. Qed.

  Lemma derivable1_refl : (forall x : expr, derivable1 x x) .
  Proof. apply derivable1_refl. Qed.

  Lemma derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) .
  Proof. apply derivable1_trans. Qed.
  Lemma coq_prop_right : (forall (P : Prop) (x : expr), P -> derivable1 x (coq_prop P)) .
  Proof. apply coq_prop_right. Qed. 
  Lemma coq_prop_left : (forall (P : Prop) (x : expr), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) .
  Proof. apply coq_prop_left. Qed. 
  Lemma derivable1_coq_prop_impp : (forall P Q : Prop, derivable1 (impp (coq_prop P) (coq_prop Q)) (coq_prop (P -> Q))).
  Proof. apply derivable1_coq_prop_impp. Qed. 
  Lemma logic_equiv_refl : (forall x : expr, logic_equiv x x) .
  Proof. apply logic_equiv_refl. Qed.
  Lemma logic_equiv_symm : forall x y : expr, logic_equiv x y -> logic_equiv y x.
  Proof. apply logic_equiv_symm. Qed.
  Lemma logic_equiv_trans : forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z.
  Proof. apply logic_equiv_trans. Qed.
  Lemma logic_equiv_derivable1 : (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) .
  Proof. apply logic_equiv_derivable1. Qed.
  Lemma derivable1_truep_intros : forall x : expr, derivable1 x truep.
  Proof. apply derivable1_truep_intros. Qed.
  Lemma derivable1_iffp_intros : forall x y : expr, derivable1 (impp x y) (impp (impp y x) (iffp x y)).
  Proof. cbv; intros. split;auto. Qed.
  Lemma derivable1_iffp_elim1 : forall x y : expr, derivable1 (iffp x y) (impp x y).
  Proof. cbv ; intros. destruct H.  auto. Qed.
  Lemma derivable1_iffp_elim2 : forall x y : expr, derivable1 (iffp x y) (impp y x).
  Proof. cbv; intros. destruct H.  auto. Qed.
  Lemma sepcon_andp_prop1 : forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon P (andp (coq_prop Q) R)) (andp (coq_prop Q) (sepcon P R)).
  Proof. apply sepcon_andp_prop1. Qed.
  Lemma derivable1_sepcon_coq_prop_andp_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon P (andp (coq_prop Q) R))) .
  Proof. apply derivable1_sepcon_coq_prop_andp_r. Qed.
  Lemma logic_equiv_andp_congr : forall x1 x2 y1 y2 : expr,
	                           logic_equiv x1 x2 ->
                             logic_equiv y1 y2 ->
                             logic_equiv (andp x1 y1) (andp x2 y2).
  Proof. apply logic_equiv_andp_congr. Qed.
  Lemma logic_equiv_andp_comm : forall x y : expr,
                             logic_equiv (andp x y) (andp y x).
  Proof. apply logic_equiv_andp_comm. Qed.
  Lemma logic_equiv_andp_assoc : forall x y z : expr,
                             logic_equiv (andp (andp x y) z) (andp x (andp y z)).
  Proof. apply logic_equiv_andp_assoc. Qed.
  Lemma logic_equiv_orp_congr : forall x1 x2 y1 y2 : expr,
  logic_equiv x1 x2 ->
    logic_equiv y1 y2 ->
    logic_equiv (orp x1 y1) (orp x2 y2).
  Proof. apply logic_equiv_orp_congr. Qed. 

  Lemma logic_equiv_orp_comm : forall x y : expr, logic_equiv (orp x y) (orp y x).
  Proof. apply logic_equiv_orp_comm. Qed.
  Lemma logic_equiv_orp_assoc : forall x y z : expr,
      logic_equiv (orp (orp x y) z) (orp x (orp y z)).
  Proof. apply logic_equiv_orp_assoc. Qed.
End sepPrimitiveRule.

Module sepRules := LogicTheorem asrts sepPrimitiveRule.

End sep_rules.
