Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Module Type LanguageSig.
(* primitive_types *)
  Parameter Inline expr : Type .
(* derived types *)
(* primitive judgements *)
  Parameter derivable1 : (expr -> expr -> Prop) .
(* primitive connectives *)
  Parameter impp : (expr -> expr -> expr) .
  Parameter andp : (expr -> expr -> expr) .
  Parameter orp : (expr -> expr -> expr) .
  Parameter exp : (forall A : Type, (A -> expr) -> expr) .
  Parameter allp : (forall A : Type, (A -> expr) -> expr) .
  Parameter sepcon : (expr -> expr -> expr) .
  Parameter wand : (expr -> expr -> expr) .
  Parameter emp : expr .
  Parameter coq_prop : (Prop -> expr) .
  Parameter truep : expr .
  Parameter logic_equiv : (expr -> expr -> Prop) .
End LanguageSig.

Module DerivedNames (Names: LanguageSig).
Include Names.
(* derived connectives *)
Definition iffp := (fun x y : expr => andp (impp x y) (impp y x)) .
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
(* derived judgements *)
End DerivedNames.

Module Type PrimitiveRuleSig (Names: LanguageSig).
Include DerivedNames (Names).
  Axiom shallow_exp_right : (forall (A : Type) (P : expr) (Q : A -> expr) (x : A), derivable1 P (Q x) -> derivable1 P (exp A Q)) .
  Axiom shallow_exp_left : (forall (A : Type) (P : A -> expr) (Q : expr), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp A P) Q) .
  Axiom shallow_allp_right : (forall (A : Type) (P : expr) (Q : A -> expr), (forall x : A, derivable1 P (Q x)) -> derivable1 P (allp A Q)) .
  Axiom shallow_allp_left : (forall (A : Type) (P : A -> expr) (Q : expr) (x : A), derivable1 (P x) Q -> derivable1 (allp A P) Q) . 
  Axiom derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) .
  Axiom derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) .
  Axiom derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) .
  Axiom sepcon_emp_left : (forall x : expr, derivable1 (sepcon x emp) x) .
  Axiom sepcon_emp_right : (forall x : expr, derivable1 x (sepcon x emp)) .
  Axiom derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Axiom derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Axiom derivable1_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) .
  Axiom derivable1_andp_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) .
  Axiom derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) .
  Axiom derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) .
  Axiom derivable1_impp_andp_adjoint : (forall x y z : expr, derivable1 x (impp y z) <-> derivable1 (andp x y) z) .
  Axiom derivable1_refl : (forall x : expr, derivable1 x x) .
  Axiom derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) .
  Axiom coq_prop_right : (forall (P : Prop) (x : expr), P -> derivable1 x (coq_prop P)) .
  Axiom coq_prop_left : (forall (P : Prop) (x : expr), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) .
  Axiom derivable1_coq_prop_impp : (forall P Q : Prop, derivable1 (impp (coq_prop P) (coq_prop Q)) (coq_prop (P -> Q))).
  Axiom logic_equiv_refl : (forall x : expr, logic_equiv x x) .
  Axiom logic_equiv_symm : forall x y : expr, logic_equiv x y -> logic_equiv y x.
  Axiom logic_equiv_trans : forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z.
  Axiom logic_equiv_derivable1 : (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) .
  Axiom derivable1_truep_intros : forall x : expr, derivable1 x truep.
  Axiom derivable1_iffp_intros : forall x y : expr, derivable1 (impp x y) (impp (impp y x) (iffp x y)).
  Axiom derivable1_iffp_elim1 : forall x y : expr, derivable1 (iffp x y) (impp x y).
  Axiom derivable1_iffp_elim2 : forall x y : expr, derivable1 (iffp x y) (impp y x) .
  Axiom sepcon_andp_prop1 : forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon P (andp (coq_prop Q) R)) (andp (coq_prop Q) (sepcon P R)).
  Axiom logic_equiv_andp_congr : forall x1 x2 y1 y2 : expr,
	                           logic_equiv x1 x2 ->
                             logic_equiv y1 y2 ->
                             logic_equiv (andp x1 y1) (andp x2 y2).
  Axiom logic_equiv_andp_comm : forall x y : expr,
                             logic_equiv (andp x y) (andp y x).
  Axiom logic_equiv_andp_assoc : forall x y z : expr,
                             logic_equiv (andp (andp x y) z) (andp x (andp y z)).
  Axiom logic_equiv_orp_congr : forall x1 x2 y1 y2 : expr,
  logic_equiv x1 x2 ->
    logic_equiv y1 y2 ->
    logic_equiv (orp x1 y1) (orp x2 y2).
  Axiom logic_equiv_orp_comm : forall x y : expr, logic_equiv (orp x y) (orp y x).
  Axiom logic_equiv_orp_assoc : forall x y z : expr,
      logic_equiv (orp (orp x y) z) (orp x (orp y z)).
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (Rules: PrimitiveRuleSig Names).
Import Rules.
Parameter Inline tree_pos : Type .
(* derived rules *)
  Axiom expr_deep : Set .
  Axiom impp_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom sepcon_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom emp_deep : expr_deep .
  Axiom varp_deep : (nat -> expr_deep) .
  Axiom var_pos : (expr -> option positive -> tree_pos) .
  Axiom sepcon_pos : (tree_pos -> tree_pos -> tree_pos) .
  Axiom cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) .
  Axiom cancel_different : (tree_pos -> tree_pos -> expr) .
  Axiom cancel_same : (tree_pos -> tree_pos -> Prop) .
  Axiom restore : (tree_pos -> tree_pos -> expr) .
  Axiom ex_and1 : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) .
  Axiom ex_and2 : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) .
  Axiom derivable1_andp_comm : (forall x y : expr,  derivable1 (andp x y) (andp y x)).
  Axiom derivable1_andp_assoc : (forall x y z : expr, derivable1 (andp (andp x y) z) (andp x (andp y z))).  
  (* derived rules as instance *)
End LogicTheoremSig.

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.Join2Sepcon.
Require Import Logic.SeparationLogic.ShallowEmbedded.Model2CoqPropEmp.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.
Require Import Logic.ShallowQuantifierLogic.Syntax.
Require Import Logic.ShallowQuantifierLogic.ProofTheory.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Local Open Scope syntax.
Local Open Scope logic_base.

Module LogicTheorem (Names: LanguageSig) (Rules: PrimitiveRuleSig Names) <: LogicTheoremSig Names Rules.
Include Rules.
(* aux primitive instances *)
  #[export] Instance L : Language := (Build_Language expr) .
  #[export] Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  #[export] Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  #[export] Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  #[export] Instance expL : (ShallowExistsLanguage L) := (Build_ShallowExistsLanguage L exp) .
  #[export] Instance allpL : (ShallowForallLanguage L) := (Build_ShallowForallLanguage L allp) .
  #[export] Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  #[export] Instance empL : (EmpLanguage L) := (Build_EmpLanguage L emp) .
  #[export] Instance wandL : (WandLanguage L) := (Build_WandLanguage L wand) .
  #[export] Instance coq_prop_L : (CoqPropLanguage L) := (Build_CoqPropLanguage L coq_prop) .
  #[export] Instance truepL : (TrueLanguage L) := (Build_TrueLanguage L truep) .
  #[export] Instance GammaD1 : (Derivable1 L) := (Build_Derivable1 L derivable1) .
  #[export] Instance andpD : (AndDeduction L GammaD1) := (Build_AndDeduction L andpL GammaD1 derivable1_andp_intros derivable1_andp_elim1 derivable1_andp_elim2) .
  #[export] Instance adjD : (ImpAndAdjointDeduction L GammaD1) := (Build_ImpAndAdjointDeduction L minL andpL GammaD1 derivable1_impp_andp_adjoint) .
  #[export] Instance orpD : (OrDeduction L GammaD1) := (Build_OrDeduction L orpL GammaD1 derivable1_orp_intros1 derivable1_orp_intros2 derivable1_orp_elim) .
  #[export] Instance expD : (ShallowExistsDeduction L GammaD1) := (Build_ShallowExistsDeduction L expL GammaD1 shallow_exp_right shallow_exp_left) .
  #[export] Instance allpD : (ShallowForallDeduction L GammaD1) := (Build_ShallowForallDeduction L allpL GammaD1 shallow_allp_right shallow_allp_left) .
  #[export] Instance bD : (BasicDeduction L GammaD1) := (Build_BasicDeduction L GammaD1 derivable1_refl derivable1_trans) .
  #[export] Instance sepconD : (SepconDeduction L GammaD1) := (Build_SepconDeduction L sepconL GammaD1 derivable1_sepcon_comm derivable1_sepcon_assoc1 derivable1_sepcon_mono) .
  #[export] Instance empD : (EmpDeduction L GammaD1) := (Build_EmpDeduction L sepconL empL GammaD1 sepcon_emp_left sepcon_emp_right) .
  #[export] Instance wandD : (WandDeduction L GammaD1) := (Build_WandDeduction L sepconL wandL GammaD1 derivable1_wand_sepcon_adjoint) .
  #[export] Instance coq_prop_D : (CoqPropDeduction L GammaD1) := (Build_CoqPropDeduction L truepL coq_prop_L GammaD1 coq_prop_right coq_prop_left) .
  #[export] Instance coq_prop_impD: (CoqPropImpDeduction L GammaD1) := (Build_CoqPropImpDeduction L minL coq_prop_L GammaD1 derivable1_coq_prop_impp) .
  #[export] Instance GammaE : (LogicEquiv L) := (Build_LogicEquiv L logic_equiv) .
  #[export] Instance basicE : (BasicLogicEquiv L GammaE) := (Build_BasicLogicEquiv L GammaE logic_equiv_refl logic_equiv_symm logic_equiv_trans).
  #[export] Instance equivD : (EquivDerivable1 L GammaD1 GammaE) := (Build_EquivDerivable1 L GammaD1 GammaE logic_equiv_derivable1).
  #[export] Instance trueD : (TrueDeduction L GammaD1) := (Build_TrueDeduction L truepL GammaD1 derivable1_truep_intros).
  #[export] Instance iffpL : (IffLanguage L) := (Build_IffLanguage L iffp).
  #[export] Instance iffD : (IffDeduction L GammaD1) := (Build_IffDeduction L minL iffpL GammaD1 derivable1_iffp_intros derivable1_iffp_elim1 derivable1_iffp_elim2).
  #[export] Instance andpE: AndLogicEquiv L GammaE := Build_AndLogicEquiv L andpL GammaE logic_equiv_andp_congr logic_equiv_andp_comm logic_equiv_andp_assoc.
  #[export] Instance orpE : OrLogicEquiv L GammaE := Build_OrLogicEquiv L orpL GammaE logic_equiv_orp_congr logic_equiv_orp_comm logic_equiv_orp_assoc.
(* aux refl instances for derivation *)
(* aux derived instances *)
  #[export] Instance exp_andpD : deduction_exp_and := ExpDeduction2ExsitsAnd .
Definition tree_pos : Type := tree_pos.
(* derived rules *)
  Definition expr_deep : Set := expr_deep .
  Definition impp_deep : (expr_deep -> expr_deep -> expr_deep) := impp_deep .
  Definition sepcon_deep : (expr_deep -> expr_deep -> expr_deep) := sepcon_deep .
  Definition emp_deep : expr_deep := emp_deep .
  Definition varp_deep : (nat -> expr_deep) := varp_deep .
  Definition var_pos : (expr -> option positive -> tree_pos) := var_pos .
  Definition sepcon_pos : (tree_pos -> tree_pos -> tree_pos) := sepcon_pos .
  Definition cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) := cancel_mark .
  Definition cancel_different : (tree_pos -> tree_pos -> expr) := cancel_different .
  Definition cancel_same : (tree_pos -> tree_pos -> Prop) := cancel_same .
  Definition restore : (tree_pos -> tree_pos -> expr) := restore .
  Definition ex_and1 : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) := ex_and1 .
  Definition ex_and2 : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) := ex_and2 .
  Definition derivable1_andp_comm : (forall x y : expr,  derivable1 (andp x y) (andp y x)) := derivable1_andp_comm.
  Definition derivable1_andp_assoc : (forall x y z : expr, derivable1 (andp (andp x y) z) (andp x (andp y z))) := derivable1_andp_assoc.
  Definition coq_prop_andp_left : forall (P : Prop) (Q R : expr), (P -> derivable1 Q R) -> derivable1 (andp (coq_prop P) Q) R := coq_prop_andp_left.
  Definition andp_coq_prop_left : forall (P : Prop) (Q R : expr), (P -> derivable1 Q R) -> derivable1 (andp Q (coq_prop P)) R := andp_coq_prop_left.
  Definition coq_prop_truep_equiv : forall P : Prop, P -> logic_equiv (coq_prop P) truep := coq_prop_truep_equiv.
  Definition coq_prop_andp_equiv : forall (P : Prop) (Q : expr), P -> logic_equiv (andp (coq_prop P) Q) Q := coq_prop_andp_equiv.
  Definition andp_coq_prop_equiv : forall (P : Prop) (Q : expr), P -> logic_equiv (andp Q (coq_prop P)) Q := andp_coq_prop_equiv.
  Definition coq_prop_and_equiv : forall P Q : Prop, logic_equiv (coq_prop (P /\ Q)) (andp (coq_prop P) (coq_prop Q)) := coq_prop_and_equiv.
  Definition coq_prop_impl_equiv : forall P Q : Prop, logic_equiv (coq_prop (P -> Q)) (impp (coq_prop P) (coq_prop Q)) := coq_prop_impl_equiv.
  Definition sepcon_andp_prop2_ : forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon P (andp (coq_prop Q) R)) := sepcon_andp_prop2_.
  Definition sepcon_comm_logic_equiv : (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) := sepcon_comm_logic_equiv .
  Definition sepcon_assoc_logic_equiv : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := sepcon_assoc_logic_equiv.
  Definition derivable1_wand_sepcon_modus_ponens1: forall (x y: expr), derivable1 (sepcon (wand x y) x) y := derivable1_wand_sepcon_modus_ponens1.
  Definition derivable1_wand_sepcon_modus_ponens2: forall (x y: expr), derivable1 (sepcon x (wand x y)) y := derivable1_wand_sepcon_modus_ponens2.
  Definition derivable1_wand_mono: forall (x1 x2 y1 y2: expr), derivable1 x2 x1 -> derivable1 y1 y2 -> derivable1 (wand x1 y1) (wand x2 y2) := derivable1_wand_mono.
  Definition wand_andp_logic_equiv: forall (x y z: expr), logic_equiv (wand x (andp y z)) (andp (wand x y) (wand x z)) := wand_andp_logic_equiv.

  #[export] Instance SAP : sepcon_andp_prop := (@Build_sepcon_andp_prop L sepconL GammaD1 coq_prop_L andpL sepcon_andp_prop1 sepcon_andp_prop2_).
  #[export] Instance dSAP_e : sepcon_andp_prop_ext := Derived_sepcon_andp_prop_ext.
  (* derived rules as instance *)
  #[export] Instance _Derivable_impp_rewrite :  RewriteRelation derivable1 := Derivable_impp_rewrite. 
  #[export] Instance _derivable1_refl_instance: Reflexive derivable1 := derivable1_refl_instance.
  #[export] Instance _derivable1_trans_instance : Transitive derivable1 := derivable1_trans_instance.
  #[export] Instance _logic_equiv_impp_rewrite : RewriteRelation logic_equiv := logic_equiv_impp_rewrite.
  #[export] Instance _logic_equiv_refl_instance: Reflexive logic_equiv := logic_equiv_refl_instance.
  #[export] Instance _logic_equiv_symm_instance: Symmetric logic_equiv := logic_equiv_symm_instance.
  #[export] Instance _logic_equiv_trans_instance: Transitive logic_equiv := logic_equiv_trans_instance.
  #[export] Instance _logic_equiv_trans_equiv: Equivalence logic_equiv := logic_equiv_trans_equiv.
  #[export] Instance _derivable1_proper_derivable1 : Proper ( derivable1 --> derivable1 ==> Basics.impl) derivable1 := derivable1_proper_derivable1. 
  #[export] Instance _logic_equiv_proper_logic_equiv : Proper (logic_equiv ==> logic_equiv ==> Basics.impl) logic_equiv := logic_equiv_proper_logic_equiv.
  #[export] Instance _logic_equiv_proper_derivable1 : Proper (logic_equiv ==> logic_equiv ==> Basics.impl) derivable1 := logic_equiv_proper_derivable1.
  #[export] Instance _andp_proper_derivable1 : Proper (derivable1 ==> derivable1 ==> derivable1) andp := andp_proper_derivable1 . 
  #[export] Instance _andp_proper_equiv : Proper (logic_equiv ==> logic_equiv ==> logic_equiv) andp := andp_proper_equiv .
  #[export] Instance _orp_proper_equiv: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) orp := orp_proper_equiv.
  #[export] Instance _orp_proper_derivable1: Proper (derivable1 ==> derivable1 ==> derivable1) orp := orp_proper_derivable1.
  #[export] Instance _sepcon_proper_logic_equiv : Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon := sepcon_proper_logic_equiv.
  #[export] Instance _sepcon_proper_derivable1 : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) := sepcon_proper_derivable1.
  #[export] Instance logic_equiv_derivable1_left: Proper (logic_equiv ==> Logic.eq ==> Basics.flip Basics.impl) derivable1.
  Proof. hnf;intros.
        hnf;intros.
        hnf;intros.
        subst x0.
        apply logic_equiv_derivable1 in H as [? ?].
        eapply derivable1_trans;eauto.  
  Qed.
  #[export] Instance logic_equiv_derivable1_right: Proper (Logic.eq ==> logic_equiv ==> Basics.flip Basics.impl) derivable1.
  Proof. hnf;intros.
        hnf;intros.
        hnf;intros.
        subst x.
        apply logic_equiv_derivable1 in H0 as [? ?].
        eapply derivable1_trans;eauto.  
  Qed.
  
  End LogicTheorem.

(*Require Logic.PropositionalLogic.DeepEmbedded.Solver.
Module IPSolver (Names: LanguageSig).
  Import Names.
  Ltac ip_solve :=
    change expr with Base.expr;
    change provable with Base.provable;
    change impp with Syntax.impp;
    change andp with Syntax.andp;
    intros; Solver.SolverSound.ipSolver.
End IPSolver.*)
