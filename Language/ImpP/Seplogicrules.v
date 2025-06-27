Require Import Logic.LogicGenerator.demo932.Interface.
From EncRelSeq.Basics Require Import basictacs basicasrt.
Require Import Coq.Lists.List.


Module Type SepSig (Names: LanguageSig) .
Import Names.

  #[global] Instance  mc : @JoinM model := {|
    basicasrt.join := join;
    basicasrt.is_unit := is_unit
  |}.
(* derived connectives *)
  Definition sepcon (x y : model -> Prop) := sepcon x y.
  Definition wand (x y : model -> Prop) := wand x y.
  Definition orp  (e1 e2 : (model -> Prop)) : (model -> Prop) := orp e1 e2.
  Definition andp (x y : model -> Prop):=  andp x y.
  Definition impp (x y : model -> Prop) := impp x y.
  Definition exp (A : Type) (x : A -> model -> Prop) := @exp model A x.
  Definition allp (A : Type) (x : A -> model -> Prop) := @allp model A x.
  Definition emp := emp .
  Definition coq_prop (P : Prop) := @coq_prop model P.
  Definition truep := @truep model.
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
  Definition iter_sepcon := (fun xs : list expr => fold_left sepcon xs emp) .
  Definition iffp := (fun x y : expr => andp (impp x y) (impp y x)) .
(* derived judgements *)
  Definition derivable1 (x y : model -> Prop):= derivable1 x y.
  Definition provable := (fun x : expr => derivable1 (impp x x) x) .
  Definition logic_equiv (x y :(model -> Prop) ):= logic_equiv x y.
End SepSig.

Module Convert (M : A) : B.
  Definition y := M.x + 1.
End Convert.


Module Type PrimitiveRuleSig (Names: LanguageSig) (DerivedNames: SepSig Names).
Import Names DerivedNames.
  Axiom unit_join : (forall n : model, exists u : model, is_unit u /\ join n u n) .
  Axiom unit_spec : (forall n m u : model, is_unit u -> join n u m -> n = m) .
  Axiom join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) .
  Axiom join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz) .
End PrimitiveRuleSig.



Module sep_rules (L: LanguageSig) ().
  Export PL.


  #[global] Instance  mcaxioms : @JoinMAxioms model mc := {|
    basicasrt.unit_join := unit_join;
    basicasrt.unit_spec := unit_spec;
    basicasrt.join_comm := join_comm;
    basicasrt.join_assoc := join_assoc;
  |}.

  Module asrts <: DerivedNamesSig L.

  (* derived types *)
  (* primitive judgements *)
  Definition derivable1 : (model -> Prop) -> (model -> Prop) -> Prop := @derivable1 model.
  (* primitive connectives *)
  Definition impp (e1 e2 : model -> Prop) : (model -> Prop) := impp e1 e2.
  Definition andp (e1 e2 : (model -> Prop)) : (model -> Prop) := andp e1 e2.
  Definition orp  (e1 e2 : (model -> Prop)) : (model -> Prop) := orp e1 e2.
  Definition exp {A : Type} (p : A -> (model -> Prop)) : (model -> Prop) := @exp model A p.
  Definition allp {A : Type} (p : A -> (model -> Prop)) : (model -> Prop) := @allp model A p.
  Definition sepcon (P: (model -> Prop)) (Q: (model -> Prop)) : (model -> Prop) :=  sepcon P Q.
  Definition wand (P: (model -> Prop)) (Q: (model -> Prop)) : (model -> Prop) :=  wand P Q.
  Definition emp : (model -> Prop) := emp.
  Definition coq_prop (P: Prop) : (model -> Prop) := coq_prop P.
  Definition truep : (model -> Prop) := truep.
  Definition logic_equiv : ((model -> Prop) -> (model -> Prop) -> Prop) := logic_equiv.
  End asrts.
  