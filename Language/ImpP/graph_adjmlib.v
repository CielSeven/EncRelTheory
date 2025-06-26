Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Sorted.

From Coq Require Import Relations.
From SetsClass Require Import SetsClass.
From AUXLib Require Import Axioms Feq Idents  List_lemma int_auto VMap ListLib GraphLib.
From compcert.lib Require Import Integers.

From EncRelSeq Require Import  callsem basicasrt contexthoare_imp.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ArrayLib ImpTactics ImpHoareTactics ImpEHoareTactics.


Class Vertex_Order : Type :=
{
  Vorder : Z -> Z ->Prop;
  Vorder_PreOrder: PreOrder Vorder;
  Vorder_antisym: antisymmetric _ Vorder;
}.

Class vlis_prop {vorder: Vertex_Order} (G: PreGraph Z Z) (vlis : list Z) : Prop := {
  Vlis_Rep: forall v, In v vlis <-> G.(vvalid) v;
  Vlis_NoDup: NoDup vlis;
  Elis_Order: StronglySorted Vorder vlis;
}.


Section adjmatrix_def_rules.

Context {vorder: Vertex_Order}.
Context (G: PreGraph Z Z).
Context (vlis : list Z).

Import ImpRules.
Context (pm : Perm.t).
Local Open Scope asrt_scope.
Local Open Scope Z_scope.

Fixpoint graph_storage (p: addr) (adjm : list (list Z)) :=
   match adjm with 
   | nil => emp 
   | adjl :: adjm' => EX pv, vPV p @ vptr ↦ₗ pv $ pm  ** 
                            store_int_array pm pv (Zlength vlis) adjl **
                            graph_storage (p + 1) adjm'
    end.


End  adjmatrix_def_rules.

