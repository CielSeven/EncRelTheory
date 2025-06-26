Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope Z.


(** 可以如下定义有向图。*)

Record PreGraph (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

Notation "pg '.(vvalid)'" := (vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).

(** 基于此就能定义“从x点经过一条边可以到达y点”。*)

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y.

(** 进一步，单步可达关系的自反传递闭包就是多步可达关系。*)

Definition reachable {V E: Type} (pg: PreGraph V E) :=
  clos_refl_trans (step pg).

(** 自反传递闭包_[clos_refl_trans]_是SetsClass库提供的定义。*)

Definition out_edges {V E: Type} (pg : PreGraph V E) (x:V) (e: E) : Prop :=
  pg.(evalid) e /\ pg.(src) e = x.