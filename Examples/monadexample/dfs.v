Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From SetsClass Require Import SetsClass.
From AUXLib Require Import List_lemma VMap ListLib. 
From FP Require Import SetsFixedpoints.
Require Import MonadLib.MonadLib.
Import StateRelMonad.
From AUXLib Require Import GraphLib.


Local Open Scope Z_scope.
Import SetsNotation.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Export MonadNotation.
Local Open Scope monad.

Section dfs_iter.
(** 下面定义DFS算法的程序状态，每个程序状态包含一个_[visitied]_集合与一个栈。*)

Record state (V: Type): Type :=
{
  stack: list V;
  visited: V -> Prop;
}.

Definition unvisited (V: Type) (s: state V): V -> Prop :=
  Sets.complement (visited V s).

Notation "s '.(visited)'" := (visited _ s) (at level 1).
Notation "s '.(unvisited)'" := (unvisited _ s) (at level 1).
Notation "s '.(stack)'" := (stack _ s) (at level 1).

Lemma unvisited_visited {V: Type}:
  forall (s: state V),
    s.(unvisited) == Sets.complement s.(visited).
Proof. intros. reflexivity. Qed.

(** 基于此就可以定义DFS中需要用到的程序状态基本操作。*)

Definition test_unvisited {V} (v: V): program (state V) unit :=
  test (fun s => ~ v ∈ s.(visited)).

Definition test_visited {V} (v: V): program (state V) unit :=
  test (fun s => v ∈ s.(visited)).

Definition test_all_neighbor_visited {V E} (pg: PreGraph V E) (u: V):
  program (state V) unit :=
    test (fun s => forall v, step pg u v -> v ∈ s.(visited)).

Definition test_ex_neighbor_unvisited {V E} (pg: PreGraph V E) (u: V):
  program (state V) unit :=
    test (fun s => exists v, step pg u v /\ ~ v ∈ s.(visited)).

Definition visit {V} (v: V): program (state V) unit :=
  fun s1 _ s2 =>
    s2.(visited) == s1.(visited) ∪ Sets.singleton v /\
    s2.(stack) = s1.(stack).

Definition push_stack {V} (v: V): program (state V) unit :=
  fun s1 _ s2 =>
    s2.(stack) = v :: s1.(stack) /\ s2.(visited) = s1.(visited).

Definition pop_stack {V}: program (state V) V :=
  fun s1 v s2 =>
    s1.(stack) = v :: s2.(stack) /\ s2.(visited) = s1.(visited).

Definition test_empty_stack {V}: program (state V) unit :=
  test (fun s => s.(stack) = nil).

Definition body_DFS {V E} (pg: PreGraph V E) (u: V):
  program (state V) (CntOrBrk V  unit) :=
  choice
    (v <- any V;;
     test_unvisited v;;
     test'(step pg u v);;
     push_stack u;;
     visit v;;
     return (by_continue v))
    (test_all_neighbor_visited pg u;;
      choice
      (v <- pop_stack;;
       return (by_continue v))
      (test_empty_stack;;
       return (by_break tt))).

Definition DFS {V E} (pg: PreGraph V E) (u: V):
  program (state V) unit :=
  visit u ;; repeat_break (body_DFS pg) u. 

Definition body_visit_neighbor {V E} (pg: PreGraph V E) (v: V) : 
  program (state V) (unit) := 
 (w <- any V ;; test'(step pg v w);; test_unvisited w;; 
  push_stack w ).

Definition cond_visit_neighbor {V E} (pg: PreGraph V E) (u: V) : 
  (state V) -> Prop := 
  (fun s => exists v, step pg u v /\ ~ v ∈ s.(visited)).

Definition visit_neighbor {V E} (pg: PreGraph V E) (v: V) : 
  program (state V) (unit) := 
  while (cond_visit_neighbor pg v) (body_visit_neighbor pg v).

Definition body_dfs {V E} (pg: PreGraph V E) : 
  program (state V) (unit) := 
  v <- pop_stack;; 
  choice (test_visited v )
         (test_unvisited v ;; 
          visit v ;; 
          visit_neighbor pg v ).

Definition cond_dfs {V E} (pg: PreGraph V E): 
  (state V) -> Prop:=
  (fun s => s.(stack) <> nil). 

Definition DFS_iter {V E} (pg: PreGraph V E) (u: V):
  program (state V) unit :=
  push_stack u ;; while (cond_dfs pg) (body_dfs pg). 


End dfs_iter.

Notation "s '.(visited)'" := (visited _ s) (at level 1).
Notation "s '.(unvisited)'" := (unvisited _ s) (at level 1).
Notation "s '.(stack)'" := (stack _ s) (at level 1).


Arguments visited {V}.
Arguments stack {V}.
Arguments unvisited {V}.