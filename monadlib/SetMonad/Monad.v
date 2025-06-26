Require Import SetsClass.SetsClass.
Import SetsNotation.
Local Open Scope sets.

(** We define Monad as a typeclass in Coq. *)
Class Monad (M: Type -> Type): Type := {
  bind: forall {A B: Type}, M A -> (A -> M B) -> M B;
  ret: forall {A: Type}, A -> M A;
}.

Arguments Monad.bind: simpl never.
Arguments Monad.ret: simpl never.

(** In order to represent looping computations, it is necessary to introduce a new looping operator.
    First, we define the result of the loop body, which terminates either with a "continue" or a "break". *)

Inductive CntOrBrk (A B: Type): Type :=
| by_continue (a: A)
| by_break (b: B).

Arguments by_continue {_} {_} (_).
Arguments by_break {_} {_} (_).

(** Some common notations for monad *)

Module MonadNotation.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation " x : T <- c1 ;; c2" :=(bind c1 (fun x : T => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (bind c1 (fun x => match x with pat => c2 end))
  (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

Notation "e1 ;; e2" := (bind e1 (fun _ => e2))
  (at level 61, right associativity) : monad_scope.

Notation "'return' v" := (ret v) (at level 60, no associativity) : monad_scope.

End MonadNotation.
