/*@ Extern Coq (program :: * => * => *) */
/*@ Extern Coq (unit :: *) */
/*@ Extern Coq (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop)
               (return : {Sigma} {A} -> A -> program Sigma A) 
               (bind: {Sigma} {A} {B} ->  program Sigma A -> (A -> program Sigma B) -> program Sigma B)
               (applyf: {A} {B} -> (A -> B) -> A -> B)
               (equiv: {T} -> T -> T -> Prop)
               */

/*@ Printing Coq Name program := MonadErr.M */
/*@ Printing Strategy Name program := MonadErr.M */
/*@ Printing Strategy No @ bind */

/*@ Extern Coq (constr_loop_from: {A} -> A -> list A -> Z -> list Z -> Z -> program unit (list Z))*/

/*@ Import Coq Require Import kmp_rel_lib */
/*@ Import Coq Local Open Scope monad */
/*@ Import Coq From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations */
/*@ Import Coq From FP Require Import PartialOrder_Setoid BourbakiWitt */

/*@ include strategies "safeexecE.strategies" */