From compcert.lib Require Import Coqlib.
Require Import AUXLib.List_lemma.

Definition ident := positive.
Definition ident_eq_dec : forall x y : ident, {x = y} + {x <> y} := Pos.eq_dec.
Definition ident_eqb (x y : ident) : bool := Pos.eqb x y.
Definition ident_eqb_refl : forall x, ident_eqb x x = true := Pos.eqb_refl.
Definition ident_eqb_eq : forall x y, ident_eqb x y = true <-> x = y := Pos.eqb_eq.


Fixpoint All_Some_true (l: list (option bool)) : bool :=
  match l with
  | nil => true
  | a :: l' =>
    match a with
    | None => false
    | Some b => b && All_Some_true l'
    end
  end.

Fixpoint Find {A : Type} (eqbA : A -> A -> bool) (l : list A) (a : A) : bool :=
  match l with
    | nil => false
    | b :: l' => if (eqbA a b) then true else Find eqbA l' a
  end.

Fixpoint Find_None {A : Type} (l : list (option A)) : bool :=
  match l with
    | nil => false
    | a :: l' => match a with
                   | None => true
                   | _ => Find_None l'
                 end
  end.

Fixpoint Clear_option {A : Type} (l : list (option A)) : list A :=
  match l with
    | nil => nil
    | a :: l' => match a with
                   | None => Clear_option l'
                   | Some a' => a' :: Clear_option l'
                 end
  end.

Fixpoint Find_A_in_prodAB {A B : Type} (eqbA : A -> A -> bool) (l : list (A * B)) (a : A) :  option B :=
  match l with
    | nil => None
    | (a' , b) :: l' => if (eqbA a' a) then Some b else Find_A_in_prodAB eqbA l' a
  end.

Fixpoint Find_B_in_prodAB {A B : Type} (eqbB : B -> B -> bool) (l : list (A * B)) (b : B) :  option A :=
  match l with
    | nil => None
    | (a , b') :: l' => if (eqbB b b') then Some a else Find_B_in_prodAB eqbB l' b
  end.

Fixpoint remove_once {A : Type} (eqbA : A -> A -> bool) (l : list A) (a : A) : list A :=
   match l with
    | nil => nil
    | b :: l' => if (eqbA a b) then l' else b :: remove_once eqbA l' a
   end.

Fixpoint Remove {A : Type} (eqbA : A -> A -> bool) (l : list A) (a : A) : list A :=
   match l with
    | nil => nil
    | b :: l' => if (eqbA a b) then Remove eqbA l' a else b :: Remove eqbA l' a
  end.

Fixpoint Same_part {A : Type} (eqbA : A -> A -> bool) (l1 l2 : list A) : list A :=
  match l1 with
    | nil => nil
    | a :: l => if (Find eqbA l2 a) then a :: (Same_part eqbA l (remove_once eqbA l2 a))
                                    else Same_part eqbA l l2
  end.

Fixpoint Remove_part{A : Type} (eqbA : A -> A -> bool) (l1 l2 : list A) : list A :=
  match l2 with
    | nil => l1
    | a :: l2' => Remove_part eqbA (remove_once eqbA l1 a) l2'
  end.


Definition Find_part {A : Type} (eqbA : A -> A -> bool) (l1 l2 : list A) : bool :=
  list_eqb eqbA (Same_part eqbA l1 l2) l2.

Definition Find_val_in_Z (l : list (Z * ident)) (a : Z) : ident :=
  match (Find_A_in_prodAB Z.eqb l a) with
    | None => xH
    | Some b => b
  end.

Definition Find_string (l : list (ident * string)) (a : ident) : string :=
  match (Find_A_in_prodAB Pos.eqb l a) with
    | None => "Cannot find the predicate"
    | Some b => b
  end.

Definition look_up (l : list (ident * ident)) (a : ident) : option ident :=
  Find_A_in_prodAB Pos.eqb l a.

Definition look_back (l : list (ident * ident)) (a : ident) : option ident :=
  Find_B_in_prodAB Pos.eqb l a.

Fixpoint Add_ident_map (l : list ident) (a : ident) : list (ident * ident) :=
  match l with
    | nil => nil
    | b :: l' => (b , (b + a)%positive) :: Add_ident_map l' a
  end.

Fixpoint Sub_ident_map (l : list ident) (a : ident) : list (ident * ident) :=
  match l with
    | nil => nil
    | b :: l' => (b , (b - a)%positive) :: Sub_ident_map l' a
  end.

Fixpoint Rev_ident_list (l : list (ident * ident)) : list (ident * ident) :=
  match l with
    | nil => nil
    | (b , c) :: l' => (c , b) :: Rev_ident_list l'
  end.

Fixpoint Add_map_ident (l : list (ident * ident)) (a : ident) : list (ident * ident) :=
  match l with
    | nil => nil
    | (b , c) :: l' => (b , (c + a)%positive) :: Add_map_ident l' a
  end.

Fixpoint build_from_ident_list (l l1 : list (ident * ident)) : list (ident * ident) :=
  match l with
    | nil => nil
    | (b , c) :: l' => match look_up l1 b with
                         | None => build_from_ident_list l' l1
                         | Some d => (c , d) :: build_from_ident_list l' l1
                       end
  end.

Definition Insert {A : Type} (eqbA : A -> A -> bool) (l1 l2 : list A) :=
  concat (map (fun a => if (Find eqbA l1 a) then nil else a :: nil) l2) ++ l1.

Definition Add_list (l l1 : list ident) : list ident := Insert Pos.eqb l l1.

Definition Front (l : list (ident * ident)) : ident :=
  match l with
    | nil => xH
    | (b , a) :: l' => a
  end.

Fixpoint Nondup_concat {A : Type} (eqbA : A -> A -> bool) (l : list (list A)) : list A :=
  match l with
    | nil => nil
    | x :: l' => let A_l := Nondup_concat eqbA l' in
                   concat (map (fun a => if (Find eqbA A_l a) then nil else a :: nil) x) ++ A_l
  end.

Definition Some_concat { A : Type} (l : list (option (list A))) : option (list A) :=
  if (Find_None l) then None else Some (concat (Clear_option l)).

Definition Option_map_concat {A B : Type} (l : list A) (f : A -> option (list B)) : option (list B) :=
  Some_concat (map f l).

Definition Option_move {A : Type} (l : list (option A)) : option (list A) :=
  if (Find_None l) then None else Some (Clear_option l).

Definition Option_map {A B : Type} (l: list A) (f : A -> option B) : option (list B) :=
  Option_move (map f l).
