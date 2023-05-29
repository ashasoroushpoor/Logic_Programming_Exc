Import Nat.
Require Import List.
Import ListNotations.

Definition atomic_type := nat.


Inductive type : Type :=
(* Defenition 3.4 *)
| Var : atomic_type -> type
| Arr : type -> type -> type
| Pi : atomic_type -> type -> type.

Definition atomic_term : Type := nat.

Inductive term : Type :=
(* Defenition 3.4.1 *)
| TVar : atomic_term -> term
| App : term -> term -> term
| Tapp : term -> type -> term
| Abs : atomic_term -> type -> term -> term
| Tabs : atomic_type -> type -> term.

Inductive statement : Type :=
(* Definition 3.4.4 *)
| St : type -> statement (*s:**)
| Stt : term -> type -> statement. (*M:s*)

Inductive declaration : Type :=
(* Definition 3.4.4 *)
| Std : atomic_type -> declaration (*s:**)
| Sttd : atomic_term -> type -> declaration. (*M:s*)

Definition context : Type := list declaration.

Check eqb.

Fixpoint check_type (G : context) (t : atomic_type) :
bool :=
    match G with
    | [] => false
    | d :: G' =>
        match d with
        | Sttd _ _ => check_type G' t
        | Std n => eqb n t || check_type G' t
        end
    end.

Fixpoint check_term (G : context) (x : atomic_term) :
bool :=
    match G with
    | [] => false
    | d :: G' =>
     match d with
     |Sttd y _ => eqb x y || check_term G' x
     | Std _ => check_term G' x
     end
    end.

Fixpoint FVl (t : type) : list atomic_type :=
    match t with
    | Var m => [m]
    | Arr a b => (FVl a) ++ (FVl b)
    | Pi n t => remove PeanoNat.Nat.eq_dec n (FVl t)
    end.

Definition foreach {T : Type} (l : list T) (P : T -> bool) :=
fold_left andb (map P l) true = true.

Inductive l2_context : context -> Prop :=
| Emp : l2_context []
| l2T : forall (G : context) (a : atomic_type)