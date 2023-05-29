Import Nat.
Require Import List.
Import ListNotations.

Definition atomic_type := nat.


Inductive type : Type :=
(* Defenition 3.4 *)
| Var : atomic_type -> type
| Arr : type -> type -> type
| Pi : atomic_type -> type -> type.

Infix ">>" := Arr (right associativity, at level 9).
Notation "$" := Var (right associativity, at level 10).

Definition atomic_term : Type := nat.

Inductive term : Type :=
(* Defenition 3.4.1 *)
| TVar : atomic_term -> term
| App : term -> term -> term
| Tapp : term -> type -> term
| Abs : atomic_term -> type -> term -> term
| Tabs : atomic_type -> type -> term.

Infix "!" := (App) (left associativity, at level 11).
Infix "!!" :=  (Tapp) (left associativity, at level 12).
Notation "_\ x t m" :=
    (Abs x t m)
    (at level 13, right associativity)
    .
Notation "*\ t m" :=
    (Tabs t m)
    (at level 14, right associativity)
    .
Inductive statement : Type :=
(* Definition 3.4.4 *)
| St : type -> statement (* s:* *)
| Stt : term -> type -> statement. (*M:s*)

Inductive declaration : Type :=
(* Definition 3.4.4 *)
| Std : atomic_type -> declaration (* s:* *)
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

Fixpoint type_eqb (a : type) (b : type): bool :=
    match a with
    | Var a' => 
        match b with
        | Var b' => eqb a' b'
        | _ => false
        end
    | a' >> a'' =>
        match b with
        | b' >> b'' => (type_eqb a' b') && (type_eqb a'' b'')
        | _ => false
        end
    | Pi a' a'' =>
        match b with 
        | Pi b' b'' => (eqb b' a') && (type_eqb a'' b'')
        | _ => false
        end
    end.

Compute (type_eqb ((Var 2) >> $3) (($2) >> $3)).
Compute (type_eqb ($ 2) (Pi (3) ($3))).
Fixpoint check_declaration (G : context) (x : atomic_term) (a : type) :
    bool :=
        match G with
        | [] => false
        | d :: G' =>
         match d with
         |Sttd y b => (eqb x y && type_eqb a b) || check_declaration G' x a
         | Std _ => check_declaration G' x a
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
| l2T : forall (G : context) (a : atomic_type) , (l2_context G) ->
(check_type G a = false) -> l2_context ( (Std a) :: G)
| l2t : forall (G : context) (x : atomic_term) (r : type),
l2_context G -> (check_term G x = false) ->
(foreach (FVl r) (check_type G)) -> l2_context ((Sttd x r) :: G).

(* Inductive l2_legal : context -> term -> type -> Prop :=
| lvar : forall (G : context) (x : term) (a : type),
(l2_context G) -> 
. *)