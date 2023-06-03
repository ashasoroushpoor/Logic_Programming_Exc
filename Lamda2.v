Import Nat.
Require Import List.
Import ListNotations.

Definition atomic_type := nat.


Inductive type : Type :=
(* Defenition 3.4 *)
| Var : atomic_type -> type
| Arr : type -> type -> type (*T2 → T2*)
| Pi : atomic_type -> type -> type. (*ΠV : ∗ . T2)*)

Infix ">>" := Arr (right associativity, at level 9).
Notation "$" := Var (right associativity, at level 10).

Definition atomic_term : Type := nat.

Inductive term : Type :=
(* Defenition 3.4.1 *)
| TVar : atomic_term -> term (*V*)
| App : term -> term -> term (*ΛΛ*)
| Tapp : term -> type -> term (*ΛT2*)
| Abs : atomic_term -> type -> term -> term (*λV : T2 . Λ)*)
| Tabs : atomic_type -> term -> term. (*λV : ∗ . Λ)*)

Infix "!" := (App) (left associativity, at level 11).
Infix "!!" :=  (Tapp) (left associativity, at level 12).
(* Notation "-\ x t m" :=
    (Abs x t m)
    (at level 13, right associativity)
    . *)
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
Fixpoint check_declaration (G : context) (x' : term) (a : type) :
    bool :=
        match x' with
        |TVar x =>
            match G with
            | [] => false
            | d :: G' =>
                match d with
                |Sttd y b => (eqb x y && type_eqb a b) || check_declaration G' x' a
                | Std _ => check_declaration G' x' a
                end
            end
        | _ => false
        end.

Compute check_declaration ([Sttd 3 ($ 2)]) (TVar 3) ($2).

Fixpoint FVl (t : type) : list atomic_type :=
    match t with
    | Var m => [m]
    | Arr a b => (FVl a) ++ (FVl b)
    | Pi n t => remove PeanoNat.Nat.eq_dec n (FVl t)
    end.

Fixpoint type_subst (t : type) (a : atomic_type) (b : type): type :=
    match t with
    | Var m =>
        match eqb a m with
        | true => b
        | false => Var m
        end
    | m >> n => (type_subst m a b) >> (type_subst n a b)
    | Pi n t => 
        match (eqb n a) with
        | true => Pi n t
        | false => Pi n (type_subst t a b)
        end
    end.
Definition foreach {T : Type} (l : list T) (P : T -> bool) :=
fold_left andb (map P l) true = true.

Inductive l2_context : context -> Prop :=
| Emp : l2_context [] 
(*∅ is a λ2-context;
dom(∅) = ( ), the empty list.*)
| l2T : forall (G : context) (a : atomic_type) , (l2_context G) ->
(check_type G a = false) -> l2_context ( (Std a) :: G)
(*If Γ is a λ2-context, α ∈ V and α not∈ dom(Γ), then Γ, α : ∗ is a λ2-context;
dom(Γ, α : ∗) = (dom(Γ), α), i.e. dom(Γ) concatenated with α.*)
| l2t : forall (G : context) (x : atomic_term) (r : type),
l2_context G -> (check_term G x = false) ->
(foreach (FVl r) (check_type G)) -> l2_context ((Sttd x r) :: G).
(*If Γ is a λ2-context, if ρ ∈ T2 such that α ∈ dom(Γ) for all free type variables
α occurring in ρ and if x not∈ dom(Γ), then Γ, x : ρ is a λ2-context;
dom(Γ, x : ρ) = (dom(Γ), x).*)

Inductive l2_legal : context -> statement -> Prop :=
(*(var) Γ |- x : σ if Γ is a λ2-context and x : σ ∈ Γ*)
| lvar : forall (G : context) (x : term) (a : type),
(l2_context G) ->  ((check_declaration G x a) = true) -> (l2_legal G (Stt x a))
(* (form) Γ |- B : ∗ if Γ is a λ2-context, B ∈ T2 and
all free type variables in B are declared in Γ *)
| lform : forall (G: context) (B : type),
l2_context G -> (foreach (FVl B) (check_type G)) -> l2_legal G (St B)
(*(appl) Γ |- M : σ → τ, Γ |- N : σ
Γ |- MN : τ*)
| lappl : forall (G: context) (M N : term) (a t : type),
(l2_legal G (Stt M (a >> t))) -> (l2_legal G (Stt N a)) -> l2_legal G (Stt (M ! N) a)
(* (abst) Γ, x : σ |- M : τ
Γ |- λx : σ . M : σ → τ*)
| labst : forall (G: context) (x: atomic_term) (a t : type) (M : term),
(l2_legal ((Sttd x a) :: G) (Stt M t)) -> (l2_legal G (Stt (Abs x a M) (a >> t)))
(* (abst2) Γ, α :∗ |- M : A
Γ |- λα : ∗. M : Πα : ∗. A*)
| labst2 : forall (G: context) (a: atomic_type) (M : term) (A : type),
(l2_legal ((Std a) :: G) (Stt M A)) -> l2_legal G (Stt (Tabs a M) (Pi a A))
(*(appl2) Γ |- M : (Πα : ∗. A), Γ |- B : ∗
Γ |- MB : A[α := B]*)
| lappl2 : forall (G: context) (a: atomic_type) (M : term) (A B: type),
(l2_legal G (Stt M (Pi a A))) -> l2_legal G (St B) -> l2_legal G (Stt (Tapp M B) (type_subst A a B)) 

.

Theorem nineteen: forall (G: context) (s: statement), l2_legal G s -> l2_context G.
(*problem 19 in the book
Prove: if Γ |- L : σ, then Γ is a λ2-context*)
Proof.
    intros. induction H.
    - apply H.
    - apply H.
    - apply IHl2_legal1.
    - inversion IHl2_legal. apply H3.
    - inversion IHl2_legal. apply H2.
    - apply IHl2_legal2.
    
Qed.
