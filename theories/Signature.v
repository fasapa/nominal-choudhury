From elpi Require Import elpi.
From Nominal Require Import Atom.

Elpi Db atom.sort.db lp:{{
%  kind atom type.
%  type atom id -> atom.

  pred atom-sort o:id.

  :name "atom.fail"
  atom-sort _ :- coq.error "NOMINAL-ERROR: No atom-sort defined.".
}}.

(* Define new atomic name *)
Elpi Command declare_name.
Elpi Accumulate Db atom.sort.db.
Elpi Accumulate declare_name lp:{{
  main [str X] :- 
    coq.elpi.accumulate _ "atom.sort.db" (clause _ (before "atom.fail") (atom-sort X)),
    coq.notation.add-abbreviation X 0 {{ Atom.t }} ff _.
%    coq.say "ANA new name".

  main _ :- coq.say "Usage: declare_name [name]".
}}.
Elpi Typecheck.

Elpi declare_name Name.

Elpi Command Nominal.
Elpi Accumulate lp:{{

  pred indt-change-name i:indt-decl, o:indt-decl.
  indt-change-name (inductive A B C D) (inductive AR B C D) :- AR is A ^ "_raw".

  main [indt-decl I] :- coq.say I.
  
  main _ :- coq.error "Not an inductive type.".
}}.
Elpi Typecheck.
Elpi Export Nominal.

Nominal Inductive lam : Set :=
| Var : Name -> lam
| App : lam -> lam -> lam
| Abs : Name -> lam -> lam.
Print lam_ind.

Print lam_rect.

Definition lapps (P : lam → Type) (f0 : ∀ l : lam, P l → ∀ l0 : lam, P l0 → P (App l l0))
  l0 (F1: P l0) l1 (F2: P l1) := f0 l0 F1 l1 F2.

Definition F := λ (P : lam → Type) (f : ∀ t : Name, P (Var t))
  (f0 : ∀ l : lam, P l → ∀ l0 : lam, P l0 → P (App l l0)) 
  (f1 : ∀ (t : Name) (l : lam), P l → P (Abs t l)),
  fix F (l : lam) : P l :=
    match l as l0 return (P l0) with
    | Var t => f t
    | App l0 l1 => lapps P f0 l0 (F l0) l1 (F l1)
    | Abs t l0 => f1 t l0 (F l0)
    end.
Print F.

Elpi Command declare_constructor.
Elpi Db constructor.db lp:{{
  kind arity type.
  kind data type.
  
}}.




Elpi declare_name.
Elpi declare_name Name.
Check Name.



Elpi declare_name.

Inductive Arity :=
| ar_unit: Arity
| ar_name: Name -> Arity
| ar_data: Data -> Arity
| ar_pair: Arity -> Arity -> Arity
| ar_bind: Name -> Arity -> Arity.

Elpi Command declare_constructor.
Elpi Accumulate lp:{{
  main [str Name, str Arity, str, Result]
}}

Open Scope string_scope.

Definition Name: Set := string.
Definition Data: Set := string.

Inductive Arity :=
| ar_unit: Arity
| ar_name: Name -> Arity
| ar_data: Data -> Arity
| ar_pair: Arity -> Arity -> Arity
| ar_bind: Name -> Arity -> Arity.

Declare Scope signature.
Delimit Scope signature with sig.

Notation "⟨ a ⟩ b" := (ar_bind a b)%sig (at level 60).
Notation "a *' b" := (ar_pair a b)%sig (at level 65).

Record Constructor : Set :=
  mK { name: Name; arity: Arity; result: Data}.

Notation "N : a ->c d" := (mK N%string a d%string) (at level 70).

Definition V: Constructor := mK "V" (ar_name "v") "t".
Check ("V" : (ar_name "v") ->c "t").

Record Σ: Set :=
  {ΣA: Name; ΣD: list Data; ΣC: list Constructor}.

Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Pretty.
Import MonadNotation.

Open Scope string_scope.
MetaCoq Run (tmQuoteInductive "nat" >>= tmPrint).

Inductive TΣ : Set :=
| 
