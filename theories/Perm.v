From stdpp Require Import list.
From Nominal Require Export Atom Group.



Instance pair_equiv `{Equiv X, Equiv Y}: Equiv (X * Y) :=
  λ '(x1,y1) '(x2,y2), (x1 ≡@{X} x2) ∧ (y1 ≡@{Y} y2).
Instance pair_equivalence `{Equivalence X, Equivalence Y}: Equivalence pair_equiv.
Instance pair_act `{Action X, Action Y}: Action (X * Y) :=
  λ p '(x,y), (p • x, p • y).
Instance pair_perm `{Perm X, Perm Y}: Perm (X * Y).
Instance pair_support `{Support X, Support Y}: Support (X * Y) :=
  λ '(x,y), (support x) ∪ (support y) ∅

(* Permutation is just a list of pair of names. *)
Notation perm := (list (name * name)).
Notation "⟨ a , b ⟩" := (@cons (name * name) (a,b) nil).

(* Swap action on pair *)
Definition swap '(a,b) : name → name :=
  λ c, if decide (a = c) then b else if decide (b = c) then a else c.

(* Swap on perm *)
Definition swap_perm (p: perm): name → name := 
  λ a, foldl (λ x y, swap y x) a p.

Section SwapProperties.
  Context (a b c : name) (p : name * name) (r s : perm).

  Lemma swap_left : swap (a,b) a = b.
  Proof. simpl; repeat case_decide; congruence. Qed.

  Lemma swap_right : swap (a,b) b = a.
  Proof. simpl; repeat case_decide; congruence. Qed.

  Lemma swap_neither : a ≠ c → b ≠ c → swap (a, b) c = c.
  Proof. intros; simpl; repeat case_decide; congruence. Qed.

  Lemma swap_id : swap (a,a) c = c.
  Proof. simpl; case_decide; congruence. Qed.

  Lemma swap_involutive : swap p (swap p a) = a.
  Proof. destruct p; simpl; repeat case_decide; congruence. Qed.

  Lemma swap_perm_app : swap_perm (r ++ s) a = swap_perm s (swap_perm r a).
  Proof. unfold swap_perm; rewrite foldl_app; simpl; auto. Qed.
End SwapProperties.

Lemma swap_perm_left_rev (p : perm) : ∀ a, swap_perm (reverse p) (swap_perm p a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p; intros.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <-swap_perm_app, <-app_assoc,
      3?swap_perm_app; simpl; rewrite IHp; apply swap_involutive.
Qed.

Lemma swap_perm_right_rev (p : perm) a: swap_perm p (swap_perm (reverse p) a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <- swap_perm_app, <-app_assoc, 
      3?swap_perm_app; simpl; rewrite swap_involutive...
Qed.

(** *Permutation as list forms a Group *)
#[global] Instance perm_neutral: Neutral perm := @nil (name * name).
#[global] Instance perm_operator: Operator perm := @app (name * name).
#[global] Instance perm_inverse: Inverse perm := @reverse (name * name).
#[global] Instance perm_equiv: Equiv perm :=
  λ p q: perm, ∀ a: name, swap_perm p a = swap_perm q a.
#[global] Instance perm_equivalence: Equivalence (≡@{perm}).
Proof. repeat split; repeat intro; [symmetry | etransitivity]; eauto. Qed.

#[global] Instance PermGrp: Group perm.
Proof with auto.
  split; unfold op, perm_operator, neutral, perm_neutral, inv, perm_inverse,
         equiv, perm_equiv in *; repeat intro...
  - typeclasses eauto.
  - rewrite 2?swap_perm_app; do 2 match goal with H : context[_ = _] |- _ => rewrite H end...
  - transitivity (swap_perm (reverse y) (swap_perm x (swap_perm (reverse x) a)));
    [rewrite H, swap_perm_left_rev | rewrite swap_perm_right_rev]...
  - rewrite app_assoc...
  - rewrite app_nil_r...
  - rewrite swap_perm_app, swap_perm_right_rev...
  - rewrite swap_perm_app, swap_perm_left_rev...
Qed.

Section PermGroupProperties.
  Context (a b c : name).

  Lemma swap_equiv_neutral : ⟨a,a⟩ ≡ ɛ@{perm}.
  Proof. unfold equiv, perm_equiv, swap_perm; intros; simpl; case_decide; auto. Qed.

  Lemma swap_expand :
    c ≠ a -> c ≠ b -> ⟨a,c⟩ ≡@{perm} ⟨a,b⟩ + ⟨b,c⟩ + ⟨a,b⟩.
  Proof.
    intros; unfold equiv, perm_equiv, swap_perm; intros; simpl; 
      repeat case_decide; subst; congruence.
  Qed.
End PermGroupProperties.

(* Permutation action *)
Class PermAct X := prmact :> Action perm X.
#[global] Hint Mode PermAct ! : typeclass_instances.
(* Instance: Params (@pact) 1 := {}. *)

Polymorphic Class Perm (X : Type) `{P : PermAct X, Equiv X} := 
  prmtype :> GAction PermGrp X (Act := @prmact X P).
#[global] Hint Mode Perm ! - - : typeclass_instances.

#[global] Instance gact_perm_proper `{Perm A} : Proper ((≡@{perm}) ⟹ (≡@{A}) ⟹ (≡@{A})) action.
Proof. apply gact_proper. Qed. 

(* Equivariant functions *)
(* Section Equivariant.
  Context `{Perm A, Perm B}.

  Class Equivariant (f : A → B) : Prop := {
    from_perm : Perm A;
    to_perm : Perm B;
    equivar : ∀ (a : A) (p : perm), p • (f a) ≡@{B} f(p • a) 
  }.
End Equivariant. *)

(* Section Example.
  Context `{Perm A}.

  Definition id' (a : A) := a.

  #[global] Instance id_equivariant : Equivariant id'.
  Proof. split.
    - auto.
    - auto.
    - intros; unfold id'; auto.
  Qed. 
  
End Example. *)

#[global] Instance perm_action_proper `{Perm X}: Proper ((≡@{perm}) ⟹ (≡@{X}) ⟹ (≡@{X})) P.
Proof. unfold Perm in *; destruct H0; unfold action, prmact in *; auto. Qed.

(* (* Function Perm *)
Section FunEquiv.
  Context `{Equiv A, Equiv B} `{!Equivalence (≡@{A}), !Equivalence (≡@{B})}.

  #[global] Instance fun_equiv : Equiv (A → B) :=
    λ (f g : A → B), (∀ (a : A), (f a) ≡@{B} (g a)).

  #[global] Instance fun_equivalence : Equivalence fun_equiv.
  Proof. split; repeat intro; [reflexivity | symmetry | etransitivity]; eauto. Qed.      
End FunEquiv.

#[global] Instance fun_action `{Perm A, Perm B} : PermAct (A → B) :=
  λ p (f : A → B), (λ (a : A), p • f(-p • a)). 

#[global] Instance TESTE {A} `{E: Equiv B}: subrelation fun_equiv (pointwise_relation A E).
Proof. repeat intro; unfold fun_equiv, equiv in *; apply H. Qed.

Lemma lala {A} `{Equiv B} (f g : A → B) a: f ≡ g → (f a) ≡@{B} (g a).
Proof. intros; apply TESTE; auto. Qed.  *)

Section ProperPermFun.
  Context (A B : Type) `{Perm A, Perm B}.
  
  Record proper_perm_fun : Type := ProperPermFun {
    f_car :> A → B;
(*     f_to : Perm A;
    f_from : Perm B; *)
    f_proper : Proper ((≡@{A}) ⟹ (≡@{B})) f_car
  }.
End ProperPermFun.

(* #[global] Arguments ProperPermFun {_ _ _ _ _ _} _ {_ _ _}. *)
#[global] Arguments ProperPermFun {_ _ _ _} _ {_}.
Existing Instance f_proper.

Notation "'λp' x .. y , t" :=
  (@ProperPermFun _ _ _ _ (λ x, .. (@ProperPermFun _ _ _ _ (λ y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).

Notation " A ⭌ B " := (proper_perm_fun A B) (at level 99, B at level 200, right associativity).

Section proper_perm_fun.
  Context `{Perm A, Perm B}.
  
  #[global] Instance perm_fun_proper (f : A ⭌ B) : Proper ((≡@{A}) ⟹ (≡@{B})) f.
  Proof. apply f_proper. Qed.

  #[global] Instance perm_fun_proper_equiv : Equiv (A ⭌ B) := 
    λ f g, ∀ (a : A), f a ≡@{B} g a.
  
  #[global] Instance perm_fun_proper_equiv1 : Equiv (A -> B) := 
    λ f g, ∀ (a : A), f a ≡@{B} g a.

  #[global] Instance perm_fun_proper_equivalence : Equivalence perm_fun_proper_equiv.
  Proof. split; repeat intro; [reflexivity | symmetry | etransitivity]; eauto. Qed.

  #[global] Instance perm_fun_proper_equivalence1 : Equivalence perm_fun_proper_equiv1.
  Proof. split; repeat intro; [reflexivity | symmetry | etransitivity]; eauto. Qed.

  #[global] Instance : Proper (perm_fun_proper_equiv ⟹ (≡@{A}) ⟹ (≡@{B})) (f_car A B).
  Proof. repeat intro. rewrite H4; auto. Qed.

  #[global,refine] Instance perm_fun_proper_act : PermAct (A ⭌ B) :=
    λ p (f : A ⭌ B), (λp (a : A), p • f(-p • a)).
  Proof.
    - assumption.
    - assumption.
    - typeclasses eauto.
    - repeat intro; apply gact_proper.
      + reflexivity.
      + apply f_proper; apply gact_proper; auto.  
  Defined. 

  #[global] Instance perm_fun_proper_act1 : PermAct (A -> B) :=
    λ p (f : A -> B), (λ (a : A), p • f(-p • a)).

  #[global] Instance perm_lalala : subrelation perm_fun_proper_equiv1 (pointwise_relation A equiv).
  Admitted.

  #[global] Instance perm_fun_proper_perm : Perm (A ⭌ B).
  Proof. split.
    - apply perm_fun_proper_equivalence.
    - intros ? ? EE f g EF ?; simpl; rewrite EE, EF; auto. 
    - unfold equiv, perm_fun_proper_equiv; intros; simpl; rewrite gact_id, grp_inv_neutral, gact_id;
        reflexivity.
    - unfold equiv, perm_fun_proper_equiv; intros; simpl; rewrite <-perm_op_inv, 2!gact_compat;
        reflexivity.
  Qed.

  #[global] Instance perm_fun_proper_perm : Perm (A -> B).
  Proof. split.
    - apply perm_fun_proper_equivalence1.
    - intros ? ? EE f g EF ?; simpl. rewrite EE, EF; auto. 
    - unfold equiv, perm_fun_proper_equiv; intros; simpl; rewrite gact_id, grp_inv_neutral, gact_id;
        reflexivity.
    - unfold equiv, perm_fun_proper_equiv; intros; simpl; rewrite <-perm_op_inv, 2!gact_compat;
        reflexivity.
  Qed.
End proper_perm_fun.