From Nominal Require Import Nominal.

(* Pair *)
  
(* #[global] Instance pair_equiv: Equiv (X * Y) := λ x y, (fst x) ≡@{X} (fst y) /\ (snd x) ≡@{Y} (snd y). *)
#[global] Instance fst_proper `{Equiv X} `{Equiv Y}: Proper ((≡@{(X * Y)}) ==> (≡@{X})) fst. Proof. intros ? ? []; auto. Qed.
#[global] Instance snd_proper `{Equiv X} `{Equiv Y}: Proper ((≡@{(X * Y)}) ==> (≡@{Y})) snd. Proof. intros ? ? []; auto. Qed.
#[global] Instance ProdAct `{PAct X, PAct Y}: PAct (X * Y) := λ (p : perm) '(x, y), (p • x, p • y).

#[global] Instance ProdPerm `{Perm X} `{Perm Y}: Perm (X * Y).
Proof.
  split.
  - apply PermGrp.
  - apply prod_relation_equiv; typeclasses eauto.
  - intros x y ? [] [] []; simpl in *; split; simpl; apply gact_proper; auto.
  - intros []; split; simpl; apply gact_id.
  - intros ? ? []; split; simpl; apply gact_compat.
Qed. 
 
Lemma prod_act_compat `{Perm X, Perm Y} (p : perm) (a : X) (b : Y) : p • (a, b) = (p • a, p • b).
Proof. unfold "•", pact; simpl; auto. Qed.

(* Group Action equivariant *)
(* Lemma perm_action_empty p: p ∙ ε ≡ p.
Proof. unfold action, action_perm, perm_comp_action, "+", perm_operator; simpl; auto. Qed. *)

(* Section LOL.
  Context X `{Perm X}.
  Instance action_equivar `{Perm X} : EquivarF (perm * X) X := λ p, p.1 ∙ p.2.
  Instance g : Equivariant (perm * X) X.
  Proof.
    split.
    - intros [] [] []; simpl in *; unfold equivar, action_equivar; rewrite H1, H2; auto.
    - unfold equivar, action_equivar; intros p []; simpl.
      rewrite action_compat, <-(action_id x), <-1!(perm_inv_empty p), <-(action_compat (-p) (p)),
        (action_compat (l + p) _ _) at 1;
      unfold action, action_perm, perm_conj_action; reflexivity.
  Qed.
End LOL.

f1: A ~> (B ~> C);
~> {
  f: A -> B;
  equivar : ...;
}.

f1 (a: A) => f1.1 a

Coercion f: Set --> Funclass.

Section Test.
  Context `{Perm A, Perm B}.
  (* Context `{EquivarF (A * B) C}. *)
  Context `{Equivariant A X}.
  Let f := uncurry (@equivar _ _ H7).
  Check f.
  Lemma lll: forall p a b, p ∙ (f a b) ≡ f (p ∙ a) (p ∙ b).
  Proof. 
    intros; simpl in *; cbv [f uncurry Datatypes.curry].
  destruct H8. specialize (equivariance p (a,b)). unfold equivar in *.
  rewrite <-pair_action_compat in *.

  unfold action, action_perm, pair_action in *. 
  rewrite <-pair_action_compat.
  unfold action, action_perm, pair_action.
  apply equivariance.
  
  unfold equivar, action, action_perm in *.
  rewrite <-pair_action_compat.
  
  apply equivariance. unfold f; simpl.

End Test. *)


(* (* A -> B *) *)
(* Record SetoidMorphism `{Equiv A, Equiv B}  := { *)
(*   (* equiv_a : Equivalence (≡@{A}); *) *)
(*   (* equiv_b : Equivalence (≡@{B}); *) *)
(*   morphism :> A -> B; *)
(*   m_proper :> Proper ((≡@{A}) ==> (≡@{B})) morphism *)
(* }. *)

(* Arguments SetoidMorphism (_) {_} (_) {_}: assert. *)

(* Section FPerm. *)
(*   Context `{Perm A, Perm B}. *)

(*   #[global] Instance morphism_equiv: Equiv (SetoidMorphism A B) := *)
(*     λ f g, forall x, (morphism f) x ≡@{B} (morphism g) x. *)

(*   #[global] Program Instance f_action: PermAction (SetoidMorphism A B) := *)
(*     λ p f, {| morphism := λ x, p ∙ (f (-p ∙ x)) |}. *)
(*   Next Obligation. *)
(*     repeat intro; f_equiv; destruct f; rewrite H3; reflexivity. *)
(*   Qed. *)

(*   #[global] Instance f_perm: Perm (SetoidMorphism A B). *)
(*   Proof. *)
(*     split. *)
(*     - unfold action, action_perm, f_action, equiv; intros f a; simpl. *)
(*       rewrite action_id; destruct f; simpl. *)
(*       rewrite <-inv_neutral, action_id; reflexivity. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*   Admitted. *)

(* End FPerm. *)
