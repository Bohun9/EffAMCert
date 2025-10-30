Require Import General.Tactics.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.

Definition normal_form {A : Set} (R : A -> A -> Prop) (a : A) :=
  ~exists a', R a a'.

Definition deterministic {A : Type} (R : A -> A -> Prop) :=
  forall (a1 a2 a3 : A), R a1 a2 -> R a1 a3 -> a2 = a3.

CoInductive diverges {A : Set} (E : A -> A -> Prop) : A -> Prop :=
  | diverges_step : forall a1 a2, E a1 a2 -> diverges E a2 -> diverges E a1.

Section diverges_coind.
  Variable A : Set.
  Variable E : A -> A -> Prop.
  Variable R : A -> Prop.
  Hypothesis Step : forall a, R a -> exists a', E a a' /\ R a'.

  Theorem diverges_coind : forall a, R a -> diverges E a.
  Proof.
    cofix lang_inf_coind.
    intros. apply Step in H as [a' [Hstep Ha']].
    eapply diverges_step.
    - apply Hstep.
    - apply lang_inf_coind. assumption.
  Qed.
End diverges_coind.

Theorem not_nf_and_diverges :
  forall (A : Set) (R : A -> A -> Prop),
    deterministic R ->
    forall (a n : A), normal_form R n ->
    ~(clos_refl_trans_1n _ R a n /\ diverges R a).
Proof.
  intros. intros [multi Hdiv]. induction multi.
  - inv Hdiv. eauto.
  - apply IHmulti; auto. inv Hdiv.
    specialize (H _ _ _ H1 H2) as ?. subst.
    assumption.
Qed.
