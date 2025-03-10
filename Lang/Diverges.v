Require Import General.Definitions.
Require Import Lang.Syntax.
Require Import Lang.Semantics.
Require Import Lang.Determinism.

Theorem not_nf_and_diverges_lang :
  forall (V : Set) (e n : expr V), normal_form red n ->
    ~(e -->* n /\ diverges red e).
Proof.
  intros. apply not_nf_and_diverges.
  - apply lang_deterministic.  
  - assumption.
Qed.

Definition ω := (v_lam (e_app (v_var VZ) (v_var VZ))) : value Empty_set.
Definition Ω := e_app ω ω : expr Empty_set.

Lemma omega_diverges :
  diverges red Ω.
Proof.
  apply diverges_coind with (R := (fun e => e = Ω)).
  - intros. subst. exists Ω. intuition.
    assert (H : Ω = esubst (e_app (v_var VZ) (v_var VZ)) ω).
    { unfold esubst. simpl. reflexivity. }
    rewrite H at 2. apply red_app.
  - reflexivity.
Qed.
