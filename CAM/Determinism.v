Require Import Lang.Syntax.
Require Import Lang.Tactics.
Require Import Lang.ContextProperties.
Require Import CAM.Syntax.
Require Import CAM.Semantics.
Require Import General.Tactics.
Require Import General.Definitions.

Theorem cam_deterministic : 
  forall (V : Set), deterministic (@cam_red V).
Proof.
  intros V s1 s2 s3 Hstep1 Hstep2.
  inv Hstep1; inv Hstep2; auto.
  - Handles_contra.
  - Handles_contra.
  - specialize (HandlesOpWith_deterministic _ _ _ _ HHandlesOp HHandlesOp0) as ?.
    subst. reflexivity.
Qed.

Lemma op_handle_not_handles_red :
  forall (V : Set) (C : i_ctx V) C' h l v s,
    ⟨ i_ctx_handle C h, C', l, v ⟩ₒ ==> s ->
    ~HandlesOp h l ->
    s = ⟨ C, o_ctx_handle C' h, l, v ⟩ₒ.
Proof.
  intros.
  eapply cam_deterministic.
  - apply H.
  - apply cam_red_op_handle1; auto.
Qed.

Lemma op_handle_handles_red :
  forall (V : Set) (C : i_ctx V) C' h l v e_op s,
    ⟨ i_ctx_handle C h, C', l, v ⟩ₒ ==> s ->
    HandlesOpWith h l e_op ->
    s = ⟨esubst (esubst e_op (vshift v))
              (v_lam (e_handle (o_ctx_shift C' [v_var VZ]ₒ) (hshift h))), C⟩ₑ.
Proof.
  intros.
  eapply cam_deterministic.
  - apply H.
  - apply cam_red_op_handle2; auto.
Qed.

Lemma expr_val_red :
  forall (V : Set) (C : i_ctx V) (v : value V) s,
    ⟨ v, C ⟩ₑ ==> s ->
    (exists C' e2, C = i_ctx_let C' e2 /\ s = ⟨esubst e2 v, C'⟩ₑ)
    \/ (exists C' h, C = i_ctx_handle C' h /\ s = ⟨esubst (ret_clause h) v, C'⟩ₑ).
Proof.
  intros. inv H; eauto.
Qed.
