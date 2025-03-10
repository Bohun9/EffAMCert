Require Import General.Definitions.
Require Import General.Lemmas.
Require Import General.Tactics.
Require Import Lang.Syntax.
Require Import Lang.Semantics.
Require Import Lang.ContextProperties.
Require Import Lang.Determinism.
Require Import Lang.NormalForm.
Require Import CAM.Syntax.
Require Import CAM.Semantics.
Require Import CAM.Determinism.

Theorem not_nf_and_diverges_cam :
  forall (V : Set) (s n : cam_state V), normal_form cam_red n ->
    ~(s ==>* n /\ diverges cam_red s).
Proof.
  intros. apply not_nf_and_diverges.
  - apply cam_deterministic.  
  - assumption.
Qed.

Definition cam_diverges_rel {V : Set} (s : cam_state V) :=
  (exists C e, s = ⟨e, C⟩ₑ /\ diverges red (C[e]ᵢ))
  \/ (exists C1 C2 l v,
       s = ⟨C1, C2, l, v⟩ₒ
       /\ diverges red (C1[ C2 [e_do l v ]ₒ ]ᵢ)
       /\ ~OctxHandlesOp C2 l).

Hint Unfold cam_diverges_rel : core.

Theorem lang_cam_diverges :
  forall (V : Set) (e : expr V),
    diverges red e -> diverges cam_red ⟨e, i_ctx_top⟩ₑ.
Proof.
  intros V e He.
  apply diverges_coind with (R := cam_diverges_rel).
  - intros s Hs. destruct Hs as [[C [e' [? ?]]] | [C1 [C2 [l [v [? [? ?]]]]]]]; subst.
    + inversion H0. subst. destruct e'.
      * apply plug_val_red in H as [[? [? [? ?]]] | [? [? [? ?]]]]; subst.
        -- eauto 10.
        -- eauto 10.
      * apply plug_add_red in H as [? [? [? [? ?]]]]; subst. eauto 10.
      * apply plug_app_red in H as [? [? ?]]; subst. eauto 10.
      * eauto 10.
      * eauto 12.
      * eauto 10.
    + inversion H0. subst. destruct C1.
      * simpl in H. exfalso.
        specialize (lang_nf_correct _ (C2 [e_do l v ]ₒ)) as Hnf.
        apply Hnf; eauto.
      * eauto 12.
      * destruct (HandlesOp_dec h l) as [[? ?] | ?].
        -- apply (plug_handle_do_red _ _ _ _ _ _ x _) in H; auto; subst.
           eauto 12.
        (* It should be automated. *)
        -- eexists. split.
           ++ eauto.
           ++ right. eexists. eexists. eexists. eexists. split.
              ** auto.
              ** split.
                 --- apply H0.
                 --- simpl. apply not_and_or. auto.
  - eauto 10.
Qed.

Definition lang_diverges_rel {V : Set} (e : expr V) :=
  (exists C e', e = C[e']ᵢ /\ diverges cam_red (⟨e', C⟩ₑ))
  \/ (exists C C' l v,
       e = (C[ C' [e_do l v ]ₒ ]ᵢ)
       /\ diverges cam_red (⟨C, C', l, v⟩ₒ)
       /\ ~OctxHandlesOp C' l).

Hint Unfold lang_diverges_rel : core.

Lemma cam_lang_op_mode_diverges :
  forall (V : Set) (C : i_ctx V) C' l v, diverges cam_red ⟨ C, C', l, v ⟩ₒ ->
    ~OctxHandlesOp C' l -> exists (e' : expr V),
    C [C' [e_do l v ]ₒ ]ᵢ --> e' /\ lang_diverges_rel e'.
Proof.
  intros. generalize dependent C'. induction C;
  intros; inversion H; subst.
  - inv H1.
  - inv H1. apply IHC with (C' := o_ctx_let C' e2); auto.
  - destruct (HandlesOp_dec h l) as [[? ?] | ?].
    + specialize (op_handle_handles_red _ _ _ _ _ _ _ _ H1 H3) as ?. subst.
       eexists. split.
       * simpl. apply red_context. apply red_handle_do; eauto.
       * eauto 10.
    + specialize (op_handle_not_handles_red _ _ _ _ _ _ _ H1 H3) as ?. subst.
       apply IHC with (C' := o_ctx_handle C' h); simpl; auto.
Qed.

Theorem cam_lang_diverges :
  forall (V : Set) (e : expr V),
  diverges cam_red ⟨e, i_ctx_top⟩ₑ -> diverges red e.
Proof.
  intros.
  apply diverges_coind with (R := lang_diverges_rel).
  - clear e H. intros.
    destruct H as [[C [e [? ?]]] | [C [C' [l [v [He [Hdiv HCe]]]]]]]; subst.
    + generalize dependent C. induction e; intros.
      * inv H0. apply expr_val_red in H as [[C' [e2 [? ?]]] | [C' [h [? ?]]]]; subst.
        -- eexists. split.
           ++ simpl. apply red_context. apply red_let.
           ++ eauto 10.
        -- eexists. split.
           ++ simpl. apply red_context. apply red_handle_ret.
           ++ eauto 10.
      * inv H0. inv H. eexists. split.
        -- apply red_context. apply red_add.
        -- eauto 10.
      * inv H0. inv H. eexists. split.
        -- apply red_context. apply red_app.
        -- eauto 10.
      * inv H0. inv H. apply IHe1 with (C := i_ctx_let C e2); auto.
      * inv H0. inv H. change (e_do l v) with (o_ctx_hole [ e_do l v ]ₒ).
        apply cam_lang_op_mode_diverges; auto.
      * inv H0. inv H. apply IHe with (C := i_ctx_handle C h); auto.
    + apply cam_lang_op_mode_diverges; auto.
  - left. exists i_ctx_top. exists e. eauto.
Qed.

Theorem lang_iff_cam_diverges :
  forall (V : Set) (e : expr V),
    diverges red e <-> diverges cam_red ⟨e, i_ctx_top⟩ₑ.
Proof.
  intros. split.
  - apply lang_cam_diverges.
  - apply cam_lang_diverges.
Qed.
