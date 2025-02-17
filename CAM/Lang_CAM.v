Require Import CAM.Syntax.
Require Import CAM.Semantics.
Require Import CAM.ShapeLemmas.
Require Import Lang.Semantics.
Require Import Lang.ContextProperties.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.

Theorem cam_lang :
  forall (V : Set) (s : cam_state V) v,
    s ==>* ⟨v, i_ctx_top⟩ₑ ->
    (forall e (C : i_ctx V),
      s = ⟨e, C⟩ₑ -> C[e]ᵢ -->* v)
    /\ (forall (C : i_ctx V) (C' : o_ctx V) l w,
      s = ⟨C, C', l, w⟩ₒ ->
      ~OctxHandlesOp C' l ->
      C[ C'[e_do l w]ₒ ]ᵢ -->* v).
Proof.
  intros. remember ⟨v, i_ctx_top⟩ₑ as s'. induction H as [| s s2 s']; subst.
  - split; intros.
    + injection H; intros; subst. simpl. apply rt1n_refl.
    + discriminate.
  - inversion H; subst; split; intros; try discriminate;
    injection H1; intros; subst; clear H1;
    specialize (IHclos_refl_trans_1n eq_refl);
    destruct IHclos_refl_trans_1n as [IH1 IH2].
    + eapply rt1n_trans.
      * apply red_context. apply red_add.
      * apply IH1. reflexivity.
    + eapply rt1n_trans.
      * apply red_context. apply red_app.
      * apply IH1. reflexivity.
    + assert (H' : C0 [e_let e1 e2]ᵢ = (i_ctx_let C0 e2) [e1]ᵢ).
      { reflexivity. }
      rewrite H'. apply IH1. reflexivity.
    + assert (H' : C0 [e_handle e h]ᵢ = (i_ctx_handle C0 h) [e]ᵢ).
      { reflexivity. }
      rewrite H'. apply IH1. reflexivity.
    + simpl. eapply rt1n_trans.
      * apply red_context. apply red_let.
      * apply IH1. reflexivity.
    + simpl. eapply rt1n_trans.
      * apply red_context. apply red_handle_ret.
      * apply IH1. reflexivity.
    + assert (H' : C0 [e_do l v0 ]ᵢ = C0 [o_ctx_hole [e_do l v0 ]ₒ ]ᵢ).
      { reflexivity. }
      rewrite H'. apply IH2.
      * reflexivity.
      * simpl. auto.
    + assert (H' : i_ctx_let C e2 [C'0 [e_do l0 w ]ₒ ]ᵢ =
                   C [(o_ctx_let C'0 e2) [e_do l0 w ]ₒ ]ᵢ).
      { reflexivity. }
      rewrite H'. apply IH2.
      * reflexivity.
      * simpl. assumption.
    + assert (H' : i_ctx_handle C h [C'0 [e_do l0 w ]ₒ ]ᵢ =
                   C [(o_ctx_handle C'0 h) [e_do l0 w ]ₒ ]ᵢ).
      { reflexivity. }
      rewrite H'. apply IH2.
      * reflexivity.
      * simpl. intro. destruct H1 as [Hcontra | Hcontra]; auto.
    + eapply rt1n_trans.
      * simpl. apply red_context. apply red_handle_do.
        -- apply HHandlesOp.
        -- assumption.
      * apply IH1. reflexivity.
Qed.

Ltac rt1n_trans2 := 
  apply clos_rt_rt1n; eapply rt_trans; apply clos_rt1n_rt.

Theorem lang_cam :
  forall (V : Set) (e : expr V) (v : value V),
    e -->* v -> 
    forall (C : i_ctx V) e',
    e = C[e']ᵢ -> ⟨e', C⟩ₑ ==>* ⟨v, i_ctx_top⟩ₑ.
Proof.
  intros V e v Hmulti. remember (e_val v) as e'.
  induction Hmulti as [| e1 e2]; intros; subst.
  - apply val_eq_plug in H as [H1 H2]. subst. apply rt1n_refl.
  - apply red_decomposition in H as [C' [r1 [r2 [HC [He2 Hr]]]]].
    subst e2. inversion Hr; subst.
    + symmetry in HC.
      apply plug_atomic_eq_plug_i in HC as [C2 [HC' He']]; auto. subst.
      rt1n_trans2.
      * apply plug_expr_mode_cam_red.
      * eapply rt1n_trans.
        -- apply cam_red_add.
        -- apply IHHmulti; auto.
    + symmetry in HC.
      apply plug_atomic_eq_plug_i in HC as [C2 [HC' He']]; auto. subst.
      rt1n_trans2.
      * apply plug_expr_mode_cam_red.
      * eapply rt1n_trans.
        -- apply cam_red_app.
        -- apply IHHmulti; auto.
    + symmetry in HC.
      apply plug_compound_eq_plug_i with (C' := o_ctx_let o_ctx_hole e)
      (v := v0) in HC as [[HC He'] | [C2 [HC' He']]]; subst; auto; simpl.
      * eapply rt1n_trans.
        -- apply cam_red_ret_let.
        -- apply IHHmulti; auto.
      * rt1n_trans2.
        -- apply plug_expr_mode_cam_red.
        -- eapply rt1n_trans.
           ++ apply cam_red_let.
           ++ eapply rt1n_trans.
              ** apply cam_red_ret_let.
              ** apply IHHmulti; auto.
    + symmetry in HC.
      apply plug_compound_eq_plug_i with (C' := o_ctx_handle o_ctx_hole h)
      (v := v0) in HC as [[HC He'] | [C2 [HC' He']]]; subst; auto; simpl.
      * eapply rt1n_trans; try apply cam_red_ret_handle.
        apply IHHmulti; auto.
      * rt1n_trans2.
        -- apply plug_expr_mode_cam_red.
        -- eapply rt1n_trans.
           ++ apply cam_red_handle.
           ++ eapply rt1n_trans.
              ** apply cam_red_ret_handle.
              ** apply IHHmulti; auto.
    + symmetry in HC.
      apply plug_handle_do_eq_plug_i in HC as
      [[C2 [HC' He']] | [C00 [C01 [HC0 [HC He']]]]]; subst.
      * rt1n_trans2.
        -- apply plug_expr_mode_cam_red.
        -- eapply rt1n_trans; try apply cam_red_handle.
           rt1n_trans2.
           ++ apply plug_expr_mode_cam_red.
           ++ eapply rt1n_trans; try apply cam_red_do.
              rt1n_trans2.
              ** apply add_op_mode_cam_red_o. assumption.
              ** rewrite add_oo_hole_r.
                 eapply rt1n_trans. try (apply cam_red_op_handle2; apply H).
                 apply IHHmulti; auto.
      * apply not_o_ctx_handles_op_add_oo_distr1 in H0 as [HC00 HC01].
        rt1n_trans2.
        -- apply plug_expr_mode_cam_red.
        -- eapply rt1n_trans; try apply cam_red_do.
           rt1n_trans2.
           ++ apply add_op_mode_cam_red_o. assumption.
           ++ rewrite add_oo_hole_r. simpl.
              rt1n_trans2.
              ** apply add_op_mode_cam_red_o. assumption.
              ** eapply rt1n_trans; try (apply cam_red_op_handle2; apply H).
                 apply IHHmulti; auto.
Qed.

Theorem lang_equiv_cam :
  forall (V : Set) (e : expr V) (v : value V),
    e -->* v <-> ⟨e, i_ctx_top⟩ₑ ==>* ⟨v, i_ctx_top⟩ₑ.
Proof.
  intros. split; intro.
  - apply lang_cam with (C := i_ctx_top) (e' := e) in H.
    + assumption.
    + simpl. reflexivity.
  - apply cam_lang in H as [H1 _].
    apply H1 with (C := i_ctx_top). reflexivity.
Qed.
