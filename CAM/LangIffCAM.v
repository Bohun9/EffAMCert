Require Import CAM.Syntax.
Require Import CAM.Semantics.
Require Import CAM.ShapeLemmas.
Require Import Lang.Semantics.
Require Import Lang.ContextProperties.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.

Ltac simplIH :=
  match goal with
  | [ _ : _ ==> ⟨?e, ?C⟩ₑ, IH1 : forall (_ : expr _), _, IH2 : forall (_ : i_ctx _), _ |- _] =>
      clear IH2;
      let e' := fresh "e" in
      let C' := fresh "C" in
      remember e as e' eqn:He;
      remember C as C' eqn:Hc;
      specialize (IH1 e' C' eq_refl);
      subst
  | [ _ : _ ==> ⟨?C1, ?C2, ?l, ?w⟩ₒ, IH1 : forall (_ : expr _), _, IH2 : forall (_ : i_ctx _), _ |- _] =>
      clear IH1;
      let C1' := fresh "C1" in
      let C2' := fresh "C2" in
      let l' := fresh "l" in
      let w' := fresh "w" in
      remember C1 as C1' eqn:HC1;
      remember C2 as C2' eqn:HC2;
      remember l  as l' eqn:Hl;
      remember w  as w' eqn:Hw;
      specialize (IH2 C1' C2' l' w' eq_refl);
      subst
  end.

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
  intros. remember ⟨v, i_ctx_top⟩ₑ as s'. induction H as [| s s2 s'];
    subst; intros.
  - split; try discriminate; intros.
    injection H; intros; subst. simpl. apply rt1n_refl.
  - specialize (IHclos_refl_trans_1n eq_refl).
    destruct IHclos_refl_trans_1n as [IH1 IH2].
    inversion H; subst; split; intros; try discriminate;
    injection H1; intros; subst; clear H1; try simplIH.
    + eapply rt1n_trans.
      * apply red_context. apply red_add.
      * apply IH1.
    + eapply rt1n_trans.
      * apply red_context. apply red_app.
      * apply IH1.
    + apply IH1.
    + apply IH1.
    + eapply rt1n_trans.
      * simpl. apply red_context. apply red_let.
      * apply IH1.
    + eapply rt1n_trans.
      * simpl. apply red_context. apply red_handle_ret.
      * apply IH1.
    + apply IH2. auto.
    + apply IH2. simpl. assumption.
    + apply IH2. simpl. tauto.
    + simpl. eapply rt1n_trans.
      * apply red_context. apply red_handle_do; try assumption.
        apply HHandlesOp.
      * apply IH1.
Qed.

Ltac inv H := inversion H; subst; clear H.

Ltac rt1n_trans2 := 
  apply clos_rt_rt1n; eapply rt_trans; apply clos_rt1n_rt.

Ltac rt1n_step :=
  apply clos_rt_rt1n; apply rt_step.

Ltac cam_red_step :=
  rt1n_step; constructor.

Ltac crush_cam_red :=
  repeat (try autorewrite with core; try simpl; try auto; match goal with
  | [ |- _ ] => cam_red_step
  | [ |- _ ] => rt1n_trans2; cam_red_step
  | [ |- ⟨ _ [_]ₒ, _ ⟩ₑ ==>* _ ] => rt1n_trans2; (try apply plug_expr_mode_cam_red)
  | [ |- ⟨ e_handle _ _, _ ⟩ₑ ==>* _ ] => rt1n_trans2; (try cam_red_step)
  | [ |- ⟨ e_do _ _, _ ⟩ₑ ==>* _ ] => rt1n_trans2; (try cam_red_step)
  | [ |- ⟨ _ +ᵢ _, _, _, _ ⟩ₒ ==>* _ ] => rt1n_trans2; (try apply add_op_mode_cam_red_o)
  end).

Lemma lang_cam_step:
  forall (V : Set) (C C' : i_ctx V) e r1 r2,
    r1 ~~> r2 ->
    C[e]ᵢ = C'[r1]ᵢ ->
    ⟨e, C⟩ₑ ==>* ⟨r2, C'⟩ₑ.
Proof.
  intros. symmetry in H0. inv H.
  - apply plug_atomic_eq_plug_i in H0 as [C2 [? ?]]; auto; subst.
    crush_cam_red.
  - apply plug_atomic_eq_plug_i in H0 as [C2 [? ?]]; auto; subst.
    crush_cam_red.
  - apply plug_compound_eq_plug_i with (C' := o_ctx_let o_ctx_hole e0)
      (v := v) in H0 as [[HC He'] | [C2 [? ?]]]; auto; subst;
    crush_cam_red.
  - apply plug_compound_eq_plug_i with (C' := o_ctx_handle o_ctx_hole h)
      (v := v) in H0 as [[HC He'] | [C2 [? ?]]]; auto; subst;
    crush_cam_red.
  - apply plug_handle_do_eq_plug_i in H0 as
      [[C2 [? ?]] | [C00 [C01 [? [? ?]]]]]; subst.
      + crush_cam_red.
      + apply not_o_ctx_handles_op_add_oo_distr1 in H2 as [HC00 HC01].
        crush_cam_red.
Qed.

Theorem lang_cam :
  forall (V : Set) (e : expr V) (v : value V),
    e -->* v -> 
    forall (C : i_ctx V) e',
    e = C[e']ᵢ -> ⟨e', C⟩ₑ ==>* ⟨v, i_ctx_top⟩ₑ.
Proof.
  intros V e v multi. remember (e_val v) as e'.
  induction multi as [| e1 e2]; intros; subst.
  - apply val_eq_plug in H as [H1 H2]. subst. apply rt1n_refl.
  - apply red_decomposition in H as [C' [r1 [r2 [HC [He2 Hr]]]]]. subst e2.
    pose (lang_cam_step _ _ _ _ _ _ Hr HC) as Hred.
    rt1n_trans2.
    + apply Hred.
    + apply IHmulti; auto.
Qed.

Theorem lang_iff_cam :
  forall (V : Set) (e : expr V) (v : value V),
    e -->* v <-> ⟨e, i_ctx_top⟩ₑ ==>* ⟨v, i_ctx_top⟩ₑ.
Proof.
  intros. split; intro.
  - apply lang_cam with (e := e); auto.
  - apply cam_lang in H as [H1 _].
    apply H1 with (C := i_ctx_top). reflexivity.
Qed.
