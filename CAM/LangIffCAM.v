Require Import CAM.Syntax.
Require Import CAM.Semantics.
Require Import CAM.NormalForm.
Require Import Lang.ShapeLemmas.
Require Import Lang.Semantics.
Require Import Lang.ContextProperties.
Require Import Lang.NormalForm.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import General.Tactics.

Ltac simplIH :=
  match goal with
  | [ _ : _ ==> ⟨?e, ?C⟩ₑ, IH1 : forall (_ : expr _), _, IH2 : forall (_ : i_ctx _), _ |- _] =>
      clear IH2;
      let e' := fresh "e" in
      let C' := fresh "C" in
      let n' := fresh "n'" in
      remember e as e' eqn:He;
      remember C as C' eqn:Hc;
      specialize (IH1 e' C' eq_refl) as [n' [IH Hn']];
      subst; exists n'; split; simpl; auto
  | [ _ : _ ==> ⟨?C1, ?C2, ?l, ?w⟩ₒ, IH1 : forall (_ : expr _), _, IH2 : forall (_ : i_ctx _), _ |- _] =>
      clear IH1;
      let C1' := fresh "C1" in let C2' := fresh "C2" in
      let l' := fresh "l" in
      let w' := fresh "w" in
      let n' := fresh "n'" in
      remember C1 as C1' eqn:HC1;
      remember C2 as C2' eqn:HC2;
      remember l  as l' eqn:Hl;
      remember w  as w' eqn:Hw;
      specialize (IH2 C1' C2' l' w' eq_refl); subst
  end.

Lemma cam_lang_nf_base :
  forall (V : Set) (n : cam_state V),
    cam_nf n ->
    (forall e C, n = ⟨e, C⟩ₑ -> exists n', C[e]ᵢ -->* n' /\ nf_rel_lang_cam n' n)
    /\ (forall (C : i_ctx V) (C' : o_ctx V) l w,
      n = ⟨C, C', l, w⟩ₒ -> ~OctxHandlesOp C' l ->
      exists n', C[ C'[e_do l w]ₒ ]ᵢ -->* n' /\ nf_rel_lang_cam n' n).
Proof.
  intros. inv H; split; intros; try discriminate;
  injection H; intros; subst. clear H.
  - exists v. intuition.
  - exists (C0 [e_add v1 v2 ]ᵢ). intuition.
  - exists (C0 [e_add v1 v2 ]ᵢ). intuition.
  - exists (C0 [e_app v1 v2 ]ᵢ). intuition.
  - exists ((toᵢ C') [e_do l0 w ]ᵢ). simpl. split.
    + rewrite <- o_plug_bijection. apply rt1n_refl.
    + rewrite <- bijection_composition_o at 2.
      apply nf_rel_lang_cam_do.
      apply not_o_ctx_handles_op_bijection.
      assumption.
Qed.

Theorem cam_lang_nf :
  forall (V : Set) (s n : cam_state V),
    s ==>* n /\ cam_nf n ->
    (forall e (C : i_ctx V),
      s = ⟨e, C⟩ₑ -> exists n', C[e]ᵢ -->* n' /\ nf_rel_lang_cam n' n)
    /\ (forall (C : i_ctx V) (C' : o_ctx V) l w,
      s = ⟨C, C', l, w⟩ₒ -> ~OctxHandlesOp C' l ->
      exists n', C[ C'[e_do l w]ₒ ]ᵢ -->* n' /\ nf_rel_lang_cam n' n).
Proof.
  intros V s n [multi Hn]. induction multi as [s | s s2 n]; intros.
  - apply cam_lang_nf_base. assumption.
  - specialize (IHmulti Hn).
    destruct IHmulti as [IH1 IH2].
    inversion H; subst; split; intros; try discriminate;
    injection H0; intros; subst; simplIH.
    + eapply rt1n_trans.
      * apply red_context. apply red_add.
      * apply IH.
    + eapply rt1n_trans.
      * apply red_context. apply red_app.
      * apply IH.
    + eapply rt1n_trans.
      * apply red_context. apply red_let.
      * apply IH.
    + eapply rt1n_trans.
      * apply red_context. apply red_handle_ret.
      * apply IH.
    + apply IH2. auto.
    + apply IH2. auto.
    + apply IH2. simpl. tauto.
    + eapply rt1n_trans.
      * apply red_context. apply red_handle_do.
        -- apply HHandlesOp.
        -- assumption.
      * apply IH.
Qed.

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

Lemma lang_cam_nf_base :
  forall (V : Set) (n : expr V), lang_nf n ->
    forall C e, n = C[e]ᵢ ->
    exists n', ⟨e, C⟩ₑ ==>* n' /\ nf_rel_lang_cam n n'.
Proof.
  intros; subst. inv H.
  - apply val_eq_plug in H1 as [? ?]. subst. exists ⟨v, i_ctx_top⟩ₑ. auto.
  - apply plug_atomic_eq_plug_i in H0 as [C2 [HC0 He]]; auto; subst.
    exists ⟨e_add v1 v2, C +ᵢ C2⟩ₑ. auto.
  - apply plug_atomic_eq_plug_i in H0 as [C2 [HC0 He]]; auto; subst.
    exists ⟨e_add v1 v2, C +ᵢ C2⟩ₑ. auto.
  - apply plug_atomic_eq_plug_i in H0 as [C2 [HC0 He]]; auto; subst.
    exists ⟨e_app v1 v2, C +ᵢ C2⟩ₑ. auto.
  - apply plug_atomic_eq_plug_i in H0 as [C2 [HC0 He]]; auto; subst.
    exists ⟨i_ctx_top, toₒ (C +ᵢ C2), l, v⟩ₒ. split.
    + apply not_i_ctx_handles_op_add_i_distr1 in H1 as [HC HC2].
      crush_cam_red. rewrite <- bijection_composition_i at 1. 
      unfold o_to_i. crush_cam_red.
      * apply not_i_ctx_handles_op_bijection. assumption.
      * rewrite add_oo_eq_add_i. apply rt1n_refl.
    + auto.
Qed.

Lemma lang_cam_nf_step :
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

Theorem lang_cam_nf :
  forall (V : Set) (e n : expr V),
    e -->* n /\ lang_nf n -> 
    forall C e', e = C[e']ᵢ ->
    exists n', ⟨e', C⟩ₑ ==>* n' /\ nf_rel_lang_cam n n'.
Proof.
  intros V e n [multi Hn].
  induction multi as [| e1 e2]; intros; subst.
  - eapply lang_cam_nf_base.
    + apply Hn.
    + reflexivity.
  - apply red_decomposition in H as [C' [r1 [r2 [HC [He2 Hr]]]]]. subst e2.
    pose (lang_cam_nf_step _ _ _ _ _ _ Hr HC) as Hred.
    specialize (IHmulti Hn C' r2 eq_refl) as [n' [IH1 IH2]]. 
    exists n'. split.
    + rt1n_trans2.
      * apply Hred.
      * apply IH1.
    + apply IH2.
Qed.

Theorem lang_iff_cam_nf :
  (forall (V : Set) (e n : expr V),
    e -->* n /\ lang_nf n ->
    exists n', ⟨e, i_ctx_top⟩ₑ ==>* n' /\ nf_rel_lang_cam n n')
  /\
  (forall (V : Set) (e : expr V) (n : cam_state V),
    ⟨e, i_ctx_top⟩ₑ ==>* n /\ cam_nf n ->
    exists n', e -->* n' /\ nf_rel_lang_cam n' n).
Proof.
  split; intros.
  - apply lang_cam_nf with (e := e); auto.
  - apply cam_lang_nf in H as [H1 _].
    apply H1 with (C := i_ctx_top).
    reflexivity.
Qed.

(* ========================================================================= *)
(* More general prototype *)

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

Theorem diverges_coind' : forall (A : Set) (E : A -> A -> Prop) (a : A),
  diverges E a -> exists (R : A -> Prop),
  R a /\ forall a, R a -> exists a', E a a' /\ R a'.
Proof.
  intros. exists (diverges E). intuition.
  inversion H0; subst. exists a2. auto.
Qed.

Print diverges_coind.

Definition ω := (v_lam (e_app (v_var VZ) (v_var VZ))) : value Empty_set.
Definition Ω := e_app ω ω : expr Empty_set.

Lemma omega_inf :
  diverges red Ω.
Proof.
  apply diverges_coind with (R := (fun e => e = Ω)).
  - intros. subst. exists Ω. intuition.
    assert (H : Ω = esubst (e_app (v_var VZ) (v_var VZ)) ω).
    { unfold esubst. simpl. reflexivity. }
    rewrite H at 2. apply red_app.
  - reflexivity.
Qed.

Theorem lang_iff_cam_inf :
  forall (V : Set) (e : expr V),
    diverges red e <-> diverges cam_red ⟨e, i_ctx_top⟩ₑ.
Abort.
