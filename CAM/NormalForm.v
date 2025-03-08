Require Import Lang.NormalForm.
Require Import Lang.ContextProperties.
Require Import CAM.Syntax.
Require Import CAM.Semantics.
Require Import General.Tactics.

Inductive cam_nf {V : Set} : cam_state V -> Prop :=
  | cam_nf_val (v : value V) : cam_nf ⟨v, i_ctx_top⟩ₑ
  | cam_nf_add1 : forall C v1 v2, non_nat v1 -> cam_nf ⟨e_add v1 v2, C⟩ₑ
  | cam_nf_add2 : forall C v1 v2, non_nat v2 -> cam_nf ⟨e_add v1 v2, C⟩ₑ
  | cam_nf_app : forall C v1 v2, non_lam v1  -> cam_nf ⟨e_app v1 v2, C⟩ₑ
  | cam_nf_do : forall C l v, cam_nf ⟨i_ctx_top, C, l, v⟩ₒ.

Hint Constructors cam_nf : core.

Theorem cam_nf_correct :
  forall (V : Set) (s : cam_state V),
    cam_nf s <-> normal_form cam_red s.
Proof.
  intros. split.
  (* cam_nf s -> normal_form cam_red s *)
  - intros H. inv H.
    + intros [s Hstep]. inv Hstep.
    + intros [s Hstep]. inv Hstep. inv H0.
    + intros [s Hstep]. inv Hstep. inv H0.
    + intros [s Hstep]. inv Hstep. inv H0.
    + intros [s Hstep]. inv Hstep.

  (* normal_form cam_red s -> cam_nf s  *)
  - intros H. unfold normal_form in H. destruct s.
    + destruct e.
      * destruct C.
        -- apply cam_nf_val.
        -- exfalso. apply H. eexists. constructor.
        -- exfalso. apply H. eexists. constructor.
      * destruct v1; destruct v2.
        -- exfalso. apply H. eexists. constructor.
        -- apply cam_nf_add2. constructor.
        -- apply cam_nf_add2. constructor.
        -- apply cam_nf_add1. constructor.
        -- apply cam_nf_add1. constructor.
        -- apply cam_nf_add1. constructor.
        -- apply cam_nf_add1. constructor.
        -- apply cam_nf_add1. constructor.
        -- apply cam_nf_add1. constructor.
      * destruct v1.
        -- apply cam_nf_app. constructor.
        -- apply cam_nf_app. constructor.
        -- exfalso. apply H. eexists. constructor.
      * exfalso. apply H. eexists. constructor.
      * exfalso. apply H. eexists. constructor.
      * exfalso. apply H. eexists. constructor.
    + destruct C.
      * apply cam_nf_do.
      * exfalso. apply H. eexists. constructor.
      * destruct (HandlesOp_dec h l).
        -- destruct H0 as [e_op He_op].
           exfalso. apply H. eexists. apply cam_red_op_handle2. apply He_op.
        -- exfalso. apply H. eexists. apply cam_red_op_handle1. assumption.
Qed.

Inductive nf_rel_lang_cam {V : Set} : expr V -> cam_state V -> Prop :=
  | nf_rel_lang_cam_val (v : value V) : nf_rel_lang_cam v ⟨v, i_ctx_top⟩ₑ
  | nf_rel_lang_cam_add1 : forall C v1 v2, non_nat v1 ->
      nf_rel_lang_cam (C [e_add v1 v2]ᵢ) ⟨e_add v1 v2, C⟩ₑ
  | nf_rel_lang_cam_add2 : forall C v1 v2, non_nat v2 ->
      nf_rel_lang_cam (C [e_add v1 v2]ᵢ) ⟨e_add v1 v2, C⟩ₑ
  | nf_rel_lang_cam_app : forall C v1 v2, non_lam v1 ->
      nf_rel_lang_cam (C [e_app v1 v2]ᵢ) ⟨e_app v1 v2, C⟩ₑ
  | nf_rel_lang_cam_do : forall C v l, ~IctxHandlesOp C l ->
      nf_rel_lang_cam (C[ e_do l v ]ᵢ) ⟨i_ctx_top, toₒ C, l, v⟩ₒ.

Hint Constructors nf_rel_lang_cam : core.

Lemma nf_rel_lang_cam_correct :
  forall (V : Set) (e : expr V) (s : cam_state V),
    nf_rel_lang_cam e s -> lang_nf e /\ cam_nf s.
Proof.
  intros. inv H; auto.
Qed.
