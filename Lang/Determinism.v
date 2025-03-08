Require Import Lang.Syntax.
Require Import Lang.Semantics.
Require Import Lang.ContextProperties.
Require Import Lang.ShapeLemmas.
Require Import General.Tactics.
Require Import General.Lemmas.

(* Canonical form is C[a], where a is atomic.
   It is useful, because we can reason about
   equality on such expressions cleanly. *)

Theorem canon_let : 
  forall (V : Set) (C : i_ctx V) (v : value V) e,
    C[ e_let v e ]ᵢ = i_ctx_let C e [ v ]ᵢ.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem canon_handle_ret : 
  forall (V : Set) (C : i_ctx V) (v : value V) h,
    C[ e_handle v h ]ᵢ = i_ctx_handle C h [ v ]ᵢ.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem canon_handle_op :
  forall (V : Set) (C : i_ctx V) (C' : o_ctx V) h l v,
    C[ e_handle (C' [e_do l v]ₒ) h ]ᵢ = (i_ctx_handle C h +ᵢ C') [ e_do l v ]ᵢ.
Proof.
  intros.
  assert (H : C [e_handle (C' [e_do l v ]ₒ) h ]ᵢ =
              i_ctx_handle C h [C' [e_do l v ]ₒ ]ᵢ).
  { reflexivity. }
  rewrite H. rewrite add_i_plug_assoc. reflexivity.
Qed.

Hint Rewrite canon_let : canon.
Hint Rewrite canon_handle_ret : canon.
Hint Rewrite canon_handle_op : canon.

Lemma handle_do_deterministic_i : 
  forall (V : Set) (C1 C2 C1' C2' : i_ctx V) h h' l e_op e_op',
    i_ctx_handle C1 h ᵢ+ᵢ C2 = i_ctx_handle C1' h' ᵢ+ᵢ C2' ->
    ~IctxHandlesOp C2 l ->
    ~IctxHandlesOp C2' l ->
    HandlesOpWith h l e_op ->
    HandlesOpWith h' l e_op' ->
    C1 = C1' /\ C2 = C2' /\ h = h' /\ e_op = e_op'.
Proof.
  intros V C1 C2 C1' C2' h h' l e_op e_op'. generalize dependent C2'. induction C2.
  - destruct C2'; simpl; intros.
    + inj H. intuition.
      eapply HandlesOpWith_deterministic. eauto.
    + discriminate.
    + inj H. exfalso. apply H1. left. eexists. eauto.
  - destruct C2'; simpl; intros.
    + discriminate.
    + inj H. specialize (IHC2 C2' H5 H0 H1 H2 H3) as [? [? [? ?]]]; subst. auto.
    + discriminate.
  - destruct C2'; simpl; intros.
    + inj H. exfalso. apply H0. left. eexists. eauto.
    + discriminate.
    + inj H.
      apply not_or_and in H0 as [_ H0].
      apply not_or_and in H1 as [_ H1].
      specialize (IHC2 C2' H5 H0 H1 H2 H3) as [? [? [? ?]]]. subst. auto.
Qed.

Lemma handle_do_deterministic_o : 
  forall (V : Set) (C1 C1' : i_ctx V) (C2 C2' : o_ctx V) h h' l e_op e_op',
    i_ctx_handle C1 h +ᵢ C2 = i_ctx_handle C1' h' +ᵢ C2' ->
    ~OctxHandlesOp C2 l ->
    ~OctxHandlesOp C2' l ->
    HandlesOpWith h l e_op ->
    HandlesOpWith h' l e_op' ->
    C1 = C1' /\ C2 = C2' /\ h = h' /\ e_op = e_op'.
Proof.
  intros.
  apply not_o_ctx_handles_op_bijection in H0.
  apply not_o_ctx_handles_op_bijection in H1.
  repeat rewrite <- add_ii_eq_add_i in H.
  pose (handle_do_deterministic_i  _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3) as Hdeter.
  destruct Hdeter as [? [? [? ?]]]; subst. intuition.
  apply (f_equal i_to_o) in H5.
  repeat rewrite bijection_composition_o in H5. assumption.
Qed.

Theorem lang_deterministic :
  forall (V : Set) (e1 e2 e3 : expr V),
    e1 --> e2 /\ e1 --> e3 -> e2 = e3.
Proof.
  intros V e1 e2 e3 [Hstep2 Hstep3].
  apply red_decomposition in Hstep2 as [C [r1 [r2 [He1 [He2 Hr]]]]]. subst.
  apply red_decomposition in Hstep3 as [C' [r1' [r2' [He1' [He3 Hr']]]]]. subst.
  inv Hr; inv Hr'; autorewrite with canon in *;
  apply plug_atomic_eq_plug_atomic_i in He1' as [HC Ha]; auto;
  try discriminate; injection Ha; try injection HC; intros; subst; clear Ha.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - pose (handle_do_deterministic_o  _ _ _ _ _ _ _ _ _ _ HC H0 H2 H H1) as Hdeter.
    destruct Hdeter as [? [? [? ?]]]; subst. reflexivity.
Qed.
