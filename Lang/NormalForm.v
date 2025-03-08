Require Import Lang.Syntax.
Require Import Lang.Semantics.
Require Import Lang.ShapeLemmas.
Require Import Lang.ContextProperties.
Require Import General.Tactics.
Require Import General.Lemmas.

Definition normal_form {A : Set} (R : A -> A -> Prop) (a : A) :=
  ~exists a', R a a'.

Inductive non_nat {V : Set} : value V -> Prop :=
  | non_nat_var (v : V) : non_nat (v_var v)
  | non_nat_lam (e : expr (inc V)) : non_nat (v_lam e).

Inductive non_lam {V : Set} : value V -> Prop :=
  | non_lam_nat (n : nat) : non_lam n
  | non_lam_var (v : V) : non_lam (v_var v).

Inductive lang_nf {V : Set} : expr V -> Prop :=
  | lang_nf_val (v : value V) : lang_nf v
  | lang_nf_add1 : forall C v1 v2, non_nat v1     -> lang_nf (C[ e_add v1 v2 ]ᵢ)
  | lang_nf_add2 : forall C v1 v2, non_nat v2     -> lang_nf (C[ e_add v1 v2 ]ᵢ)
  | lang_nf_app : forall C v1 v2, non_lam v1      -> lang_nf (C[ e_app v1 v2 ]ᵢ)
  | lang_nf_do : forall C v l, ~IctxHandlesOp C l -> lang_nf (C[ e_do l v ]ᵢ).

Hint Constructors lang_nf : core.

Inductive predex {V : Set} : expr V -> Prop :=
  | predex_add : forall v1 v2, predex (e_add v1 v2)
  | predex_app : forall v1 v2, predex (e_app v1 v2)
  | predex_let : forall (v : value V) e, predex (e_let v e)
  | predex_handle_ret : forall (v : value V) h, predex (e_handle v h)
  | predex_handle_do : forall h (C : o_ctx V) l v,
      ~OctxHandlesOp C l -> HandlesOp h l ->
      predex (e_handle (C [ e_do l v ]ₒ) h).

Hint Constructors predex : core.

Lemma lang_decomposition_o :
  forall {V : Set} (e : expr V),
    (exists (v : value V), e = v)
    \/ (exists C p, e = C[p]ₒ /\ predex p)
    \/ (exists C l v, e = C[ e_do l v ]ₒ /\ ~OctxHandlesOp C l).
Proof.
  intros. induction e.
  - eauto.
  - right. left. exists o_ctx_hole. simpl. eauto.
  - right. left. exists o_ctx_hole. simpl. eauto.
  - destruct IHe1 as [[v ?] | [[C [p [HC Hp]]] | [C [l [v [He1 HC]]]]]]; subst.
    + right. left. exists o_ctx_hole. simpl. eauto.
    + right. left. exists (o_ctx_let C e2). simpl. eauto.
    + right. right. exists (o_ctx_let C e2). simpl. eauto.
  - right. right. exists o_ctx_hole. simpl. eauto.
  - destruct IHe as [[v ?] | [[C [p [HC Hp]]] | [C [l [v [He HC]]]]]]; subst.
    + right. left. exists o_ctx_hole. simpl. eauto.
    + right. left. exists (o_ctx_handle C h). simpl. eauto.
    + destruct (HandlesOp_dec h l).
      * right. left. exists o_ctx_hole. simpl. eauto.
      * right. right. exists (o_ctx_handle C h). simpl.
        exists l. exists v. tauto.
Qed.

Lemma lang_decomposition_i :
  forall {V : Set} (e : expr V),
    (exists (v : value V), e = v)
    \/ (exists C p, e = C[p]ᵢ /\ predex p)
    \/ (exists C l v, e = C[ e_do l v ]ᵢ /\ ~IctxHandlesOp C l).
Proof.
  intros.
  destruct (lang_decomposition_o e) as [[v ?] | [[C [p [? ?]]] | [C [l [v [? ?]]]]]]; subst.
  - eauto.
  - right. left. exists (o_to_i C). exists p. intuition.
    apply o_plug_bijection.
  - right. right. exists (o_to_i C). exists l. exists v. split; auto.
    apply o_plug_bijection.
Qed.

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

Ltac inv_redex :=
  match goal with
  | [ Hr : ?r1 ~~> ?r2, HC : _ = _ [?r1]ᵢ |- _ ] =>
      inv Hr; try rewrite canon_let in HC;
      try rewrite canon_handle_ret in HC; try rewrite canon_handle_op in HC;
      let HC' := fresh "HC'" in
      apply plug_atomic_eq_plug_atomic_i in HC as [? HC']; auto;
      try discriminate HC'; injection HC' as ? ?; subst
  end.

Ltac Handles_contra :=
  match goal with
  | [ H1 : ~HandlesOp ?h ?l, H2 : HandlesOpWith ?h ?l ?e  |- _ ] =>
      let H := fresh "H" in
      assert (H : HandlesOp h l);
      [ exists e; assumption | auto ]
  end.

Theorem lang_nf_correct :
  forall (V : Set) (e : expr V),
    lang_nf e <-> normal_form red e.
Proof.
  intros. split.
  - intro H. inv H; intros [e Hstep];
    apply red_decomposition in Hstep as [C' [r1 [r2 [Hv [He Hr]]]]]; subst.
    + apply val_eq_plug in Hv as [HC Hv]. subst. inversion Hr.
    + inv_redex. inv H0.
    + inv_redex. inv H0.
    + inv_redex. inv H0.
    + inv_redex. apply not_i_ctx_handles_op_add_i_distr1 in H0 as [? ?].
      simpl in H0. apply not_or_and in H0 as [? _]. Handles_contra.
  - intros Hnf. destruct (lang_decomposition_i e)
    as [[v ?] | [[C [p [? Hp]]] | [C [l [v [? ?]]]]]]; subst.
    + apply lang_nf_val.
    + inv Hp; unfold normal_form in Hnf.
      * destruct v1; destruct v2.
        -- exfalso. apply Hnf. eexists. apply red_context. constructor.
        -- apply lang_nf_add2. constructor.
        -- apply lang_nf_add2. constructor.
        -- apply lang_nf_add1. constructor.
        -- apply lang_nf_add1. constructor.
        -- apply lang_nf_add1. constructor.
        -- apply lang_nf_add1. constructor.
        -- apply lang_nf_add1. constructor.
        -- apply lang_nf_add1. constructor.
      * destruct v1.
        -- apply lang_nf_app. constructor.
        -- apply lang_nf_app. constructor.
        -- exfalso. apply Hnf. eexists. apply red_context. constructor.
      * exfalso. apply Hnf. eexists. apply red_context. constructor.
      * exfalso. apply Hnf. eexists. apply red_context. constructor.
      * exfalso. apply Hnf. destruct H0 as [e He]. eexists.
        apply red_context. constructor.
        -- apply He.
        -- assumption.
    + apply lang_nf_do. assumption.
Qed.
