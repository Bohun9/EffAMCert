Require Import Lang.Syntax.
Require Import Lang.Semantics.
Require Import Lang.ShapeLemmas.
Require Import Lang.ContextProperties.
Require Import Tactics.General.

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

Lemma not_or_and :
  forall (P Q : Prop),
    ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  tauto.
Qed.

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
  - admit.
Admitted.
