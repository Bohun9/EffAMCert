Require Import CEK.Syntax.
Require Import CEK.Semantics.
Require Import CEK.Tactics.
Require Import General.Definitions.

Inductive cek_non_nat : cek_value -> Prop :=
  | cek_non_nat_lam {V : Set} (e : expr (inc V)) (Γ : V -> cek_value) :
    cek_non_nat (cek_v_lam e Γ)
  | cek_non_nat_cont (C : cek_o_ctx) :
    cek_non_nat (cek_v_cont C).

Inductive cek_non_applicable : cek_value -> Prop :=
  | cek_non_applicable_nat (n : nat) : 
    cek_non_applicable n.

Inductive cek_nf : cek_state -> Prop :=
  | cek_nf_val (w : cek_value) :
    cek_nf ᵉ⟨cek_i_ctx_top, w⟩ᶜ
  | cek_nf_add1 {V : Set} (v1 v2 : value V) (Γ : env V) (C : cek_i_ctx) :
    cek_non_nat (value_to_cek_value v1 Γ) ->
    cek_nf ᵉ⟨e_add v1 v2, Γ, C⟩ₑ
  | cek_nf_add2 {V : Set} (v1 v2 : value V) (Γ : env V) (C : cek_i_ctx) :
    cek_non_nat (value_to_cek_value v2 Γ) ->
    cek_nf ᵉ⟨e_add v1 v2, Γ, C⟩ₑ
  | cek_nf_app {V : Set} (v1 v2 : value V) (Γ : env V) (C : cek_i_ctx) :
    cek_non_applicable (value_to_cek_value v1 Γ) ->
    cek_nf ᵉ⟨e_app v1 v2, Γ, C⟩ₑ
  | cek_nf_do (l : string) (w : cek_value) (C : cek_o_ctx) :
    cek_nf ᵉ⟨cek_i_ctx_top, C, l, w⟩ₒ.

Theorem cek_nf_correct :
  forall (s : cek_state),
    cek_nf s <-> normal_form cek_red s.
Proof.
  intros. split.
  - intro H. inv H.
    + intros [s H]. inv H.
    + intros [s H]. inv H. destruct_existT.
      rewrite H7 in H0. inv H0.
    + intros [s H]. inv H. destruct_existT.
      rewrite H8 in H0. inv H0.
    + intros [s H]. inv H; destruct_existT.
      * rewrite H7 in H0. inv H0.
      * rewrite H7 in H0. inv H0.
    + intros [s H]. inv H.
  - intro H. unfold normal_form in H. destruct s.
    + destruct e.
      * exfalso. apply H. eexists. constructor.
      * remember (value_to_cek_value v1 Γ) as w1 eqn:Hw1.
        remember (value_to_cek_value v2 Γ) as w2 eqn:Hw2.
        symmetry in Hw1. symmetry in Hw2.
        destruct w1; destruct w2.
        -- exfalso. apply H. eexists. constructor; eauto.
        -- apply cek_nf_add2. rewrite Hw2. constructor.
        -- apply cek_nf_add2. rewrite Hw2. constructor.
        -- apply cek_nf_add1. rewrite Hw1. constructor.
        -- apply cek_nf_add1. rewrite Hw1. constructor.
        -- apply cek_nf_add1. rewrite Hw1. constructor.
        -- apply cek_nf_add1. rewrite Hw1. constructor.
        -- apply cek_nf_add1. rewrite Hw1. constructor.
        -- apply cek_nf_add1. rewrite Hw1. constructor.
      * remember (value_to_cek_value v1 Γ) as w1 eqn:Hw1.
        symmetry in Hw1.
        destruct w1.
        -- constructor. rewrite Hw1. constructor.
        -- exfalso. apply H. eexists. apply cek_red_app1.
           rewrite Hw1. reflexivity.
        -- exfalso. apply H. eexists. apply cek_red_app2.
           rewrite Hw1. reflexivity.
      * exfalso. apply H. eexists. constructor.
      * exfalso. apply H. eexists. constructor.
      * exfalso. apply H. eexists. constructor.
    + destruct C.
      * constructor.
      * exfalso. apply H. eexists. constructor.
      * destruct (HandlesOp_dec h l).
        -- destruct H0 as [e_op He_op]. exfalso. apply H.
           eexists. apply cek_red_op_handle2. apply He_op.
        -- exfalso. apply H. eexists. apply cek_red_op_handle1. assumption.
    + destruct C.
      * constructor.
      * exfalso. apply H. eexists. constructor.
      * exfalso. apply H. eexists. constructor.
Qed.
