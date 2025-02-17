Require Import CAM.Syntax.
Require Import Lang.Semantics.
Require Import Lang.ContextProperties.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.

Reserved Notation "k '==>' k'" (at level 40).

Inductive cam_red {V : Set} : cam_state V -> cam_state V -> Prop :=
  | cam_red_add
      (n1 n2 : nat) (C : i_ctx V) :
      ⟨e_add n1 n2, C⟩ₑ ==>
      ⟨n1 + n2, C⟩ₑ
  | cam_red_app
      (e : expr (inc V)) (v : value V) (C : i_ctx V) :
      ⟨e_app (v_lam e) v, C⟩ₑ ==>
      ⟨esubst e v, C⟩ₑ
  | cam_red_let
      (e1 : expr V) (e2 : expr (inc V)) (C : i_ctx V) :
      ⟨e_let e1 e2, C⟩ₑ ==>
      ⟨e1, i_ctx_let C e2⟩ₑ
  | cam_red_handle
      (e : expr V) (h : handler V) (C : i_ctx V) :
      ⟨e_handle e h, C⟩ₑ ==>
      ⟨e, i_ctx_handle C h⟩ₑ
  | cam_red_ret_let
      (v : value V) (e2 : expr (inc V)) (C : i_ctx V) :
      ⟨v, i_ctx_let C e2⟩ₑ ==>
      ⟨esubst e2 v, C⟩ₑ
  | cam_red_ret_handle
      (v : value V) (h : handler V) (C : i_ctx V) :
      ⟨v, i_ctx_handle C h⟩ₑ ==>
      ⟨esubst (ret_clause h) v, C⟩ₑ
  | cam_red_do
      (l : string) (v : value V) (C : i_ctx V) :
      ⟨e_do l v, C⟩ₑ ==>
      ⟨C, o_ctx_hole, l, v⟩ₒ
  | cam_red_op_let
      (C : i_ctx V) (C' : o_ctx V) (l : string)
      (v : value V) (e2 : expr (inc V)) :
      ⟨i_ctx_let C e2, C', l, v⟩ₒ ==>
      ⟨C, o_ctx_let C' e2, l, v⟩ₒ
  | cam_red_op_handle1
      (C : i_ctx V) (C' : o_ctx V) (l : string)
      (v : value V) (h : handler V)
      (HNotHandlesOp : ~HandlesOp h l) :
      ⟨i_ctx_handle C h, C', l, v⟩ₒ ==>
      ⟨C, o_ctx_handle C' h, l, v⟩ₒ
  | cam_red_op_handle2
      (C : i_ctx V) (C' : o_ctx V) (l : string)
      (v : value V) (h : handler V) (e_op : expr (inc (inc V)))
      (HHandlesOp : HandlesOpWith h l e_op) :
      ⟨i_ctx_handle C h, C', l, v⟩ₒ ==>
      ⟨esubst (esubst e_op (vshift v))
              (v_lam (e_handle (o_ctx_shift C' [v_var VZ]ₒ) (hshift h))), C⟩ₑ

where "k '==>' k'" := (cam_red k k').

Notation "k '==>*' k'" := (clos_refl_trans_1n _ cam_red k k') (at level 40).

Lemma plug_expr_mode_cam_red : 
  forall (V : Set) (C : i_ctx V) (C' : o_ctx V) e,
    ⟨C'[e]ₒ, C⟩ₑ ==>* ⟨e, C +ᵢ C'⟩ₑ.
Proof.
  intros. generalize dependent C. induction C'; intro.
  - simpl. apply rt1n_refl.
  - simpl. eapply rt1n_trans.
    + apply cam_red_let.
    + apply IHC'.
  - simpl. eapply rt1n_trans.
    + apply cam_red_handle.
    + apply IHC'.
Qed.

Lemma not_or_and : forall A B : Prop, ~(A \/ B) -> ~A /\ ~B.
Proof.
  intros. split.
  - intros HA. apply H. left. assumption.
  - intros HB. apply H. right. assumption.
Qed.

Lemma add_op_mode_cam_red_i :
  forall (V : Set) (C1 C2 : i_ctx V) (C' : o_ctx V) l v,
    ~IctxHandlesOp C2 l ->
    ⟨C1 ᵢ+ᵢ C2, C', l, v⟩ₒ ==>* ⟨C1, C2 +ₒ C', l, v⟩ₒ.
Proof.
  intros. generalize dependent C'. induction C2; intro; simpl in H.
  - simpl. apply rt1n_refl.
  - simpl. eapply rt1n_trans.
    + apply cam_red_op_let.
    + apply IHC2. assumption.
  - apply not_or_and in H as [Hh HC2].
    simpl. eapply rt1n_trans.
    + apply cam_red_op_handle1. assumption.
    + apply IHC2. assumption.
Qed.

Lemma add_op_mode_cam_red_o :
  forall (V : Set) (C1 : i_ctx V) (C2 C' : o_ctx V) l v,
    ~OctxHandlesOp C2 l ->
    ⟨C1 +ᵢ C2, C', l, v⟩ₒ ==>* ⟨C1, C2 ₒ+ₒ C', l, v⟩ₒ.
Proof.
  intros.
  rewrite <- add_ii_eq_add_i.
  rewrite <- add_o_eq_add_oo.
  apply add_op_mode_cam_red_i.
  apply not_o_ctx_handles_op_bijection.
  assumption.
Qed.
