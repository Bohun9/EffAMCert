Require Import Lang.Syntax.
Require Import Lang.ContextProperties.
Require Import Coq.Relations.Relation_Operators.

Reserved Notation "e '-->' e'" (at level 40).

Inductive red {V : Set} : expr V -> expr V -> Prop :=
  | red_add (n1 n2 : nat) :
      e_add n1 n2 --> (n1 + n2)
  | red_app (e : expr (inc V)) (v : value V) :
      e_app (v_lam e) v --> esubst e v
  | red_let (v : value V) (e : expr (inc V)) :
      e_let (e_val v) e --> esubst e v
  | red_handle_ret (v : value V) (h : handler V) :
      e_handle v h --> esubst (ret_clause h) v
  | red_handle_do
      (h : handler V) (e_op : expr (inc (inc V)))
      (C : o_ctx V) (l : string) (v : value V) :
      HandlesOpWith h l e_op ->
      ~OctxHandlesOp C l ->
      e_handle (C [e_do l v]ₒ) h -->
        esubst (esubst e_op (vshift v))
               (v_lam (e_handle (o_ctx_shift C [v_var VZ]ₒ) (hshift h)))
  | red_context
      (C : i_ctx V)
      (e1 e2 : expr V)
      (Hred : e1 --> e2) :
      C[e1]ᵢ --> (C[e2]ᵢ)
where "e '-->' e'" := (red e e').

Notation "e '-->*' e'" := (clos_refl_trans_1n _ red e e') (at level 40).

Definition nat_refl :
  @v_nat Empty_set 42 -->* @v_nat Empty_set 42.
Proof.
  apply rt1n_refl.
Qed.

Reserved Notation "e '~~>' e'" (at level 40).

Inductive contraction {V : Set} : expr V -> expr V -> Prop :=
  | contraction_add (n1 n2 : nat) :
      e_add n1 n2 ~~> (n1 + n2)
  | contraction_app (e : expr (inc V)) (v : value V) :
      e_app (v_lam e) v ~~> esubst e v
  | contraction_let (v : value V) (e : expr (inc V)) :
      e_let (e_val v) e ~~> esubst e v
  | contraction_handle_ret (v : value V) (h : handler V) :
      e_handle v h ~~> esubst (ret_clause h) v
  | contraction_handle_do
      (h : handler V) (e_op : expr (inc (inc V)))
      (C : o_ctx V) (l : string) (v : value V) :
      HandlesOpWith h l e_op ->
      ~OctxHandlesOp C l ->
      e_handle (C [e_do l v]ₒ) h ~~>
        esubst (esubst e_op (vshift v))
               (v_lam (e_handle (o_ctx_shift C [v_var VZ]ₒ) (hshift h)))
where "e '~~>' e'" := (contraction e e').

Hint Constructors contraction : contr_ctors.

Theorem red_decomposition :
  forall (V : Set) e1 e2,
    e1 --> e2 ->
    (exists (C : i_ctx V) r1 r2,
         e1 = C[r1]ᵢ
      /\ e2 = C[r2]ᵢ
      /\ r1 ~~> r2).
Proof.
  intros. induction H;
  try solve [
    exists i_ctx_top; eexists; eexists; simpl;
    repeat split; auto with contr_ctors
  ].
  - destruct IHred as [C2 [r1 [r2 [Hr1 [Hr2 Hcontr]]]]]. subst.
    exists (C ᵢ+ᵢ C2). exists r1. exists r2.
    repeat split.
    + rewrite add_ii_plug_assoc. reflexivity.
    + rewrite add_ii_plug_assoc. reflexivity.
    + assumption.
Qed.
