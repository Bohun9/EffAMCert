Require Import Lang.Syntax.
Require Import Lang.ContextProperties.
Require Import Coq.Relations.Relation_Operators.

Reserved Notation "e '-->' e'" (at level 40).

Inductive red {V : Set} : expr V -> expr V -> Prop :=
  | red_add (n1 n2 : nat) :
      (e_add (v_nat n1) (v_nat n2)) --> (e_ret (v_nat (n1 + n2)))
  | red_app (e : expr (inc V)) (v : value V) :
      (e_app (v_lam e) v) --> (esubst e v)
  | red_let (v : value V) (e : expr (inc V)) :
      (e_let (e_ret v) e) --> (esubst e v)
  | red_handle_ret (v : value V) (h : handler V) :
      (e_handle (e_ret v) h) --> (esubst (ret_clause h) v)
  | red_handle_do
      (h : handler V)
      (l : string)
      (v : value V)
      (ctx : oi_ctx V)
      (e_op : expr (inc (inc V)))
      (He_op : HandlesOp h l e_op)
      (Hctx : ~OiCtxHandlesOp ctx l) :
      (e_handle (oi_plug ctx (e_do l v)) h) -->
      (esubst (esubst e_op (vshift v))
              (v_lam (oi_plug (oi_shift ctx) (e_ret (v_var VZ)))))
  | red_context
      (c : io_ctx V)
      (e1 e2 : expr V)
      (Hred : e1 --> e2) :
      io_plug c e1 --> io_plug c e2
where "e '-->' e'" := (red e e').

Notation "e '-->*' e'" := (clos_refl_trans_1n _ red e e') (at level 40).

Definition nat_refl :
  (e_ret (@v_nat Empty_set 42)) -->* (e_ret (@v_nat Empty_set 42)).
Proof.
  apply rt1n_refl.
Qed.

Reserved Notation "e '~~>' e'" (at level 40).

Inductive contraction {V : Set} : expr V -> expr V -> Prop :=
  | contraction_add (n1 n2 : nat) :
      (e_add (v_nat n1) (v_nat n2)) ~~> (e_ret (v_nat (n1 + n2)))
  | contraction_app (e : expr (inc V)) (v : value V) :
      (e_app (v_lam e) v) ~~> (esubst e v)
  | contraction_let (v : value V) (e : expr (inc V)) :
      (e_let (e_ret v) e) ~~> (esubst e v)
  | contraction_handle_ret (v : value V) (h : handler V) :
      (e_handle (e_ret v) h) ~~> (esubst (ret_clause h) v)
  | contraction_handle_do
      (h : handler V)
      (l : string)
      (v : value V)
      (ctx : oi_ctx V)
      (e_op : expr (inc (inc V)))
      (He_op : HandlesOp h l e_op)
      (Hctx : ~OiCtxHandlesOp ctx l) :
      (e_handle (oi_plug ctx (e_do l v)) h) ~~>
      (esubst (esubst e_op (vshift v))
              (v_lam (oi_plug (oi_shift ctx) (e_ret (v_var VZ)))))
where "e '~~>' e'" := (contraction e e').

Theorem red_decomposition : forall (V:Set) (e1 e2:expr V),
  e1 --> e2 ->
  (exists (c:io_ctx V) (r1 r2:expr V),
  e1 = io_plug c r1 /\ 
  e2 = io_plug c r2 /\ 
  r1 ~~> r2).
Proof.
  intros. induction H.
  - exists io_ctx_top. exists (e_add (v_nat n1) (v_nat n2)). exists (v_nat (n1 + n2)).
    repeat split; auto. apply contraction_add.
  - exists io_ctx_top. exists (e_app (v_lam e) v). exists (esubst e v).
    repeat split; auto. apply contraction_app.
  - exists io_ctx_top. exists (e_let (e_ret v) e). exists (esubst e v).
    repeat split; auto. apply contraction_let.
  - exists  io_ctx_top. exists (e_handle (e_ret v) h). exists (esubst (ret_clause h) v).
    repeat split; auto. apply contraction_handle_ret.
  - exists io_ctx_top. exists (e_handle (oi_plug ctx (e_do l v)) h).
    exists (esubst (esubst e_op (vshift v))
                   (v_lam (oi_plug (oi_shift ctx) (e_ret (v_var VZ))))).
    repeat split; auto. apply contraction_handle_do; auto.
  - destruct IHred as [c' [r1 [r2 [He1 [He2 Hr]]]]].
    exists (add_io_io c c'). exists r1. exists r2.
    repeat split; subst.
    + rewrite plug_add_io_io. reflexivity.
    + rewrite plug_add_io_io. reflexivity.
    + apply Hr.
Qed.
