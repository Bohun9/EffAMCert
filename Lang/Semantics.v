Require Import Lang.Syntax.
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
      (ctx : io_ctx V)
      (e_op : expr (inc (inc V)))
      (He_op : HandlesOp h l e_op)
      (Hctx : ~IoCtxHandlesOp ctx l) :
      (e_handle (io_plug ctx (e_do l v)) h) -->
      (esubst (esubst e_op (vshift v))
              (v_lam (io_plug (cshift ctx) (e_ret (v_var VZ)))))
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
