Require Import Lang.Syntax.

Reserved Notation "e '-->' e'" (at level 40).

Inductive step {V : Set} : expr V -> expr V -> Prop :=
  | ST_Add (n1 n2 : nat) :
      (e_add (v_nat n1) (v_nat n2)) --> (e_ret (v_nat (n1 + n2)))
  | ST_App (e : expr (inc V)) (v : value V) :
      (e_app (v_lam e) v) --> (esubst e v)
  | ST_Let (v : value V) (e : expr (inc V)) :
      (e_let (e_ret v) e) --> (esubst e v)
  | ST_HandleRet (v : value V) (h : handler V) :
      (e_handle (e_ret v) h) --> (esubst (ret_clause h) v)
  | ST_HandleDo
      (h : handler V)
      (l : string)
      (v : value V)
      (ctx : io_ctx V)
      (e_op : expr (inc (inc V)))
      (H_e_op : HandlesOp h l e_op)
      (H_ctx : ~IoCtxHandlesOp ctx l) :
      (e_handle (io_plug ctx (e_do l v)) h) -->
      (esubst (esubst e_op (vshift v))
              (v_lam (io_plug (cshift ctx) (e_ret (v_var VZ)))))
  | ST_Context
      (c : io_ctx V)
      (e1 e2 : expr V)
      (Hstep : e1 --> e2) :
      io_plug c e1 --> io_plug c e2
where "e '-->' e'" := (step e e').
