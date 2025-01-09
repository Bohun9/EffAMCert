Require Import CAM.Syntax.
Require Import Lang.Semantics.
Require Import Coq.Relations.Relation_Operators.

Reserved Notation "k '==>' k'" (at level 40).

Inductive cam_red {V : Set} : cam_state V -> cam_state V -> Prop :=
  | cam_red_add (n1 n2 : nat) (ctx : io_ctx V) :
      ⟨e_add (v_nat n1) (v_nat n2), ctx⟩ ==> ⟨e_ret (v_nat (n1 + n2)), ctx⟩
  | cam_red_app (e : expr (inc V)) (v : value V) (ctx : io_ctx V) :
      ⟨e_app (v_lam e) v, ctx⟩ ==> ⟨esubst e v, ctx⟩
  | cam_red_let (e1 : expr V) (e2 : expr (inc V)) (ctx : io_ctx V) :
      ⟨e_let e1 e2, ctx⟩ ==> ⟨e1, io_ctx_let ctx e2⟩
  | cam_red_handle (e : expr V) (h : handler V) (ctx : io_ctx V) :
      ⟨e_handle e h, ctx⟩ ==> ⟨e, io_ctx_handle ctx h⟩
  | cam_red_ret_let (v : value V) (e2 : expr (inc V)) (ctx : io_ctx V) :
      ⟨e_ret v, io_ctx_let ctx e2⟩ ==> ⟨esubst e2 v, ctx⟩
  | cam_red_ret_handle (v : value V) (h : handler V) (ctx : io_ctx V) :
      ⟨e_ret v, io_ctx_handle ctx h⟩ ==> ⟨esubst (ret_clause h) v, ctx⟩
  | cam_red_do (l : string) (v : value V) (ctx : io_ctx V) :
      ⟨e_do l v, ctx⟩ ==> ⟨ctx, oi_ctx_hole, l, v⟩
  | cam_red_op_let (ctx : io_ctx V) (h_ctx : oi_ctx V) (l : string)
      (v : value V) (e2 : expr (inc V)) :
      ⟨io_ctx_let ctx e2, h_ctx, l, v⟩ ==> ⟨ctx, oi_ctx_let h_ctx e2, l, v⟩
  | cam_red_op_handle1 (ctx : io_ctx V) (h_ctx : oi_ctx V) (l : string)
      (v : value V) (h : handler V) (Hnot_handle : (~exists e_op, HandlesOp h l e_op)) :
      ⟨io_ctx_handle ctx h, h_ctx, l, v⟩ ==> ⟨ctx, oi_ctx_handle h_ctx h, l, v⟩
  | cam_red_op_handle2 (ctx : io_ctx V) (h_ctx : oi_ctx V) (l : string)
      (v : value V) (h : handler V) (e_op : expr (inc (inc V)))
      (Hhandle : HandlesOp h l e_op) :
      ⟨io_ctx_handle ctx h, h_ctx, l, v⟩ ==>
      ⟨(esubst (esubst e_op (vshift v))
               (v_lam (io_plug (cshift ctx) (e_ret (v_var VZ))))), ctx⟩

where "k '==>' k'" := (cam_red k k').

Notation "k '==>*' k'" := (clos_refl_trans_1n _ cam_red k k') (at level 40).

Theorem cam_implies_lang : forall (V:Set) (k:cam_state V) (e:expr V) (v v':value V)
  (c:io_ctx V) (hc:oi_ctx V) (l:string),
  k ==>* ⟨v, io_ctx_top⟩ ->
  (k = ⟨e, c⟩ -> io_plug c e -->* v) /\
  (k = ⟨c, hc, l, v'⟩ -> ~(OiCtxHandlesOp hc l) -> io_plug c (oi_plug hc (e_do l v)) -->* v)
.
Proof.
  intros.
  generalize dependent e.
  generalize dependent c.
  generalize dependent hc.
  generalize dependent l.
  generalize dependent v'.
  remember ⟨v, io_ctx_top⟩ as k'. induction H; subst.
  - intros. split; intro.
    + injection H as H1 H2; subst. simpl. apply rt1n_refl.
    + discriminate H.
  - admit.
Admitted.

Theorem lang_equiv_cam : forall (V:Set) (e:expr V) (v:value V),
  e -->* v <-> ⟨e, io_ctx_top⟩ ==>* ⟨v, io_ctx_top⟩.
Admitted.
