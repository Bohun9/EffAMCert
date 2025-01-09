Require Import CAM.Syntax.
Require Import Lang.Semantics.

Reserved Notation "e 'e==>e' e'" (at level 40).
Reserved Notation "e 'e==>o' e'" (at level 40).
Reserved Notation "e 'o==>o' e'" (at level 40).
Reserved Notation "e 'o==>e' e'" (at level 40).

Inductive cam_red_expr_expr {V : Set} : cam_expr_mode V -> cam_expr_mode V -> Prop :=
  | cam_red_add (n1 n2 : nat) (ctx : io_ctx V) :
      ⟨e_add (v_nat n1) (v_nat n2), ctx⟩ e==>e ⟨e_ret (v_nat (n1 + n2)), ctx⟩
  | cam_red_app (e : expr (inc V)) (v : value V) (ctx : io_ctx V) :
      ⟨e_app (v_lam e) v, ctx⟩ e==>e ⟨esubst e v, ctx⟩
  | cam_red_let (e1 : expr V) (e2 : expr (inc V)) (ctx : io_ctx V) :
      ⟨e_let e1 e2, ctx⟩ e==>e ⟨e1, io_ctx_let ctx e2⟩
  | cam_red_handle (e : expr V) (h : handler V) (ctx : io_ctx V) :
      ⟨e_handle e h, ctx⟩ e==>e ⟨e, io_ctx_handle ctx h⟩
  | cam_red_ret_let (v : value V) (e2 : expr (inc V)) (ctx : io_ctx V) :
      ⟨e_ret v, io_ctx_let ctx e2⟩ e==>e ⟨esubst e2 v, ctx⟩
  | cam_red_ret_handle (v : value V) (h : handler V) (ctx : io_ctx V) :
      ⟨e_ret v, io_ctx_handle ctx h⟩ e==>e ⟨esubst (ret_clause h) v, ctx⟩

with cam_red_expr_op {V : Set} : cam_expr_mode V -> cam_op_mode V -> Prop :=
  | cam_red_do (l : string) (v : value V) (ctx : io_ctx V) :
      ⟨e_do l v, ctx⟩ e==>o ⟨ctx, oi_ctx_hole, l, v⟩

with cam_red_op_op {V : Set} : cam_op_mode V -> cam_op_mode V -> Prop :=
  | cam_red_op_let (ctx : io_ctx V) (h_ctx : oi_ctx V) (l : string)
      (v : value V) (e2 : expr (inc V)) :
      ⟨io_ctx_let ctx e2, h_ctx, l, v⟩ o==>o ⟨ctx, oi_ctx_let h_ctx e2, l, v⟩
  | cam_red_op_handle1 (ctx : io_ctx V) (h_ctx : oi_ctx V) (l : string)
      (v : value V) (h : handler V) (Hnot_handle : (~exists e_op, HandlesOp h l e_op)) :
      ⟨io_ctx_handle ctx h, h_ctx, l, v⟩ o==>o ⟨ctx, oi_ctx_handle h_ctx h, l, v⟩

with cam_red_op_expr {V : Set} : cam_op_mode V -> cam_expr_mode V -> Prop :=
  | cam_red_op_handle2 (ctx : io_ctx V) (h_ctx : oi_ctx V) (l : string)
      (v : value V) (h : handler V) (e_op : expr (inc (inc V)))
      (Hhandle : HandlesOp h l e_op) :
      ⟨io_ctx_handle ctx h, h_ctx, l, v⟩ o==>e 
      ⟨(esubst (esubst e_op (vshift v))
               (v_lam (io_plug (cshift ctx) (e_ret (v_var VZ))))), ctx⟩

where "e 'e==>e' e'" := (cam_red_expr_expr e e')
  and "e 'e==>o' e'" := (cam_red_expr_op e e')
  and "e 'o==>o' e'" := (cam_red_op_op e e')
  and "e 'o==>e' e'" := (cam_red_op_expr e e').

Reserved Notation "e 'e==>*e' e'" (at level 40).
Reserved Notation "o 'o==>*e' e'" (at level 40).

Inductive cam_multi_red_expr_expr {V : Set} : cam_expr_mode V -> cam_expr_mode V -> Prop :=
  | cam_multi_refl (k : cam_expr_mode V) : k e==>*e k
  | cam_multi_expr_expr (k1 k2 k3 : cam_expr_mode V)
      (Hred : k1 e==>e k2) (Hmulti : k2 e==>*e k3) :
      k1 e==>*e k3
  | cam_multi_expr_op (k1 k3 : cam_expr_mode V) (k2 : cam_op_mode V)
      (Hred : k1 e==>o k2) (Hmulti : k2 o==>*e k3) :
      k1 e==>*e k3

with cam_multi_red_op_expr {V : Set} : cam_op_mode V -> cam_expr_mode V -> Prop :=
  | cam_multi_op_expr (k1 : cam_op_mode V) (k2 k3 : cam_expr_mode V)
      (Hred : k1 o==>e k2) (Hmulti : k2 e==>*e k3) :
      k1 o==>*e k3
  | cam_multi_op_op (k1 k2 : cam_op_mode V) (k3 : cam_expr_mode V)
      (Hred : k1 o==>o k2) (Hmulti : k2 o==>*e k3) :
      k1 o==>*e k3

where "e 'e==>*e' e'" := (cam_multi_red_expr_expr e e')
  and "e 'o==>*e' e'" := (cam_multi_red_op_expr e e').

Scheme cam_multi_expr_ind := Minimality for cam_multi_red_expr_expr Sort Prop
  with cam_multi_op_ind := Minimality for cam_multi_red_op_expr Sort Prop.

Check cam_multi_red_expr_expr_ind.
Check cam_multi_expr_ind.

Theorem cam_implies_lang : forall (V:Set) (e:expr V) (v:value V)
  (ctx:io_ctx V),
  ⟨e, ctx⟩ e==>*e ⟨v, io_ctx_top⟩ -> io_plug ctx e -->* v.
Proof.
  intros. remember ⟨e, ctx⟩ as k1. remember ⟨v, io_ctx_top⟩ as k2.
  apply cam_multi_expr_ind with (P0 := fun x y => True).
  (* apply cam_multi_expr_ind with (P0 := fun x y => True) (c := k1) (c0 := k2). *)


Theorem lang_equiv_cam : forall (V:Set) (e:expr V) (v:value V),
  e -->* v <-> ⟨e, io_ctx_top⟩ e==>*e ⟨v, io_ctx_top⟩.
Admitted.
