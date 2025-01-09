Require Import Lang.Syntax.
Export Lang.Syntax.

(* Context Abstract Machine *)

Inductive cam_expr_mode (V : Set) : Set :=
  cam_expr_state : expr V -> io_ctx V -> cam_expr_mode V

with cam_op_mode (V : Set) : Set :=
  cam_op_state : io_ctx V -> oi_ctx V -> string -> value V -> cam_op_mode V
.

Arguments cam_expr_state {V}.
Arguments cam_op_state {V}.

Notation "'⟨' e ',' c '⟩'" := (cam_expr_state e c) (at level 0).
Notation "'⟨' c ',' c' ',' l ',' v '⟩'" := (cam_op_state c c' l v) (at level 0).

Check Empty_set.

Check (⟨e_ret (v_nat 42), io_ctx_top⟩).
Check (⟨io_ctx_top, oi_ctx_hole, "abc", v_nat 2⟩).
