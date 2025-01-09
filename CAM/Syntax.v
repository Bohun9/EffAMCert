Require Import Lang.Syntax.
Export Lang.Syntax.

(* Context Abstract Machine *)

Inductive cam_state (V : Set) : Set :=
  | cam_expr_mode : expr V -> io_ctx V -> cam_state V
  | cam_op_mode : io_ctx V -> oi_ctx V -> string -> value V -> cam_state V
.

Arguments cam_expr_mode {V}.
Arguments cam_op_mode {V}.

Notation "'⟨' e ',' c '⟩'" := (cam_expr_mode e c) (at level 0).
Notation "'⟨' c ',' c' ',' l ',' v '⟩'" := (cam_op_mode c c' l v) (at level 0).

Check Empty_set.

Check (⟨e_ret (v_nat 42), io_ctx_top⟩).
Check (⟨io_ctx_top, oi_ctx_hole, "abc", v_nat 2⟩).
