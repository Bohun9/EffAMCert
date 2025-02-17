Require Import Lang.Syntax.
Export Lang.Syntax.

(* Context Abstract Machine *)

Inductive cam_state (V : Set) : Set :=
  | cam_expr_mode (e : expr V) (C : i_ctx V)
  | cam_op_mode (C : i_ctx V) (C' : o_ctx V) (l : string) (v : value V).

Arguments cam_expr_mode {V}.
Arguments cam_op_mode {V}.

Notation "'⟨' e ',' C '⟩ₑ'" := (cam_expr_mode e C) (at level 0).
Notation "'⟨' C ',' C' ',' l ',' v '⟩ₒ'" := (cam_op_mode C C' l v) (at level 0).

Check (⟨e_val (v_nat 42), i_ctx_top⟩ₑ).
Check (⟨i_ctx_top, o_ctx_hole, "abc", v_nat 2⟩ₒ).
