Require Import CEK.Syntax.

Fixpoint add_i (C1 : cek_i_ctx) (C2 : cek_o_ctx) : cek_i_ctx :=
  match C2 with
  | cek_o_ctx_hole => C1
  | cek_o_ctx_let C e2 Γ => add_i (cek_i_ctx_let C1 e2 Γ) C
  | cek_o_ctx_handle C h Γ => add_i (cek_i_ctx_handle C1 h Γ) C
  end.

Notation "C1 '+ᵢ' C2" := (add_i C1 C2) (at level 40).
