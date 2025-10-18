Require Import Lang.Syntax.
Export Lang.Syntax.

Inductive cek_value (V : Set) : Set :=
  | cek_v_nat (n : nat)
  | cek_v_lam (e : expr (inc V)) (Γ : V -> cek_value V)
  | cek_v_cont (C : cek_i_ctx V) (* Not sure which context is better. *)

with cek_i_ctx (V : Set) : Set := 
  | cek_i_ctx_top
  | cek_i_ctx_let (C : cek_i_ctx V) (e2 : expr (inc V)) (Γ : V -> cek_value V)
  | cek_i_ctx_handle (C : cek_i_ctx V) (h : handler V) (Γ : V -> cek_value V)

with cek_o_ctx (V : Set) : Set := 
  | cek_o_ctx_hole
  | cek_o_ctx_let (C : cek_o_ctx V) (e2 : expr (inc V)) (Γ : V -> cek_value V)
  | cek_o_ctx_handle (C : cek_o_ctx V) (h : handler V) (Γ : V -> cek_value V).

Arguments cek_v_nat {V}.
Arguments cek_v_lam {V}.
Arguments cek_v_cont {V}.

Coercion cek_v_nat : nat >-> cek_value.

Definition env (V : Set) := V -> cek_value V.

Inductive cek_state (V : Set) : Set :=
  | cek_expr_mode (e : expr V) (Γ : env V) (C : cek_i_ctx V)
  | cek_op_mode (C : cek_i_ctx V) (C' : cek_o_ctx V) (l : string) (w : cek_value V)
  | cek_cont_mode (C : cek_i_ctx V) (w : cek_value V).

Arguments cek_expr_mode {V}.
Arguments cek_op_mode {V}.
Arguments cek_cont_mode {V}.

(* Disambiguate machine notations via a unique superscript letter (ᵉ for CEK). *)

Notation "'ᵉ⟨' e ',' Γ ',' C '⟩ₑ'" := (cek_expr_mode e Γ C) (at level 0).
Notation "'ᵉ⟨' C ',' C' ',' l ',' w '⟩ₒ'" := (cek_op_mode C C' l w) (at level 0).
Notation "'ᵉ⟨' C ',' w '⟩ᶜ'" := (cek_cont_mode C w) (at level 0).
