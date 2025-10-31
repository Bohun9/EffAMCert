Require Import Lang.Syntax.
Export Lang.Syntax.

Inductive cek_value : Type :=
  | cek_v_nat (n : nat)
  | cek_v_lam {V : Set} (e : expr (inc V)) (Γ : V -> cek_value)
  | cek_v_cont (C : cek_o_ctx) (* Not sure which context is better. *)

with cek_i_ctx : Type := 
  | cek_i_ctx_top
  | cek_i_ctx_let {V : Set}
      (C : cek_i_ctx) (e2 : expr (inc V)) (Γ : V -> cek_value)
  | cek_i_ctx_handle {V : Set}
      (C : cek_i_ctx) (h : handler V) (Γ : V -> cek_value)

with cek_o_ctx : Type := 
  | cek_o_ctx_hole
  | cek_o_ctx_let {V : Set}
      (C : cek_o_ctx) (e2 : expr (inc V)) (Γ : V -> cek_value)
  | cek_o_ctx_handle {V : Set}
      (C : cek_o_ctx) (h : handler V) (Γ : V -> cek_value).

Coercion cek_v_nat : nat >-> cek_value.

Definition env (V : Set) := V -> cek_value.

Inductive cek_state : Type :=
  | cek_expr_mode {V : Set} (e : expr V) (Γ : env V) (C : cek_i_ctx)
  | cek_op_mode (C : cek_i_ctx) (C' : cek_o_ctx) (l : string) (w : cek_value)
  | cek_cont_mode (C : cek_i_ctx) (w : cek_value).

Definition value_to_cek_value {V : Set} (v : value V) (Γ : env V) : cek_value :=
  match v with
  | v_nat n => cek_v_nat n
  | v_var x => Γ x
  | v_lam e => cek_v_lam e Γ
  end.

(* Disambiguate machine notations via a unique superscript letter (ᵉ for CEK). *)

Notation "'ᵉ⟨' e ',' Γ ',' C '⟩ₑ'" := (cek_expr_mode e Γ C) (at level 0).
Notation "'ᵉ⟨' C ',' C' ',' l ',' w '⟩ₒ'" := (cek_op_mode C C' l w) (at level 0).
Notation "'ᵉ⟨' C ',' w '⟩ᶜ'" := (cek_cont_mode C w) (at level 0).
