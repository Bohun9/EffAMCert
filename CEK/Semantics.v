Require Import CEK.Syntax.

Definition value_to_cek_value {V : Set} (Γ : env V) (v : value V) : cek_value V :=
  match v with
  | v_nat n => cek_v_nat n
  | v_var x => Γ x
  | v_lam e => cek_v_lam e Γ
  end.

Reserved Notation "s '==>ₑ' s'" (at level 40).

Inductive cek_red {V V' : Set} : cek_state V -> cek_state V' -> Prop := 
  cek_red_add (v1 v2 : value V) (n1 n2 : nat) (Γ : env V) (C : cek_i_ctx V):
    value_to_cek_value Γ v1 = n1 ->
    value_to_cek_value Γ v2 = n2 ->
    ᵉ⟨e_add v1 v2, Γ, C⟩ₑ ==>ₑ ᵉ⟨C, n1 + n2⟩ᶜ

where "s '==>ₑ' s'" := (cek_red s s').
