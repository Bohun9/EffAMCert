Require Import CEK.Syntax.
Require Import CEK.ContextProperties.

Reserved Notation "s '==>ₑ' s'" (at level 40).

Inductive cek_red : cek_state -> cek_state -> Prop := 
  | cek_red_add
      (V : Set) (v1 v2 : value V) (n1 n2 : nat) (Γ : env V) (C : cek_i_ctx) :
      value_to_cek_value v1 Γ = n1 ->
      value_to_cek_value v2 Γ = n2 ->
      ᵉ⟨e_add v1 v2, Γ, C⟩ₑ ==>ₑ
      ᵉ⟨C, n1 + n2⟩ᶜ
  | cek_red_app1
      (V V' : Set) (v1 v2 : value V) (e : expr (inc V'))
      (Γ : env V) (Γ' : env V') (C : cek_i_ctx) :
      value_to_cek_value v1 Γ = cek_v_lam e Γ' ->
      ᵉ⟨e_app v1 v2, Γ, C⟩ₑ ==>ₑ
      ᵉ⟨e, Γ'[↦ value_to_cek_value v2 Γ], C⟩ₑ
  | cek_red_app2
      (V : Set) (v1 v2 : value V)
      (Γ : env V) (C : cek_i_ctx) (C' : cek_o_ctx) :
      value_to_cek_value v1 Γ = cek_v_cont C' ->
      ᵉ⟨e_app v1 v2, Γ, C⟩ₑ ==>ₑ
      ᵉ⟨C +ᵢ C', value_to_cek_value v2 Γ⟩ᶜ
  | cek_red_let 
      (V : Set) (e1 : expr V) (e2 : expr (inc V)) (Γ : env V) (C : cek_i_ctx) :
      ᵉ⟨e_let e1 e2, Γ, C⟩ₑ ==>ₑ
      ᵉ⟨e1, Γ, cek_i_ctx_let C e2 Γ⟩ₑ
  | cek_red_handle 
      (V : Set) (e : expr V) (h : handler V) (Γ : env V) (C : cek_i_ctx) :
      ᵉ⟨e_handle e h, Γ, C⟩ₑ ==>ₑ
      ᵉ⟨e, Γ, cek_i_ctx_handle C h Γ⟩ₑ
  | cek_red_ret
      (V : Set) (v : value V) (Γ : env V) (C : cek_i_ctx) :
      ᵉ⟨v, Γ, C⟩ₑ ==>ₑ
      ᵉ⟨C, value_to_cek_value v Γ⟩ᶜ
  | cek_red_cont_let 
      (V : Set) (w : cek_value) (e : expr (inc V))
      (Γ : env V) (C : cek_i_ctx) :
      ᵉ⟨cek_i_ctx_let C e Γ, w⟩ᶜ ==>ₑ
      ᵉ⟨e, Γ[↦ w], C⟩ₑ
  | cek_red_cont_handle 
      (V : Set) (w : cek_value) (h : handler V)
      (Γ : env V) (C : cek_i_ctx) :
      ᵉ⟨cek_i_ctx_handle C h Γ, w⟩ᶜ ==>ₑ
      ᵉ⟨ret_clause h, Γ[↦ w], C⟩ₑ
  | cek_red_do
      (V : Set) (l : string) (v : value V) (Γ : env V) (C : cek_i_ctx) :
      ᵉ⟨e_do l v, Γ, C⟩ₑ ==>ₑ
      ᵉ⟨C, cek_o_ctx_hole, l, value_to_cek_value v Γ⟩ₒ
  | cek_red_op_let
      (V : Set) (l : string) (w : cek_value) (e2 : expr (inc V))
      (Γ : env V) (C : cek_i_ctx) (C' : cek_o_ctx) :
      ᵉ⟨cek_i_ctx_let C e2 Γ, C', l, w⟩ₒ ==>ₑ
      ᵉ⟨C, cek_o_ctx_let C' e2 Γ, l, w⟩ₒ
  | cek_red_op_handle1  
      (V : Set) (l : string) (w : cek_value) (h : handler V)
      (Γ : env V) (C : cek_i_ctx) (C' : cek_o_ctx)
      (HNotHandlesOp : ~HandlesOp h l) :
      ᵉ⟨cek_i_ctx_handle C h Γ, C', l, w⟩ₒ ==>ₑ
      ᵉ⟨C, cek_o_ctx_handle C' h Γ, l, w⟩ₒ
  | cek_red_op_handle2  
      (V : Set) (l : string) (w : cek_value) (h : handler V)
      (e_op : expr (inc (inc V))) (Γ : env V) (C : cek_i_ctx) (C' : cek_o_ctx)
      (HHandlesOp : HandlesOpWith h l e_op) :
      ᵉ⟨cek_i_ctx_handle C h Γ, C', l, w⟩ₒ ==>ₑ
      ᵉ⟨e_op, Γ[↦ w][↦ cek_v_cont C'], C⟩ₑ

where "s '==>ₑ' s'" := (cek_red s s').
