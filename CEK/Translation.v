Require Import CEK.Syntax.

(* It doesn't work. *)
(* Fixpoint cyclic_env (x : inc ∅ ) : cek_value := *)
(*   match x with *)
(*   | VZ => cek_v_lam 42 (fun z => cyclic_env z) *)
(*   | VS y => match y with end *)
(*   end. *)

Fixpoint trans_expr {V : Set} (e : expr V) (Γ : env V) : expr ∅ :=
  ebind (trans_env Γ) e

with trans_expr_inc {V : Set} (e : expr (inc V)) (Γ : env V) : expr (inc ∅ ) :=
  ebind (liftS (trans_env Γ)) e

with trans_handler {V : Set} (h : handler V) (Γ : env V) : handler ∅ :=
  hbind (trans_env Γ) h

with trans_env {V : Set} (Γ : env V) (x : V) : value ∅ :=
  trans_value (Γ x)

with trans_value (w : cek_value) : value ∅ :=
  match w with
  | cek_v_nat n => v_nat n
  | cek_v_lam e Γ => v_lam (trans_expr_inc e Γ)
  | cek_v_cont C => v_lam ((o_ctx_shift (trans_ctx_o C))[v_var VZ]ₒ)
  end

with trans_ctx_o (C : cek_o_ctx) : o_ctx ∅ :=
  match C with
  | cek_o_ctx_hole => o_ctx_hole
  | cek_o_ctx_let C' e2 Γ => o_ctx_let (trans_ctx_o C') (trans_expr_inc e2 Γ)
  | cek_o_ctx_handle C' h Γ => o_ctx_handle (trans_ctx_o C') (trans_handler h Γ)
  end.
