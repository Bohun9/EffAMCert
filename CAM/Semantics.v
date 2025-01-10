Require Import CAM.Syntax.
Require Import Lang.Semantics.
Require Import Coq.Relations.Relation_Operators.

Reserved Notation "k '==>' k'" (at level 40).

Inductive cam_red {V : Set} : cam_state V -> cam_state V -> Prop :=
  | cam_red_add (n1 n2 : nat) (ctx : io_ctx V) :
      ⟨e_add (v_nat n1) (v_nat n2), ctx⟩ ==> ⟨e_ret (v_nat (n1 + n2)), ctx⟩
  | cam_red_app (e : expr (inc V)) (v : value V) (ctx : io_ctx V) :
      ⟨e_app (v_lam e) v, ctx⟩ ==> ⟨esubst e v, ctx⟩
  | cam_red_let (e1 : expr V) (e2 : expr (inc V)) (ctx : io_ctx V) :
      ⟨e_let e1 e2, ctx⟩ ==> ⟨e1, io_ctx_let ctx e2⟩
  | cam_red_handle (e : expr V) (h : handler V) (ctx : io_ctx V) :
      ⟨e_handle e h, ctx⟩ ==> ⟨e, io_ctx_handle ctx h⟩
  | cam_red_ret_let (v : value V) (e2 : expr (inc V)) (ctx : io_ctx V) :
      ⟨e_ret v, io_ctx_let ctx e2⟩ ==> ⟨esubst e2 v, ctx⟩
  | cam_red_ret_handle (v : value V) (h : handler V) (ctx : io_ctx V) :
      ⟨e_ret v, io_ctx_handle ctx h⟩ ==> ⟨esubst (ret_clause h) v, ctx⟩
  | cam_red_do (l : string) (v : value V) (ctx : io_ctx V) :
      ⟨e_do l v, ctx⟩ ==> ⟨ctx, oi_ctx_hole, l, v⟩
  | cam_red_op_let (ctx : io_ctx V) (h_ctx : oi_ctx V) (l : string)
      (v : value V) (e2 : expr (inc V)) :
      ⟨io_ctx_let ctx e2, h_ctx, l, v⟩ ==> ⟨ctx, oi_ctx_let h_ctx e2, l, v⟩
  | cam_red_op_handle1 (ctx : io_ctx V) (h_ctx : oi_ctx V) (l : string)
      (v : value V) (h : handler V) (Hnot_handle : (~exists e_op, HandlesOp h l e_op)) :
      ⟨io_ctx_handle ctx h, h_ctx, l, v⟩ ==> ⟨ctx, oi_ctx_handle h_ctx h, l, v⟩
  | cam_red_op_handle2 (ctx : io_ctx V) (h_ctx : oi_ctx V) (l : string)
      (v : value V) (h : handler V) (e_op : expr (inc (inc V)))
      (Hhandle : HandlesOp h l e_op) :
      ⟨io_ctx_handle ctx h, h_ctx, l, v⟩ ==>
      ⟨(esubst (esubst e_op (vshift v))
               (v_lam (oi_plug (oi_shift h_ctx) (e_ret (v_var VZ))))), ctx⟩

where "k '==>' k'" := (cam_red k k').

Notation "k '==>*' k'" := (clos_refl_trans_1n _ cam_red k k') (at level 40).

Theorem cam_implies_lang : forall (V:Set) (k:cam_state V) (v:value V),
  k ==>* ⟨v, io_ctx_top⟩ ->
  (forall (e:expr V) (c:io_ctx V), k = ⟨e, c⟩ -> io_plug c e -->* v) /\
  (forall (c:io_ctx V) (hc:oi_ctx V) (l:string) (v':value V),
    k = ⟨c, hc, l, v'⟩ -> ~(OiCtxHandlesOp hc l) ->
    io_plug c (oi_plug hc (e_do l v')) -->* v)
.
Proof.
  intros.
  remember ⟨v, io_ctx_top⟩ as k'. induction H; subst.
  - split; intros.
    + injection H as H1 H2; subst. simpl. apply rt1n_refl.
    + discriminate H.
  - inversion H; subst; split; intros; try discriminate;
    injection H1 as H3 H4; subst;
    specialize (IHclos_refl_trans_1n eq_refl); (* remove trivial prefix from the IH *)
    destruct IHclos_refl_trans_1n as [IH1 IH2]. (* IH1 expr mode, IH2 op mode *)
    (* cam_red_add *)
    + eapply rt1n_trans.
      -- apply red_context. apply red_add.
      -- apply IH1. reflexivity.
    (* cam_red_app *)
    + eapply rt1n_trans.
      -- apply red_context. apply red_app.
      -- apply IH1; reflexivity.
    (* cam_red_let *)
    + assert (Hlet_ctx : io_plug c (e_let e1 e2) = io_plug (io_ctx_let c e2) e1).
      {  reflexivity. }
      rewrite Hlet_ctx.
      apply IH1; reflexivity.
    (* cam_red_handle *)
    + assert (Hhandle_ctx : io_plug c (e_handle e h) = io_plug (io_ctx_handle c h) e).
      { reflexivity. }
      rewrite Hhandle_ctx.
      apply IH1; reflexivity.
    (* cam_red_ret_let *)
    + eapply rt1n_trans.
      -- simpl. apply red_context. apply red_let.
      -- apply IH1; reflexivity.
    (* cam_red_ret_handle *)
    + eapply rt1n_trans.
      -- simpl. apply red_context. apply red_handle_ret.
      -- apply IH1; reflexivity.
    (* cam_red_do *)
    + assert (Hdo_ctx : io_plug c (e_do l v0) = io_plug c (oi_plug oi_ctx_hole (e_do l v0))).
      { reflexivity. }
      rewrite Hdo_ctx.
      apply IH2; try reflexivity.
      simpl. auto.
    (* cam_red_op_let *)
    + assert (Hlet_ctx :
        io_plug (io_ctx_let ctx e2) (oi_plug hc (e_do l0 v')) =
        io_plug ctx (oi_plug (oi_ctx_let hc e2) (e_do l0 v'))).
      { reflexivity. }
      rewrite Hlet_ctx.
      apply IH2; try reflexivity.
      simpl. assumption.
    (* cam_red_op_handle1 *)
    + assert (Hhandle_ctx :
        io_plug (io_ctx_handle ctx h) (oi_plug hc (e_do l0 v')) =
        io_plug ctx (oi_plug (oi_ctx_handle hc h) (e_do l0 v'))).
      { reflexivity. }
      rewrite Hhandle_ctx.
      apply IH2; try reflexivity.
      simpl. intros [Habsurd | Habsurd]; auto.
    (* cam_red_op_handle2 *)
    + eapply rt1n_trans.
      -- simpl. apply red_context. apply red_handle_do; eauto.
      -- apply IH1. reflexivity.
Qed.

Theorem lang_equiv_cam : forall (V:Set) (e:expr V) (v:value V),
  e -->* v <-> ⟨e, io_ctx_top⟩ ==>* ⟨v, io_ctx_top⟩.
Admitted.
