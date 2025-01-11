Require Import CAM.Syntax.
Require Import Lang.Semantics.
Require Import Lang.ContextProperties.
Require Import Coq.Relations.Operators_Properties.
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

Lemma plug_cam_red : 
  forall (V:Set) (c1:io_ctx V) (c2:oi_ctx V) (e:expr V),
    ⟨oi_plug c2 e, c1⟩ ==>* ⟨e, add_io_oi c1 c2⟩.
Proof.
  intros. generalize dependent c1. induction c2; intro.
  - simpl. apply rt1n_refl.
  - simpl. eapply rt1n_trans.
    + apply cam_red_let.
    + apply IHc2.
  - simpl. eapply rt1n_trans.
    + apply cam_red_handle.
    + apply IHc2.
Qed.

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

Inductive atomic_expr {V : Set} : expr V -> Prop :=
  | atomic_add (n1 n2 : nat) :
      atomic_expr (e_add (v_nat n1) (v_nat n2))
  | atomic_app (e : expr (inc V)) (v : value V) :
      atomic_expr (e_app (v_lam e) v)
  | atomic_do (l : string) (v : value V) :
      atomic_expr (e_do l v)
.

Lemma plug_atomic_eq_plug_oi :
  forall (V:Set) (c1 c:oi_ctx V) (a e:expr V),
    oi_plug c a = oi_plug c1 e -> atomic_expr a -> 
    (exists (c2:oi_ctx V), c = add_oi_oi c1 c2).
Proof.
  intros. generalize dependent c1. induction c; simpl; intros.
  - destruct c1.
    + simpl in H. exists oi_ctx_hole. simpl. reflexivity.
    + simpl in H. inversion H0.
      -- subst. discriminate.
      -- subst. discriminate.
      -- subst. discriminate.
    + simpl in H. inversion H0.
      -- subst. discriminate.
      -- subst. discriminate.
      -- subst. discriminate.
  - destruct c1.
    + exists (oi_ctx_let c e0). simpl. reflexivity.
    + simpl in H. injection H as Hplug He0.
      subst e0. apply IHc in Hplug.
      destruct Hplug as [c2 Hc2].
      exists c2. simpl. rewrite <- Hc2. reflexivity.
    + simpl in H. discriminate.
  - destruct c1.
    + exists (oi_ctx_handle c h). simpl. reflexivity.
    + simpl in H. discriminate.
    + simpl in H. injection H as Hplug Hh.
      subst h0. apply IHc in Hplug.
      destruct Hplug as [c2 Hc2].
      exists c2. simpl. rewrite <- Hc2. reflexivity.
Qed.

Lemma plug_atomic_eq_plug_io :
  forall (V:Set) (c1 c:io_ctx V) (a e:expr V),
    io_plug c a = io_plug c1 e -> atomic_expr a -> 
    (exists (c2:oi_ctx V), c = add_io_oi c1 c2).
Proof.
  intros.
  pose proof plug_atomic_eq_plug_oi (V) (io_to_oi c1) (io_to_oi c) a e as H1.
  rewrite io_plug_bijection in H.
  rewrite io_plug_bijection in H.
  apply H1 in H. clear H1.
  - destruct H as [c2 Hc2].
    exists c2.
    apply oi_implies_io in Hc2.
    rewrite io_bijection_composition in Hc2.
    rewrite bijection_add_oi_oi in Hc2.
    apply Hc2.
  - assumption.
Qed.

Inductive compound_expr {V : Set} : expr V -> value V -> oi_ctx V -> Prop :=
  | compound_let (v : value V) (e2 : expr (inc V)) :
    compound_expr (e_let v e2) v (oi_ctx_let oi_ctx_hole e2)
  | compound_handle (v : value V) (h : handler V) :
    compound_expr (e_handle v h) v (oi_ctx_handle oi_ctx_hole h)
.

Lemma plug_compound_eq_plug_oi :
  forall (V:Set) (c1 c c_construct:oi_ctx V) (x e:expr V) (v:value V),
    oi_plug c x = oi_plug c1 e -> compound_expr x v c_construct ->
    (c1 = add_oi_oi c c_construct /\ e = v) \/
    (exists (c2:oi_ctx V), c = add_oi_oi c1 c2 /\ e = oi_plug c2 x).
Proof.
  intros. generalize dependent c1. induction c; simpl; intros.
  - inversion H0.
    + subst. destruct c1.
      -- right. exists oi_ctx_hole. simpl. split.
         ++ reflexivity.
         ++ simpl in H1. symmetry in H1. assumption.
      -- left. simpl in H1. injection H1 as H2 H3; subst.
         destruct c1.
         ++ simpl in H2. auto.
         ++ simpl in H2. discriminate.
         ++ simpl in H2. discriminate.
      -- simpl in H1. discriminate.
    + subst. destruct c1.
      -- right. exists oi_ctx_hole. simpl. split.
         ++ reflexivity.
         ++ simpl in H1. symmetry in H1. assumption.
      -- simpl in H1. discriminate.
      -- left. simpl in H1. injection H1 as H2 H3; subst.
         destruct c1.
         ++ simpl in H2. auto.
         ++ simpl in H2. discriminate.
         ++ simpl in H2. discriminate.
  - destruct c1.
    + simpl in H. right. exists (oi_ctx_let c e0).
      simpl. split.
      -- reflexivity.
      -- symmetry in H. assumption.
    + simpl in H. injection H as H1 H2; subst.
      apply IHc in H1. destruct H1 as [[Hc1 He] | [c2 [Hc He]]].
      -- left. rewrite <- Hc1. rewrite He. split; reflexivity.
      -- right. exists c2. simpl. rewrite <- Hc. rewrite He.
         split; reflexivity.
    + simpl in H. discriminate.
  - destruct c1.
    + simpl in H. right. exists (oi_ctx_handle c h).
      simpl. split.
      -- reflexivity.
      -- symmetry in H. assumption.
    + simpl in H. discriminate.
    + simpl in H. injection H as H1 H2; subst.
      apply IHc in H1. destruct H1 as [[Hc1 He] | [c2 [Hc He]]].
      -- left. rewrite <- Hc1. rewrite He. split; reflexivity.
      -- right. exists c2. simpl. rewrite <- Hc. rewrite He.
         split; reflexivity.
Qed.

Lemma plug_compound_eq_plug_io :
  forall (V:Set) (c1 c:io_ctx V) (c_construct:oi_ctx V) (x e:expr V) (v:value V),
    io_plug c x = io_plug c1 e -> compound_expr x v c_construct ->
    (c1 = add_io_oi c c_construct /\ e = v) \/
    (exists (c2:oi_ctx V), c = add_io_oi c1 c2 /\ e = oi_plug c2 x).
Proof.
  intros.
  pose proof plug_compound_eq_plug_oi
    V (io_to_oi c1) (io_to_oi c) c_construct x e v as H1.
  rewrite io_plug_bijection in H.
  rewrite io_plug_bijection in H.
  apply H1 in H; try assumption. clear H1.
  destruct H as [[Hc1 He] | [c2 [Hc2 He]]].
  - left. split.
    + apply oi_implies_io in Hc1.
      rewrite io_bijection_composition in Hc1.
      rewrite bijection_add_oi_oi in Hc1.
      assumption.
    + assumption.
  - right. exists c2. split.
    + apply oi_implies_io in Hc2.
      rewrite io_bijection_composition in Hc2.
      rewrite bijection_add_oi_oi in Hc2.
      assumption.
    + assumption.
Qed.

Lemma plug_handle_do_eq_plug_oi :
  forall (V:Set) (c c1 ch:oi_ctx V) (e:expr V) (h:handler V) (l:string) (v:value V),
      oi_plug c (e_handle (oi_plug ch (e_do l v)) h) = oi_plug c1 e ->
      ((exists (c2:oi_ctx V), c = add_oi_oi c1 c2 /\ e = oi_plug c2 (e_handle (oi_plug ch (e_do l v)) h))
      \/ (exists (ch1 ch2:oi_ctx V), ch = add_oi_oi ch1 ch2 /\ c1 = add_oi_oi c (oi_ctx_handle ch1 h) /\ e = oi_plug ch2 (e_do l v))).
Proof.
  intros. generalize dependent c1. induction c; intros.
  - simpl in H.
    destruct c1.
    + simpl. simpl in H. left.
      exists oi_ctx_hole. split.
      -- reflexivity.
      -- simpl. symmetry in H. assumption.
    + simpl in H. discriminate.
    + simpl in H. simpl.
      injection H as H1 H2.
      subst h0.
      apply plug_atomic_eq_plug_oi in H1 as Hhc2; (try apply atomic_do).
      destruct Hhc2 as [hc2 Hch].
      subst ch. right.
      exists c1. exists hc2.
      repeat split.
      rewrite plug_add_oi_oi in H1.
      apply oi_plug_injection in H1.
      symmetry in H1.
      assumption.
  - simpl in H. simpl.
    destruct c1.
    + left. simpl.
      exists (oi_ctx_let c e0).
      repeat split.
      simpl in H. simpl.
      symmetry in H. assumption.
    + simpl in H.
      injection H as H1 H2.
      subst e1.
      apply IHc in H1. clear IHc.
      destruct H1 as [[c2 [Hc2 He]] | [ch1 [ch2 [Hch [Hc1 He]]]]].
      -- left. exists c2. simpl.
         rewrite <- Hc2.
         repeat split.
         assumption.
      -- right. exists ch1. exists ch2.
         repeat split.
         ++ assumption.
         ++ rewrite <- Hc1. reflexivity.
         ++ assumption.
    + simpl in H.
      discriminate.
  - simpl in H. simpl.
    destruct c1.
    + left. simpl.
      exists (oi_ctx_handle c h0).
      repeat split.
      simpl in H. simpl.
      symmetry in H. assumption.
    + simpl in H.
      discriminate.
    + simpl in H.
      injection H as H1 H2.
      subst h0.
      apply IHc in H1. clear IHc.
      destruct H1 as [[c2 [Hc2 He]] | [ch1 [ch2 [Hch [Hc1 He]]]]].
      -- left. exists c2. simpl.
         rewrite <- Hc2.
         repeat split.
         assumption.
      -- right. exists ch1. exists ch2.
         repeat split.
         ++ assumption.
         ++ rewrite <- Hc1. reflexivity.
         ++ assumption.
Qed.

Lemma plug_handle_do_eq_plug_io :
  forall (V:Set) (c1 c:io_ctx V) (ch:oi_ctx V) (e:expr V) (h:handler V) (l:string) (v:value V),
      io_plug c (e_handle (oi_plug ch (e_do l v)) h) = io_plug c1 e ->
      ((exists (c2:oi_ctx V), c = add_io_oi c1 c2 /\ e = oi_plug c2 (e_handle (oi_plug ch (e_do l v)) h))
      \/ (exists (ch1 ch2:oi_ctx V), ch = add_oi_oi ch1 ch2 /\ c1 = add_io_oi (io_ctx_handle c h) ch1 /\ e = oi_plug ch2 (e_do l v))).
Proof.
  intros.
  pose proof plug_handle_do_eq_plug_oi
    V (io_to_oi c) (io_to_oi c1) ch e h l v as H1.
  rewrite io_plug_bijection in H.
  rewrite io_plug_bijection in H.
  apply H1 in H. clear H1.
  destruct H as [[c2 [Hc2 He]] | [ch1 [ch2 [Hch [Hc1 He]]]]].
  - left. exists c2.
    apply oi_implies_io in Hc2.
    rewrite io_bijection_composition in Hc2.
    rewrite bijection_add_oi_oi in Hc2.
    split.
    + assumption.
    + assumption.
  - right. exists ch1. exists ch2.
    repeat split.
    + assumption.
    + apply oi_implies_io in Hc1.
      rewrite io_bijection_composition in Hc1.
      rewrite bijection_add_oi_oi in Hc1.
      simpl in Hc1. assumption.
    + assumption.
Qed.

Lemma de_morgan2 : forall (P Q : Prop), ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q H. split.
  - intro HP. apply H. left. assumption.
  - intro HQ. apply H. right. assumption.
Qed.

Lemma add_io_oi_op_cam_red_io :
  forall (V:Set) (c1 c2:io_ctx V) (ch:oi_ctx V) (l:string) (v:value V),
    ~IoCtxHandlesOp c2 l ->
    ⟨add_io_io c1 c2, ch, l, v⟩ ==>* ⟨c1, add_io_oi2 c2 ch, l, v⟩.
Proof.
  intros. generalize dependent ch.
  induction c2; intro.
  - simpl. apply rt1n_refl.
  - simpl. eapply rt1n_trans.
    + apply cam_red_op_let.
    + apply IHc2.
      simpl in H. assumption.
  - simpl. simpl in H.
    apply de_morgan2 in H as [H1 H2].
    eapply rt1n_trans.
    + apply cam_red_op_handle1. assumption.
    + apply IHc2. assumption.
Qed.

Lemma add_io_oi_op_cam_red :
  forall (V:Set) (c1:io_ctx V) (c2 ch:oi_ctx V) (l:string) (v:value V),
    ~OiCtxHandlesOp c2 l ->
    ⟨add_io_oi c1 c2, ch, l, v⟩ ==>* ⟨c1, add_oi_oi c2 ch, l, v⟩.
Proof.
  intros.
  pose proof add_io_oi_op_cam_red_io V c1 (oi_to_io c2) ch l v.
  apply not_oi_ctx_handles_op_bijection in H.
  apply H0 in H. clear H0.
  rewrite add_io_io_eq_add_io_oi in H.
  rewrite add_io_oi2_eq_add_oi_oi in H.
  apply H.
Qed.

Theorem lang_implies_cam : forall (V:Set) (e1:expr V) (v:value V),
  e1 -->* v -> forall (c:io_ctx V) (e:expr V), e1 = io_plug c e -> ⟨e, c⟩ ==>* ⟨v, io_ctx_top⟩.
Proof.
  intros V e1 v Hmulti.
  remember (e_ret v) as e2.
  induction Hmulti; intros; subst.
  - assert (Hplug_eq_v: io_plug c e = v -> c = io_ctx_top /\ e = v).
    { generalize dependent e. induction c; intro.
      + simpl. auto.
      + simpl. intro H. apply IHc in H as [_ H2].
        -- discriminate H2.
        -- auto.
      + simpl. intro H. apply IHc in H as [_ H2].
        -- discriminate H2. 
        -- auto.
    }
    symmetry in H.
    apply Hplug_eq_v in H as [Hc He]. subst.
    simpl. apply rt1n_refl.
  - apply red_decomposition in H as [c' [r1 [r2 [Hc' [Hy Hr]]]]].
    subst y.
    inversion Hr; subst.
    + symmetry in Hc'.
      apply plug_atomic_eq_plug_io in Hc' as Hc2; try (apply atomic_add).
      destruct Hc2 as [c2 Hc2]. subst c'.
      rewrite plug_add_io_oi in Hc'.
      apply io_plug_injection in Hc'.
      rewrite <- Hc'.
      apply clos_rt_rt1n.
      eapply rt_trans; (apply clos_rt1n_rt).
      -- apply plug_cam_red.
      -- eapply rt1n_trans.
         ++ apply cam_red_add.
         ++ apply IHHmulti; reflexivity.
    + symmetry in Hc'.
      apply plug_atomic_eq_plug_io in Hc' as Hc2; try (apply atomic_app).
      destruct Hc2 as [c2 Hc2]. subst c'.
      rewrite plug_add_io_oi in Hc'.
      apply io_plug_injection in Hc'.
      rewrite <- Hc'.
      apply clos_rt_rt1n.
      eapply rt_trans; (apply clos_rt1n_rt).
      -- apply plug_cam_red.
      -- eapply rt1n_trans.
         ++ apply cam_red_app.
         ++ apply IHHmulti; reflexivity.
    + symmetry in Hc'.
      apply plug_compound_eq_plug_io with
        (c_construct := oi_ctx_let oi_ctx_hole e0) (v := v0) in Hc' as Hc_shape;
      try apply compound_let.
      destruct Hc_shape as [[Hc He] | [c2 [Hc2 He]]].
      -- subst. simpl.
         eapply rt1n_trans.
         ++ apply cam_red_ret_let.
         ++ apply IHHmulti; reflexivity.
      -- subst. 
         apply clos_rt_rt1n.
         eapply rt_trans; (apply clos_rt1n_rt).
         ++ apply plug_cam_red.
         ++ eapply rt1n_trans.
            ** apply cam_red_let.
            ** eapply rt1n_trans.
               *** apply cam_red_ret_let.
               *** apply IHHmulti; reflexivity.
    + symmetry in Hc'.
      apply plug_compound_eq_plug_io with
        (c_construct := oi_ctx_handle oi_ctx_hole h) (v := v0) in Hc' as Hc_shape;
      try apply compound_handle.
      destruct Hc_shape as [[Hc He] | [c2 [Hc2 He]]].
      -- subst. simpl.
         eapply rt1n_trans.
         ++ apply cam_red_ret_handle.
         ++ apply IHHmulti; reflexivity.
      -- subst. 
         apply clos_rt_rt1n.
         eapply rt_trans; (apply clos_rt1n_rt).
         ++ apply plug_cam_red.
         ++ eapply rt1n_trans.
            ** apply cam_red_handle.
            ** eapply rt1n_trans.
               *** apply cam_red_ret_handle.
               *** apply IHHmulti; reflexivity.
    + symmetry in Hc'.
      apply plug_handle_do_eq_plug_io in Hc' as Hc_shape.
      destruct Hc_shape as [[c2 [Hc2 He]] | [ch1 [ch2 [Hhc [Hc He]]]]].
      -- subst.
         apply clos_rt_rt1n.
         eapply rt_trans; (apply clos_rt1n_rt).
         ++ apply plug_cam_red.
         ++ eapply rt1n_trans.
            ** apply cam_red_handle.
            ** apply clos_rt_rt1n.
               eapply rt_trans; (apply clos_rt1n_rt).
               *** apply plug_cam_red.
               *** eapply rt1n_trans.
                   **** apply cam_red_do.
                   **** apply clos_rt_rt1n.
                        eapply rt_trans; (apply clos_rt1n_rt).
                        ***** apply add_io_oi_op_cam_red.
                              assumption.
                        ***** rewrite add_oi_oi_hole_r.
                              eapply rt1n_trans.
                              ****** eapply cam_red_op_handle2.
                                     apply He_op.
                              ****** apply IHHmulti; reflexivity.
      -- subst.
         apply clos_rt_rt1n.
         eapply rt_trans; (apply clos_rt1n_rt).
         ++ apply plug_cam_red.
         ++ eapply rt1n_trans.
            ** apply cam_red_do.
            ** apply not_oi_ctx_handles_op_add in Hctx as [Hch1 Hch2].
               apply clos_rt_rt1n.
               eapply rt_trans; (apply clos_rt1n_rt).
               *** apply add_io_oi_op_cam_red.
                   assumption.
               *** apply clos_rt_rt1n.
                   eapply rt_trans; (apply clos_rt1n_rt).
                   **** apply add_io_oi_op_cam_red.
                        assumption.
                   **** rewrite add_oi_oi_hole_r.
                        eapply rt1n_trans.
                        ***** apply cam_red_op_handle2.
                              apply He_op.
                        ***** apply IHHmulti; reflexivity.
Qed.

Theorem lang_equiv_cam : forall (V:Set) (e:expr V) (v:value V),
  e -->* v <-> ⟨e, io_ctx_top⟩ ==>* ⟨v, io_ctx_top⟩.
Proof.
  intros V e v. split; intro.
  - apply lang_implies_cam with (e1 := e).
    + assumption.
    + simpl. reflexivity.
  - apply cam_implies_lang in H as [H1 _].
    apply H1 with (c := io_ctx_top).
    reflexivity.
Qed.
