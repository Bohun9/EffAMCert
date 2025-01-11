Require Import Lang.Syntax.

Fixpoint add_io_io {V : Set} (c1 c2 : io_ctx V) : io_ctx V :=
  match c2 with
  | io_ctx_top => c1
  | io_ctx_let c e2 => io_ctx_let (add_io_io c1 c) e2
  | io_ctx_handle c h => io_ctx_handle (add_io_io c1 c) h
  end.

Theorem plug_add_io_io : 
  forall (V:Set) (c1 c2:io_ctx V) (e:expr V),
    io_plug (add_io_io c1 c2) e = io_plug c1 (io_plug c2 e).
Proof.
  intros. generalize dependent e. induction c2; intro.
  - simpl. reflexivity.
  - simpl. rewrite IHc2. reflexivity.
  - simpl. rewrite IHc2. reflexivity.
Qed.

Fixpoint add_oi_oi {V : Set} (c1 c2 : oi_ctx V) : oi_ctx V :=
  match c1 with
  | oi_ctx_hole => c2
  | oi_ctx_let c e2 => oi_ctx_let (add_oi_oi c c2) e2
  | oi_ctx_handle c h => oi_ctx_handle (add_oi_oi c c2) h
  end.

Lemma add_oi_oi_hole_r :
  forall (V:Set) (c:oi_ctx V), add_oi_oi c oi_ctx_hole = c.
Admitted.

Fixpoint add_io_oi {V : Set} (c1 : io_ctx V) (c2 : oi_ctx V) : io_ctx V :=
  match c2 with
  | oi_ctx_hole => c1
  | oi_ctx_let c e2 => add_io_oi (io_ctx_let c1 e2) c
  | oi_ctx_handle c h => add_io_oi (io_ctx_handle c1 h) c
  end.

Fixpoint add_io_oi2 {V : Set} (c1 : io_ctx V) (c2 : oi_ctx V) : oi_ctx V :=
  match c1 with
  | io_ctx_top => c2
  | io_ctx_let c e2 => add_io_oi2 c (oi_ctx_let c2 e2)
  | io_ctx_handle c h => add_io_oi2 c (oi_ctx_handle c2 h)
  end.

Fixpoint io_to_oi_aux {V : Set} (ctx : io_ctx V) (acc : oi_ctx V) : oi_ctx V :=
  match ctx with
  | io_ctx_top => acc
  | io_ctx_let ctx' e2 => io_to_oi_aux ctx' (oi_ctx_let acc e2)
  | io_ctx_handle ctx' h => io_to_oi_aux ctx' (oi_ctx_handle acc h)
  end.

Definition io_to_oi {V : Set} (ctx : io_ctx V) : oi_ctx V :=
  io_to_oi_aux ctx oi_ctx_hole.

Fixpoint oi_to_io_aux {V : Set} (ctx : oi_ctx V) (acc : io_ctx V) : io_ctx V :=
  match ctx with
  | oi_ctx_hole => acc
  | oi_ctx_let ctx' e2 => oi_to_io_aux ctx' (io_ctx_let acc e2)
  | oi_ctx_handle ctx' h => oi_to_io_aux ctx' (io_ctx_handle acc h)
  end.

Definition oi_to_io {V : Set} (ctx : oi_ctx V) : io_ctx V :=
  oi_to_io_aux ctx io_ctx_top.

Lemma io_plug_bijection :
  forall (V:Set) (c:io_ctx V) (e:expr V),
    io_plug c e = oi_plug (io_to_oi c) e
.
Admitted.

Lemma oi_implies_io :
  forall (V:Set) (c1 c2:oi_ctx V),
    c1 = c2 -> oi_to_io c1 = oi_to_io c2.
Admitted.

Lemma io_bijection_composition :
  forall (V:Set) (c:io_ctx V),
    oi_to_io (io_to_oi c) = c.
Admitted.

Lemma bijection_add_oi_oi :
  forall (V:Set) (c1:io_ctx V) (c2:oi_ctx V),
    oi_to_io (add_oi_oi (io_to_oi c1) c2) = add_io_oi c1 c2.
Admitted.

Lemma plug_add_io_oi :
  forall (V:Set) (c1:io_ctx V) (c2:oi_ctx V) (e:expr V),
  io_plug (add_io_oi c1 c2) e = io_plug c1 (oi_plug c2 e).
Admitted.

Lemma plug_add_oi_oi :
  forall (V:Set) (c1 c2:oi_ctx V) (e:expr V),
  oi_plug (add_oi_oi c1 c2) e = oi_plug c1 (oi_plug c2 e).
Admitted.

Lemma io_plug_injection :
  forall (V:Set) (c:io_ctx V) (e1 e2:expr V),
    io_plug c e1 = io_plug c e2 -> e1 = e2.
Admitted.

Lemma oi_plug_injection :
  forall (V:Set) (c:oi_ctx V) (e1 e2:expr V),
    oi_plug c e1 = oi_plug c e2 -> e1 = e2.
Admitted.

Lemma oi_ctx_handles_op_add :
  forall (V:Set) (c1 c2:oi_ctx V) (l:string),
    OiCtxHandlesOp (add_oi_oi c1 c2) l <-> OiCtxHandlesOp c1 l \/ OiCtxHandlesOp c2 l.
Admitted.

Lemma not_oi_ctx_handles_op_add :
  forall (V:Set) (c1 c2:oi_ctx V) (l:string),
    ~OiCtxHandlesOp (add_oi_oi c1 c2) l -> ~OiCtxHandlesOp c1 l /\ ~OiCtxHandlesOp c2 l.
Admitted.

Lemma oi_ctx_handles_op_bijection :
  forall (V:Set) (c:oi_ctx V) (l:string),
    OiCtxHandlesOp c l -> IoCtxHandlesOp (oi_to_io c) l.
Admitted.

Lemma not_oi_ctx_handles_op_bijection :
  forall (V:Set) (c:oi_ctx V) (l:string),
    ~OiCtxHandlesOp c l -> ~IoCtxHandlesOp (oi_to_io c) l.
Admitted.

Lemma add_io_io_eq_add_io_oi :
  forall (V:Set) (c1:io_ctx V) (c2:oi_ctx V),
    add_io_io c1 (oi_to_io c2) = add_io_oi c1 c2.
Admitted.

Lemma add_io_oi2_eq_add_oi_oi :
  forall (V:Set) (c1 c2:oi_ctx V),
    add_io_oi2 (oi_to_io c1) c2 = add_oi_oi c1 c2.
Admitted.
