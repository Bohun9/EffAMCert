Require Import Utf8.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Export Coq.Strings.String.
Require Import Coq.Lists.List.

Inductive inc (V : Set) : Set :=
  | VZ : inc V
  | VS : V -> inc V
.

Arguments VZ {V}.
Arguments VS {V}.

(** Extending function to inc domain (γ[↦v] operation) *)
Definition inc_ext {A : Set} {B : Type} (f : A → B) (v : B) (x : inc A) : B :=
  match x with
  | VZ   => v
  | VS y => f y
  end.

Notation "f '[↦' v ']'" := (@inc_ext _ _ f v) (at level 50).

Inductive value (V : Set) : Set :=
  | v_nat : nat -> value V
  | v_var : V -> value V
  | v_lam : expr (inc V) -> value V

with expr (V : Set) : Set :=
  | e_add    : value V -> value V -> expr V
  | e_app    : value V -> value V -> expr V
  | e_ret    : value V -> expr V
  | e_let    : expr V -> expr (inc V) -> expr V
  | e_do     : string -> value V -> expr V
  | e_handle : expr V -> handler V -> expr V

with handler (V : Set) : Set :=
  | h_handler : (expr (inc V)) -> list (string * expr (inc (inc V))) -> handler V
.

Arguments v_nat {V}.
Arguments v_var {V}.
Arguments v_lam {V}.

Arguments e_add {V} v1 v2. (* why it does not use these names? *)
Arguments e_app {V}.
Arguments e_ret {V}.
Arguments e_let {V}.
Arguments e_do {V}.
Arguments e_handle {V}.

Arguments h_handler {V}.

Definition ret_clause {V : Set} (h : handler V) : expr (inc V) :=
  match h with
  | h_handler ret_clause _ => ret_clause
  end
.

(* Two kinds of evaluation contexts: inside-out and outside-in.
   Often it is more natural to work with one of them,
   depending on whether the context is extended at the top or at the bottom. *)
Inductive io_ctx (V : Set) : Set :=
  | io_ctx_top   : io_ctx V
  | io_ctx_let    : io_ctx V -> expr (inc V) -> io_ctx V
  | io_ctx_handle : io_ctx V -> handler V -> io_ctx V
.

Arguments io_ctx_top {V}.
Arguments io_ctx_let {V}.
Arguments io_ctx_handle {V}.

Fixpoint io_plug {V : Set} (c : io_ctx V) (e : expr V) : expr V :=
  match c with
  | io_ctx_top => e
  | io_ctx_let c1 e2 => io_plug c1 (e_let e e2)
  | io_ctx_handle c1 h => io_plug c1 (e_handle e h)
  end
.

Inductive oi_ctx (V : Set) : Set :=
  | oi_ctx_hole   : oi_ctx V
  | oi_ctx_let    : oi_ctx V -> expr (inc V) -> oi_ctx V
  | oi_ctx_handle : oi_ctx V -> handler V -> oi_ctx V
.

Arguments oi_ctx_hole {V}.
Arguments oi_ctx_let {V}.
Arguments oi_ctx_handle {V}.

Fixpoint oi_plug {V : Set} (c : oi_ctx V) (e : expr V) : expr V :=
  match c with
  | oi_ctx_hole => e
  | oi_ctx_let c1 e2 => e_let (oi_plug c1 e) e2
  | oi_ctx_handle c1 h => e_handle (oi_plug c1 e) h
  end
.

Inductive InAssocList {B : Set} : list (string * B) -> string -> B -> Prop :=
  | in_assoc_list_head (a : string) (b : B) (tail : list (string * B)) : InAssocList (cons (a,b) tail) a b
  | in_assoc_list_tail (a a' : string) (b b' : B) (tail : list (string * B))
      (H : InAssocList tail a b) (Ha_not_eq : ~(a = a'))
      : InAssocList (cons (a',b') tail) a b
  .

Lemma in_assoc_list_dec : forall (B:Set) (l:list (string*B)) (a:string),
  (exists b, InAssocList l a b) \/ ~(exists b, InAssocList l a b).
Proof.
  intros B l a. induction l as [|(a',b') l' IH].
  - right. intros [b H]. inversion H.
  - inversion IH as [[b Htail] | Htail].
    + left. specialize (string_dec a a') as [Heq | Hneq].
      -- exists b'. subst. apply in_assoc_list_head.
      -- exists b. apply in_assoc_list_tail.
         ++ assumption.
         ++ assumption.
    + specialize (string_dec a a') as [Heq | Hneq].
      -- left. exists b'. subst. apply in_assoc_list_head.
      -- right. intros [b Hlist]. inversion Hlist; subst.
         ++ apply Hneq. reflexivity.
         ++ apply Htail. exists b. assumption.
Qed.

Inductive HandlesOp {V : Set} : handler V -> string -> expr (inc (inc V)) -> Prop :=
  | handles_op : forall
      (ret_clause : expr (inc V))
      (op_clauses : list (string * expr (inc (inc V))))
      (l : string)
      (clause : expr (inc (inc V)))
      (H : InAssocList op_clauses l clause),
        HandlesOp (h_handler ret_clause op_clauses) l clause
.

Lemma handles_op_dec : forall (V:Set) (h:handler V) (l:string),
  (exists e, HandlesOp h l e) \/ ~(exists e, HandlesOp h l e).
Proof.
  intros V h l. destruct h as [ret ops].
  specialize (in_assoc_list_dec _  ops l) as [[e_op He_op] | H].
  - left. exists e_op. apply handles_op. assumption.
  - right. intros [e_op He_op]. inversion He_op.
    apply H. exists e_op. assumption.
Qed.

Fixpoint OiCtxHandlesOp {V : Set} (ctx : oi_ctx V) (l : string) : Prop :=
  match ctx with
  | oi_ctx_hole => False
  | oi_ctx_let ctx' _ => OiCtxHandlesOp ctx' l
  | oi_ctx_handle ctx' h => (exists e, HandlesOp h l e) \/ OiCtxHandlesOp ctx' l
  end
.

Fixpoint IoCtxHandlesOp {V : Set} (ctx : io_ctx V) (l : string) : Prop :=
  match ctx with
  | io_ctx_top => False
  | io_ctx_let ctx' _ => IoCtxHandlesOp ctx' l
  | io_ctx_handle ctx' h => (exists e, HandlesOp h l e) \/ IoCtxHandlesOp ctx' l
  end
.

(* Potential redexes (only add and app are potential) *)
Inductive predex {V : Set} : expr V -> Prop :=
  | predex_add (v1 v2 : value V) : predex (e_add v1 v2)
  | predex_app (v1 v2 : value V) : predex (e_app v1 v2)
  | predex_let (v : value V) (e2 : expr (inc V)) : predex (e_let (e_ret v) e2)
  | predex_handle_ret (v : value V) (h : handler V) : predex (e_handle (e_ret v) h)
  | predex_handle_op
      (h : handler V)
      (l : string)
      (v : value V)
      (c : oi_ctx V)
      (e_op : expr (inc (inc V)))
      (H_e_op : HandlesOp h l e_op)
      (H_ctx : ~OiCtxHandlesOp c l) :
      predex (e_handle (oi_plug c (e_do l v)) h)
.

Lemma de_morgan : forall (P Q : Prop), ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros P Q [HnP HnQ] [HP | HQ].
  - apply HnP. assumption.
  - apply HnQ. assumption.
Qed.

Theorem ex_oi_decomposition :
  forall (V:Set) (e:expr V),
    (exists (v:value V), e = e_ret v) \/
    (exists (c:oi_ctx V) (r:expr V), e = oi_plug c r /\ predex r) \/ 
    (exists (c:oi_ctx V) (l:string) (v:value V),
      e = oi_plug c (e_do l v) /\ ~OiCtxHandlesOp c l)
.
Proof.
  intros V e. induction e.
  - right. left. exists oi_ctx_hole. eexists. split.
    + simpl. reflexivity.
    + apply predex_add.
  - right. left. exists oi_ctx_hole. eexists. split.
    + simpl. reflexivity.
    + apply predex_app.
  - left. exists v. reflexivity.
  - destruct IHe1 as [[v H] | [[c [r [He Hr]]] | [c [l [v [He  Hc]]]]]]; subst.
    + right. left. exists oi_ctx_hole. eexists. split.
      -- simpl. reflexivity.
      -- apply predex_let.
    + right. left. exists (oi_ctx_let c e2). exists r. split.
      -- simpl. reflexivity.
      -- assumption.
    + right. right. exists (oi_ctx_let c e2). exists l. exists v. split.
      -- simpl. reflexivity.
      -- simpl. assumption.
  - right. right. exists oi_ctx_hole. exists s. exists v. split.
    + simpl. reflexivity.
    + simpl. intro. assumption.
  - destruct IHe as [[v H] | [[c [r [He Hr]]] | [c [l [v [He  Hc]]]]]]; subst.
    + right. left. exists oi_ctx_hole. eexists. split. 
      -- simpl. reflexivity.
      -- apply predex_handle_ret.
    + right. left. exists (oi_ctx_handle c h). exists r. simpl. split.
      -- reflexivity.
      -- assumption.
    + specialize (handles_op_dec _ h l) as [[e_op Hhandles] | Hnot_handles].
      -- right. left. exists oi_ctx_hole. eexists. split.
         ++ simpl. reflexivity.
         ++ apply predex_handle_op with (e_op := e_op).
            * assumption.
            * assumption.
      -- right. right. exists (oi_ctx_handle c h). exists l. exists v. split.
         ++ simpl. reflexivity.
         ++ simpl. apply de_morgan. split.
            * apply Hnot_handles.
            * assumption.
Qed.

(* ========================================================================= *)
(* Mapping, i.e., variable renaming *)

(** Lifting of renamings (↑ operation) *)
Definition liftA {A B : Set} (f : A → B) (x : inc A) : inc B :=
  match x with
  | VZ   => VZ
  | VS y => VS (f y)
  end.

(** Mapping of expressions and values († operation) *)
Fixpoint emap {A B : Set} (f : A → B) (e : expr A) : expr B :=
  match e with
  | e_add v1 v2 => e_add (vmap f v1) (vmap f v2)
  | e_app e1 e2 => e_app (vmap f e1) (vmap f e2)
  | e_ret v => e_ret (vmap f v)
  | e_let e1 e2 => e_let (emap f e1) (emap (liftA f) e2)
  | e_do l v => e_do l (vmap f v)
  | e_handle e' h => e_handle (emap f e') (hmap f h)
  end
with vmap {A B : Set} (f : A → B) (v : value A) : value B :=
  match v with
  | v_nat n => v_nat n
  | v_var x => v_var (f x)
  | v_lam e => v_lam (emap (liftA f) e)
  end
with hmap {A B : Set} (f : A -> B) (h : handler A) : handler B :=
  match h with
  | h_handler ret_clause op_clauses =>
      h_handler (emap (liftA f) ret_clause)
                (map (fun '(l,e) => (l, emap (liftA (liftA f)) e)) op_clauses)
  end.

Fixpoint cmap {A B : Set} (f : A -> B) (c : io_ctx A) : io_ctx B := 
  match c with
  | io_ctx_top => io_ctx_top
  | io_ctx_let ctx' e2 => io_ctx_let (cmap f ctx') (emap (liftA f) e2)
  | io_ctx_handle ctx' h => io_ctx_handle (cmap f ctx') (hmap f h)
  end.

(** Shifting of expressions (s† operation). This operation shifts expression
  * to a context where one more variable is allowed *)
Definition eshift {A : Set} (e : expr A) : expr (inc A) := emap VS e.

(** Shifting of values *)
Definition vshift {A : Set} (v : value A) : value (inc A) := vmap VS v.

(** Shifting of values *)
Definition cshift {A : Set} (c : io_ctx A) : io_ctx (inc A) := cmap VS c.

(* ========================================================================= *)
(* Binding, i.e., simultaneous substitution *)

(** Lifting of substitution (⇑ operation) *)
Definition liftS {A B : Set} (f : A → value B) (x : inc A) : value (inc B) :=
  match x with
  | VZ   => v_var VZ
  | VS y => vshift (f y)
  end.

(** Binding of expressions and value ( * operation) *)
Fixpoint ebind {A B : Set} (f : A → value B) (e : expr A) : expr B :=
  match e with
  | e_add e1 e2 => e_add (vbind f e1) (vbind f e2)
  | e_app e1 e2 => e_app (vbind f e1) (vbind f e2)
  | e_ret v => e_ret (vbind f v)
  | e_let e1 e2 => e_let (ebind f e1) (ebind (liftS f) e2)
  | e_do l v => e_do l (vbind f v)
  | e_handle e' h => e_handle (ebind f e') (hbind f h)
  end
with vbind {A B : Set} (f : A → value B) (v : value A) : value B :=
  match v with
  | v_nat n => v_nat n
  | v_var x => f x
  | v_lam e => v_lam (ebind (liftS f) e)
  end
with hbind {A B : Set} (f : A → value B) (h : handler A) : handler B :=
  match h with
  | h_handler ret_clause op_clauses =>
      h_handler (ebind (liftS f) ret_clause)
                (map (fun '(l,e) => (l, ebind (liftS (liftS f)) e)) op_clauses)
  end
.

(** Substitution of single value in expression *)
Definition esubst {A : Set} (e : expr (inc A)) (v : value A) : expr A :=
  ebind (v_var [↦ v ]) e.

(** Substitution of single value in value *)
Definition vsubst {A : Set} (v' : value (inc A)) (v : value A) : value A :=
  vbind (v_var [↦ v ]) v'.
