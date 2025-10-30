Require Import Utf8.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Export Coq.Strings.String.
Require Import Coq.Lists.List.

Inductive inc (V : Set) : Set :=
  | VZ : inc V
  | VS : V -> inc V.

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
  | v_nat (n : nat)
  | v_var (x : V)
  | v_lam (e : expr (inc V))

with expr (V : Set) : Set :=
  | e_val    (v : value V)
  | e_add    (v1 v2 : value V)
  | e_app    (v1 v2 : value V)
  | e_let    (e1 : expr V) (e2 : expr (inc V))
  | e_do     (l : string) (v : value V)
  | e_handle (e : expr V) (h : handler V)

with handler (V : Set) : Set :=
  | h_handler (e_ret : expr (inc V))
              (h_ops : list (string * expr (inc (inc V)))).

Arguments v_nat {V}.
Arguments v_var {V}.
Arguments v_lam {V}.

Arguments e_add    {V}.
Arguments e_app    {V}.
Arguments e_val    {V}.
Arguments e_let    {V}.
Arguments e_do     {V}.
Arguments e_handle {V}.

Arguments h_handler {V}.

Coercion v_nat : nat >-> value.
Coercion e_val : value >-> expr.

Definition ret_clause {V : Set} (h : handler V) : expr (inc V) :=
  match h with
  | h_handler e_ret _ => e_ret
  end.

(* The two kinds of evaluation contexts are inside-out and outside-in.
   Often it is more natural to work with one of them, depending on
   whether the context is extended at the top or at the bottom. *)

Inductive i_ctx (V : Set) : Set :=
  | i_ctx_top
  | i_ctx_let (C1 : i_ctx V) (e2 : expr (inc V))
  | i_ctx_handle (C1 : i_ctx V) (h : handler V).

Arguments i_ctx_top    {V}.
Arguments i_ctx_let    {V}.
Arguments i_ctx_handle {V}.

Fixpoint i_plug {V : Set} (C : i_ctx V) (e : expr V) : expr V :=
  match C with
  | i_ctx_top => e
  | i_ctx_let C1 e2 => i_plug C1 (e_let e e2)
  | i_ctx_handle C1 h => i_plug C1 (e_handle e h)
  end.

Inductive o_ctx (V : Set) : Set :=
  | o_ctx_hole
  | o_ctx_let (C1 : o_ctx V) (e2 : expr (inc V))
  | o_ctx_handle (C1 : o_ctx V) (h : handler V).

Arguments o_ctx_hole   {V}.
Arguments o_ctx_let    {V}.
Arguments o_ctx_handle {V}.

Fixpoint o_plug {V : Set} (C : o_ctx V) (e : expr V) : expr V :=
  match C with
  | o_ctx_hole => e
  | o_ctx_let C1 e2 => e_let (o_plug C1 e) e2
  | o_ctx_handle C1 h => e_handle (o_plug C1 e) h
  end.

Notation "'top'" := (i_ctx_top) (at level 30).
Notation "'hole'" := (o_ctx_hole) (at level 30).
Notation "C '[' e ']ᵢ'" := (i_plug C e) (at level 40).
Notation "C '[' e ']ₒ'" := (o_plug C e) (at level 40).

Check i_ctx_top [2]ᵢ.
Check o_ctx_hole [ o_ctx_hole [2]ₒ ]ₒ.

Inductive HandlesOpWith {V : Set}
  : handler V -> string -> expr (inc (inc V)) -> Prop :=
  | handles_op_with
      (e_ret : expr (inc V)) (h_ops : list (string * expr (inc (inc V))))
      (l : string) (e_op : expr (inc (inc V))) :
      In (l, e_op) h_ops ->
      HandlesOpWith (h_handler e_ret h_ops) l e_op.

Definition HandlesOp {V : Set} (h : handler V) (l : string) : Prop :=
  exists e_op, HandlesOpWith h l e_op.

Fixpoint OctxHandlesOp {V : Set} (C : o_ctx V) (l : string) : Prop :=
  match C with
  | o_ctx_hole => False
  | o_ctx_let C1 _ => OctxHandlesOp C1 l
  | o_ctx_handle C1 h => HandlesOp h l \/ OctxHandlesOp C1 l
  end.

Hint Unfold OctxHandlesOp : core.

Fixpoint IctxHandlesOp {V : Set} (C : i_ctx V) (l : string) : Prop :=
  match C with
  | i_ctx_top => False
  | i_ctx_let C1 _ => IctxHandlesOp C1 l
  | i_ctx_handle C1 h => HandlesOp h l \/ IctxHandlesOp C1 l
  end.

Lemma HandlesOp_dec :
  forall {V : Set} (h : handler V) (l : string),
    HandlesOp h l \/ ~HandlesOp h l.
Admitted.

Lemma HandlesOpWith_deterministic :
  forall {V : Set} (h : handler V) (l : string) e e',
    HandlesOpWith h l e -> HandlesOpWith h l e' -> e = e'.
Admitted.

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
  | e_val v => e_val (vmap f v)
  | e_add v1 v2 => e_add (vmap f v1) (vmap f v2)
  | e_app e1 e2 => e_app (vmap f e1) (vmap f e2)
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
  | h_handler e_ret h_ops =>
      h_handler (emap (liftA f) e_ret)
                (map (fun '(l, e) => (l, emap (liftA (liftA f)) e)) h_ops)
  end.

Fixpoint i_ctx_map {A B : Set} (f : A -> B) (C : i_ctx A) : i_ctx B := 
  match C with
  | i_ctx_top => i_ctx_top
  | i_ctx_let C1 e2 => i_ctx_let (i_ctx_map f C1) (emap (liftA f) e2)
  | i_ctx_handle C1 h => i_ctx_handle (i_ctx_map f C1) (hmap f h)
  end.

Fixpoint o_ctx_map {A B : Set} (f : A -> B) (C : o_ctx A) : o_ctx B := 
  match C with
  | o_ctx_hole => o_ctx_hole
  | o_ctx_let C1 e2 => o_ctx_let (o_ctx_map f C1) (emap (liftA f) e2)
  | o_ctx_handle C1 h => o_ctx_handle (o_ctx_map f C1) (hmap f h)
  end.

(** Shifting of expressions (s† operation). This operation shifts expression
  * to a context where one more variable is allowed *)
Definition eshift {A : Set} (e : expr A) : expr (inc A) := emap VS e.

(** Shifting of values *)
Definition vshift {A : Set} (v : value A) : value (inc A) := vmap VS v.

(** Shifting of handlers *)
Definition hshift {A : Set} (h : handler A) : handler (inc A) := hmap VS h.

(** Shifting of contexts *)
Definition i_ctx_shift {A : Set} (C : i_ctx A) : i_ctx (inc A) := i_ctx_map VS C.
Definition o_ctx_shift {A : Set} (C : o_ctx A) : o_ctx (inc A) := o_ctx_map VS C.

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
  | e_val v => e_val (vbind f v)
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
  end.

(** Substitution of single value in expression *)
Definition esubst {A : Set} (e : expr (inc A)) (v : value A) : expr A :=
  ebind (v_var [↦ v ]) e.

(** Substitution of single value in value *)
Definition vsubst {A : Set} (v' : value (inc A)) (v : value A) : value A :=
  vbind (v_var [↦ v ]) v'.
