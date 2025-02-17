Require Import CAM.Syntax.
Require Import CAM.Semantics.
Require Import Lang.Semantics.
Require Import ContextProperties.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.

Lemma val_eq_plug :
  forall (V : Set) (C : i_ctx V) (v : value V) e,
    e_val v = C[e]ᵢ -> C = i_ctx_top /\ e_val v = e.
Proof.
  intros. generalize dependent e. induction C; intros.
  - simpl in H. subst. auto.
  - simpl in H. apply IHC in H as [_ Hcontra]. discriminate Hcontra.
  - simpl in H. apply IHC in H as [_ Hcontra]. discriminate Hcontra.
Qed.

Inductive atomic_expr {V : Set} : expr V -> Prop :=
  | atomic_add (n1 n2 : nat) :
      atomic_expr (e_add n1 n2)
  | atomic_app (e : expr (inc V)) (v : value V) :
      atomic_expr (e_app (v_lam e) v)
  | atomic_do (l : string) (v : value V) :
      atomic_expr (e_do l v).

Hint Constructors atomic_expr : core.

Lemma plug_atomic_eq_plug_o :
  forall (V : Set) (C C1 : o_ctx V) a e,
    C[a]ₒ = C1[e]ₒ ->
    atomic_expr a -> 
    exists (C2 : o_ctx V), C = C1 ₒ+ₒ C2 /\ e = C2[a]ₒ.
Proof.
  intros. generalize dependent C1. induction C; intros.
  - simpl in H. inversion H0; subst; destruct C1;
    try discriminate; try (exists o_ctx_hole; auto).
  - destruct C1.
    + exists (o_ctx_let C e2). simpl. split; auto.
    + simpl in H. injection H as HC He2; subst.
      apply IHC in HC as [C2 [HC He]]; subst.
      exists C2. split; auto.
    + discriminate.
  - destruct C1.
    + exists (o_ctx_handle C h). simpl. split; auto.
    + discriminate.
    + simpl in H. injection H as HC He2; subst.
      apply IHC in HC as [C2 [HC He]]; subst.
      exists C2. split; auto.
Qed.

Lemma plug_atomic_eq_plug_i :
  forall (V : Set) (C C1 : i_ctx V) a e,
    C[a]ᵢ = C1[e]ᵢ ->
    atomic_expr a -> 
    exists (C2 : o_ctx V), C = C1 +ᵢ C2 /\ e = C2[a]ₒ.
Proof.
  intros.
  repeat rewrite i_plug_bijection in H.
  apply plug_atomic_eq_plug_o in H as [C2 [HC He]]; subst; auto.
  exists C2. split; auto.
  assert (H : toᵢ (toₒ C) = toᵢ((toₒ C1) ₒ+ₒ C2)).
  { f_equal. assumption. }
  rewrite bijection_composition_i in H.
  rewrite bijection_add_oo in H.
  assumption.
Qed.

Inductive compound_expr {V : Set} : expr V -> value V -> o_ctx V -> Prop :=
  | compound_let (v : value V) (e2 : expr (inc V)) :
    compound_expr (e_let v e2) v (o_ctx_let o_ctx_hole e2)
  | compound_handle (v : value V) (h : handler V) :
    compound_expr (e_handle v h) v (o_ctx_handle o_ctx_hole h).

Hint Constructors compound_expr : core.

Lemma plug_compound_eq_plug_o :
  forall (V : Set) (C C1 C' : o_ctx V) (c e : expr V) v,
    C[c]ₒ = C1[e]ₒ ->
    compound_expr c v C' ->
    (C1 = C ₒ+ₒ C' /\ e = v)
    \/ exists (C2 : o_ctx V), C = C1 ₒ+ₒ C2 /\ e = C2[c]ₒ.
Proof.
  intros. generalize dependent C1. induction C; intros.
  - simpl. simpl in H. inversion H0; subst.
    + destruct C1.
      * right. exists o_ctx_hole. split; auto.
      * left. injection H1 as Hv He2; subst.
        destruct C1; try discriminate. split; auto.
      * discriminate.
    + destruct C1.
      * right. exists o_ctx_hole. split; auto.
      * discriminate.
      * left. injection H1 as Hv He2; subst.
        destruct C1; try discriminate. split; auto.
  - destruct C1.
    + right. exists (o_ctx_let C e2). split; auto.
    + simpl in H. injection H as HC He2; subst.
      apply IHC in HC as [[HC1 He] | [C2 [HC He]]]; subst.
      * left. simpl. split; auto.
      * right. exists C2. split; auto.
    + discriminate.
  - destruct C1.
    + right. exists (o_ctx_handle C h). split; auto.
    + discriminate.
    + simpl in H. injection H as HC He2; subst.
      apply IHC in HC as [[HC1 He] | [C2 [HC He]]]; subst.
      * left. simpl. split; auto.
      * right. exists C2. split; auto.
Qed.

Lemma plug_compound_eq_plug_i :
  forall (V : Set) (C C1 : i_ctx V) (C' : o_ctx V) (c e : expr V) v,
    C[c]ᵢ = C1[e]ᵢ ->
    compound_expr c v C' ->
    (C1 = C +ᵢ C' /\ e = v)
    \/ exists (C2 : o_ctx V), C = C1 +ᵢ C2 /\ e = C2[c]ₒ.
Proof.
  intros.
  repeat rewrite i_plug_bijection in H.
  apply plug_compound_eq_plug_o with (C' := C') (v := v)
  in H as [[HC1 He] | [C2 [HC He]]]; subst; auto.
  - left.
    assert (H : toᵢ (toₒ C1) = toᵢ((toₒ C) ₒ+ₒ C')).
    { f_equal. assumption. }
    rewrite bijection_composition_i in H.
    rewrite bijection_add_oo in H.
    split; auto.
  - right.
    assert (H : toᵢ (toₒ C) = toᵢ ((toₒ C1) ₒ+ₒ C2)).
    { f_equal. assumption. }
    rewrite bijection_composition_i in H.
    rewrite bijection_add_oo in H.
    exists C2. split; auto.
Qed.

Lemma plug_handle_do_eq_plug_o :
  forall (V : Set) (C C1 C' : o_ctx V) e h l v,
    C[ e_handle (C'[e_do l v]ₒ) h ]ₒ = C1[e]ₒ ->
    (exists (C2 : o_ctx V),
      C = C1 ₒ+ₒ C2
      /\ e = C2[e_handle (C'[e_do l v]ₒ) h]ₒ)
    \/ (exists (C'1 C'2 : o_ctx V),
      C' = C'1 ₒ+ₒ C'2
      /\ C1 = C ₒ+ₒ o_ctx_handle C'1 h
      /\ e = C'2 [e_do l v]ₒ).
Proof.
  intros. generalize dependent C1. induction C; intros.
  - destruct C1.
    + left. exists o_ctx_hole. split; auto.
    + simpl in H. discriminate.
    + simpl in H. injection H as HC' Hh; subst.
      apply plug_atomic_eq_plug_o in HC' as [C2 [HC' He]]; subst; auto.
      right. exists C1. exists C2. split; auto.
  - destruct C1.
    + left. exists (o_ctx_let C e2). split; auto.
    + simpl in H. injection H as HC He2; subst.
      apply IHC in HC as [[C2 [HC He]] | [C'1 [C'2 [HC' [HC1 He]]]]]; subst.
      * left. exists C2. split; auto.
      * right. exists C'1. exists C'2. split; auto.
    + discriminate.
  - destruct C1.
    + left. exists (o_ctx_handle C h0). split; auto.
    + discriminate.
    + simpl in H. injection H as HC He2; subst.
      apply IHC in HC as [[C2 [HC He]] | [C'1 [C'2 [HC' [HC1 He]]]]]; subst.
      * left. exists C2. split; auto.
      * right. exists C'1. exists C'2. split; auto.
Qed.

Lemma plug_handle_do_eq_plug_i :
  forall (V : Set) (C C1 : i_ctx V) (C' : o_ctx V) e h l v,
    C[ e_handle (C'[e_do l v]ₒ) h ]ᵢ = C1[e]ᵢ ->
    (exists (C2 : o_ctx V),
      C = C1 +ᵢ C2
      /\ e = C2[e_handle (C'[e_do l v]ₒ) h]ₒ)
    \/ (exists (C'1 C'2 : o_ctx V),
      C' = C'1 ₒ+ₒ C'2
      /\ C1 = C +ᵢ o_ctx_handle C'1 h
      /\ e = C'2 [e_do l v]ₒ).
Proof.
  intros.
  repeat rewrite i_plug_bijection in H.
  apply plug_handle_do_eq_plug_o in H
  as [[C2 [HC He]] | [C'1 [C'2 [HC' [HC1 He]]]]]; subst.
  - left. exists C2. split; auto.
    assert (H : toᵢ (toₒ C) = toᵢ ((toₒ C1) ₒ+ₒ C2)).
    { f_equal. assumption. }
    rewrite bijection_composition_i in H.
    rewrite bijection_add_oo in H.
    assumption.
  - right. exists C'1. exists C'2. repeat split; auto.
    assert (H : toᵢ (toₒ C1) = toᵢ ((toₒ C) ₒ+ₒ o_ctx_handle C'1 h)).
    { f_equal. assumption. }
    rewrite bijection_composition_i in H.
    rewrite bijection_add_oo in H.
    assumption.
Qed.
