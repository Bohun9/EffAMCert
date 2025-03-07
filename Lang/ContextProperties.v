Require Import Lang.Syntax.

Lemma HandlesOp_dec :
  forall {V : Set} (h : handler V) (l : string),
    HandlesOp h l \/ ~HandlesOp h l.
Admitted.

(* ===================================================================================== *)
(* Context addition definitions *)

Fixpoint add_ii {V : Set} (C1 C2 : i_ctx V) : i_ctx V :=
  match C2 with
  | i_ctx_top => C1
  | i_ctx_let C e2 => i_ctx_let (add_ii C1 C) e2
  | i_ctx_handle C h => i_ctx_handle (add_ii C1 C) h
  end.

Fixpoint add_oo {V : Set} (C1 C2 : o_ctx V) : o_ctx V :=
  match C1 with
  | o_ctx_hole => C2
  | o_ctx_let C e2 => o_ctx_let (add_oo C C2) e2
  | o_ctx_handle C h => o_ctx_handle (add_oo C C2) h
  end.

Fixpoint add_i {V : Set} (C1 : i_ctx V) (C2 : o_ctx V) : i_ctx V :=
  match C2 with
  | o_ctx_hole => C1
  | o_ctx_let C e2 => add_i (i_ctx_let C1 e2) C
  | o_ctx_handle C h => add_i (i_ctx_handle C1 h) C
  end.

Fixpoint add_o {V : Set} (C1 : i_ctx V) (C2 : o_ctx V) : o_ctx V :=
  match C1 with
  | i_ctx_top => C2
  | i_ctx_let C e2 => add_o C (o_ctx_let C2 e2)
  | i_ctx_handle C h => add_o C (o_ctx_handle C2 h)
  end.

Notation "C1 'ᵢ+ᵢ' C2" := (add_ii C1 C2) (at level 40).
Notation "C1 'ₒ+ₒ' C2" := (add_oo C1 C2) (at level 40).
Notation "C1 '+ᵢ' C2" := (add_i C1 C2) (at level 40).
Notation "C1 '+ₒ' C2" := (add_o C1 C2) (at level 40).

Definition i_to_o {V : Set} (C : i_ctx V) : o_ctx V :=
  C +ₒ o_ctx_hole.

Definition o_to_i {V : Set} (C : o_ctx V) : i_ctx V :=
  i_ctx_top +ᵢ C.

Notation "'toₒ' C" := (i_to_o C) (at level 40).
Notation "'toᵢ' C" := (o_to_i C) (at level 40).

(* ===================================================================================== *)
(* Context addition properties *)


(* ===================================================================================== *)
(* Neutral elements of addition *)

Theorem add_ii_top_l :
  forall (V : Set) (C : i_ctx V),
    i_ctx_top ᵢ+ᵢ C = C.
Proof.
  intros. induction C.
  - simpl. reflexivity.
  - simpl. rewrite IHC. reflexivity.
  - simpl. rewrite IHC. reflexivity.
Qed.


Lemma add_oo_hole_r :
  forall (V : Set) (C : o_ctx V),
    C ₒ+ₒ hole = C.
Proof.
  intros. induction C.
  - simpl. reflexivity.
  - simpl. rewrite IHC. reflexivity.
  - simpl. rewrite IHC. reflexivity.
Qed.

Hint Rewrite add_oo_hole_r : core.

(* Note that there are no such theorems for add_i and add_o *)

(* ===================================================================================== *)
(* Addition associativity with plug *)

Lemma add_o_plug_assoc :
  forall (V : Set) (C1 : i_ctx V) (C2 : o_ctx V) e,
    C1 [ C2[e]ₒ ]ᵢ = (C1 +ₒ C2) [e]ₒ.
Proof.
  intros. generalize dependent C2. induction C1; intro.
  - simpl. reflexivity.
  - simpl.
    assert (H : e_let (C2 [e]ₒ) e2 = (o_ctx_let C2 e2) [e]ₒ).
    { simpl. reflexivity. }
    rewrite H. apply IHC1.
  - simpl.
    assert (H : e_handle (C2 [e]ₒ) h = (o_ctx_handle C2 h) [e]ₒ).
    { simpl. reflexivity. }
    rewrite H. apply IHC1.
Qed.

Lemma add_i_plug_assoc :
  forall (V : Set) (C1 : i_ctx V) (C2 : o_ctx V) e,
    (C1 +ᵢ C2) [e]ᵢ = C1 [ C2[e]ₒ ]ᵢ.
Proof.
  intros. generalize dependent C1. induction C2; intro.
  - simpl. reflexivity.
  - simpl.
    assert (H : C1 [e_let (C2 [e ]ₒ) e2 ]ᵢ = i_ctx_let C1 e2 [ C2[e]ₒ ]ᵢ).
    { simpl. reflexivity. }
    rewrite H. apply IHC2.
  - simpl.
    assert (H : C1 [e_handle (C2 [e ]ₒ) h ]ᵢ = i_ctx_handle C1 h [ C2[e]ₒ ]ᵢ).
    { simpl. reflexivity. }
    rewrite H. apply IHC2.
Qed.

Lemma add_oo_plug_assoc :
  forall (V : Set) (C1 C2 : o_ctx V) e,
    (C1 ₒ+ₒ C2) [e]ₒ = C1 [ C2[e]ₒ ]ₒ.
Proof.
  intros. induction C1.
  - simpl. reflexivity.
  - simpl. rewrite IHC1. reflexivity.
  - simpl. rewrite IHC1. reflexivity.
Qed.

Theorem add_ii_plug_assoc : 
  forall (V : Set) (C1 C2 : i_ctx V) e,
    (C1 ᵢ+ᵢ C2) [e]ᵢ = C1 [ C2[e]ᵢ ]ᵢ.
Proof.
   intros. generalize dependent e. induction C2; intro.
  - simpl. reflexivity.
  - simpl. rewrite IHC2. reflexivity.
  - simpl. rewrite IHC2. reflexivity.
Qed.

Lemma i_plug_bijection :
  forall (V : Set) (C : i_ctx V) e,
    C[e]ᵢ = (toₒ C) [e]ₒ.
Proof.
  intros. unfold i_to_o.
  rewrite <- add_o_plug_assoc.
  simpl. reflexivity.
Qed.

Lemma o_plug_bijection :
  forall (V : Set) (C : o_ctx V) e,
    C[e]ₒ = (toᵢ C) [e]ᵢ.
Proof.
  intros. unfold o_to_i.
  rewrite add_i_plug_assoc.
  simpl. reflexivity.
Qed.

(* Lemma oi_implies_io : *)
(*   forall (V : Set) (C C' : o_ctx V), *)
(*     C = C' -> toᵢ C = toᵢ C'. *)
(* Admitted. *)

(* ===================================================================================== *)
(* Addition associativity with addition *)

Lemma add_ii_add_i_assoc :
  forall (V : Set) (C1 C2 : i_ctx V) (C3 : o_ctx V),
    (C1 ᵢ+ᵢ C2) +ᵢ C3 = C1 ᵢ+ᵢ (C2 +ᵢ C3).
Proof.
  intros. generalize dependent C2. induction C3; intro.
  - simpl. reflexivity.
  - simpl.
    assert (H : i_ctx_let (C1 ᵢ+ᵢ C2) e2 = C1 ᵢ+ᵢ i_ctx_let C2 e2).
    { simpl. reflexivity. }
    rewrite H. apply IHC3.
  - simpl.
    assert (H : i_ctx_handle (C1 ᵢ+ᵢ C2) h = C1 ᵢ+ᵢ i_ctx_handle C2 h).
    { simpl. reflexivity. }
    rewrite H. apply IHC3.
Qed.

Lemma add_ii_add_i_assoc2 :
  forall (V : Set) (C1 C2 : i_ctx V) (C3 : o_ctx V),
    (C1 ᵢ+ᵢ C2) +ᵢ C3 = C1 +ᵢ (C2 +ₒ C3).
Proof.
  intros. generalize dependent C3. induction C2; intro.
  - simpl. reflexivity.
  - simpl.
    assert (H : i_ctx_let (C1 ᵢ+ᵢ C2) e2 +ᵢ C3 = (C1 ᵢ+ᵢ C2) +ᵢ o_ctx_let C3 e2).
    { simpl. reflexivity. }
    rewrite H. apply IHC2.
  - simpl.
    assert (H : i_ctx_handle (C1 ᵢ+ᵢ C2) h +ᵢ C3 = (C1 ᵢ+ᵢ C2) +ᵢ o_ctx_handle C3 h).
    { simpl. reflexivity. }
    rewrite H. apply IHC2.
Qed.

Lemma add_o_add_oo_assoc :
  forall (V : Set) (C1 : i_ctx V) (C2 C3 : o_ctx V),
    (C1 +ₒ C2) ₒ+ₒ C3 = C1 +ₒ (C2 ₒ+ₒ C3).
Proof.
  intros. generalize dependent C2. induction C1; intro.
  - simpl. reflexivity.
  - simpl.
    assert (H : o_ctx_let (C2 ₒ+ₒ C3) e2 = (o_ctx_let C2 e2) ₒ+ₒ C3).
    { simpl. reflexivity. }
    rewrite H. apply IHC1.
  - simpl.
    assert (H : o_ctx_handle (C2 ₒ+ₒ C3) h = (o_ctx_handle C2 h) ₒ+ₒ C3).
    { simpl. reflexivity. }
    rewrite H. apply IHC1.
Qed.

Lemma add_o_add_oo_assoc2 :
  forall (V : Set) (C1 : i_ctx V) (C2 C3 : o_ctx V),
    C1 +ₒ (C2 ₒ+ₒ C3) = (C1 +ᵢ C2) +ₒ C3.
Proof.
  intros. generalize dependent C1. induction C2; intro.
  - simpl. reflexivity.
  - simpl.
    assert (H : C1 +ₒ o_ctx_let (C2 ₒ+ₒ C3) e2 = (i_ctx_let C1 e2) +ₒ (C2 ₒ+ₒ C3)).
    { simpl. reflexivity. }
    rewrite H. apply IHC2.
  - simpl.
    assert (H : C1 +ₒ o_ctx_handle (C2 ₒ+ₒ C3) h = (i_ctx_handle C1 h) +ₒ (C2 ₒ+ₒ C3)).
    { simpl. reflexivity. }
    rewrite H. apply IHC2.
Qed.

(* Conclusions *)

Lemma bijection_composition_i :
  forall (V : Set) (C : i_ctx V),
    toᵢ (toₒ C) = C.
Proof.
  intros. unfold i_to_o. unfold o_to_i.
  rewrite <- add_ii_add_i_assoc2.
  rewrite add_ii_top_l.
  simpl. reflexivity.
Qed.

Lemma bijection_add_oo :
  forall (V : Set) (C1 : i_ctx V) (C2 : o_ctx V),
    toᵢ ((toₒ C1) ₒ+ₒ C2) = C1 +ᵢ C2.
Proof.
  intros. unfold i_to_o. unfold o_to_i.
  rewrite add_o_add_oo_assoc. simpl.
  rewrite <- add_ii_add_i_assoc2.
  rewrite add_ii_top_l.
  reflexivity.
Qed.

Lemma add_ii_eq_add_i :
  forall (V : Set) (C1 : i_ctx V) (C2 : o_ctx V),
    C1 ᵢ+ᵢ (toᵢ C2) = C1 +ᵢ C2.
Proof.
  intros. unfold o_to_i.
  rewrite <- add_ii_add_i_assoc.
  simpl. reflexivity.
Qed.

Lemma add_o_eq_add_oo :
  forall (V:Set) (C1 C2 : o_ctx V),
    (toᵢ C1) +ₒ C2 = C1 ₒ+ₒ C2.
Proof.
  intros. unfold o_to_i.
  rewrite <- add_o_add_oo_assoc2.
  simpl. reflexivity.
Qed.

Lemma add_oo_eq_add_i :
  forall (V : Set) (C1 : i_ctx V) (C2 : o_ctx V),
    (toₒ C1) ₒ+ₒ C2 = toₒ (C1 +ᵢ C2).
Proof.
  intros. unfold i_to_o.
  rewrite add_o_add_oo_assoc. simpl.
  rewrite <- add_o_add_oo_assoc2.
  rewrite add_oo_hole_r.
  reflexivity.
Qed.

(* ===================================================================================== *)
(* Injection of plugs *)

Lemma i_plug_injection :
  forall (V : Set) (C : i_ctx V) e1 e2,
    C[e1]ᵢ = C[e2]ᵢ -> e1 = e2.
Proof.
  intro V. intro C. induction C; intros; simpl in H.
  - assumption.
  - apply IHC in H. injection H as He1. assumption.
  - apply IHC in H. injection H as He1. assumption.
Qed.

Lemma o_plug_injection :
  forall (V : Set) (C : o_ctx V) e1 e2,
    C[e1]ₒ = C[e2]ₒ -> e1 = e2.
Proof.
  intros. induction C; simpl in H.
  - assumption. 
  - injection H as He1. apply IHC in He1. assumption.
  - injection H as He1. apply IHC in He1. assumption.
Qed.

(* ===================================================================================== *)
(* Distribution of OctxHandlesOp and IctxHandlesOp *)

Lemma o_ctx_handles_op_add_oo_distr1 :
  forall (V : Set) (C1 C2 : o_ctx V) l,
    OctxHandlesOp (C1 ₒ+ₒ C2) l -> OctxHandlesOp C1 l \/ OctxHandlesOp C2 l.
Proof.
  intros. induction C1; simpl in H.
  - right. assumption.
  - simpl. apply IHC1. assumption.
  - simpl. destruct H.
    + left. left. assumption.
    + apply IHC1 in H.
      destruct H.
      * left. right. assumption.
      * right. assumption.
Qed.

Lemma o_ctx_handles_op_add_oo_distr2 :
  forall (V : Set) (C1 C2 : o_ctx V) l,
    OctxHandlesOp C1 l \/ OctxHandlesOp C2 l -> OctxHandlesOp (C1 ₒ+ₒ C2) l.
Proof.
  intros. induction C1.
  - destruct H.
    + contradiction.
    + simpl. assumption.
  - simpl in H. simpl. apply IHC1. assumption.
  - simpl in H. simpl.
    destruct H as [[H1 | H2] | H3].
    + left. assumption.
    + right. apply IHC1. left. assumption.
    + right. apply IHC1. right. assumption.
Qed.

Hint Resolve o_ctx_handles_op_add_oo_distr2 : core.

Lemma not_o_ctx_handles_op_add_oo_distr1 :
  forall (V : Set) (C1 C2 : o_ctx V) l,
    ~OctxHandlesOp (C1 ₒ+ₒ C2) l -> ~OctxHandlesOp C1 l /\ ~OctxHandlesOp C2 l.
Proof.
  intros. split; auto.
Qed.

Lemma i_ctx_handles_op_add_i_distr1 :
  forall (V : Set) (C1 : i_ctx V) (C2 : o_ctx V) l,
    IctxHandlesOp (C1 +ᵢ C2) l -> IctxHandlesOp C1 l \/ OctxHandlesOp C2 l.
Proof.
  intros. generalize dependent C1. induction C2; intro C1.
  - simpl. intro H. left. assumption.
  - simpl. intro H. apply IHC2 in H.
    simpl in H. assumption.
  - simpl. intro H. apply IHC2 in H. 
    simpl in H. destruct H as [[H | H] | H]; auto.
Qed.

Lemma i_ctx_handles_op_add_i_distr2 :
  forall (V : Set) (C1 : i_ctx V) (C2 : o_ctx V) l,
    IctxHandlesOp C1 l \/ OctxHandlesOp C2 l -> IctxHandlesOp (C1 +ᵢ C2) l.
Proof.
  intros. generalize dependent C1. induction C2; simpl; intros.
  - tauto.
  - apply IHC2. simpl. assumption.
  - apply IHC2. simpl. tauto.
Qed.

Hint Resolve i_ctx_handles_op_add_i_distr2 : core.

Lemma not_i_ctx_handles_op_add_i_distr1 :
  forall (V : Set) (C1 : i_ctx V) (C2 : o_ctx V) l,
    ~IctxHandlesOp (C1 +ᵢ C2) l -> ~IctxHandlesOp C1 l /\ ~OctxHandlesOp C2 l.
Proof.
  intros. split; auto.
Qed.

Lemma i_ctx_handles_op_add_o_distr1 :
  forall (V : Set) (C1 : i_ctx V) (C2 : o_ctx V) l,
    OctxHandlesOp (C1 +ₒ C2) l -> IctxHandlesOp C1 l \/ OctxHandlesOp C2 l.
Proof.
  intros. generalize dependent C2. induction C1; intros.
  - tauto.
  - simpl. specialize (IHC1 _ H) as [? | ?]; auto.
  - simpl. specialize (IHC1 _ H) as [? | ?]; auto.
    simpl in H0. destruct H0; auto.
Qed.

Lemma o_ctx_handles_op_bijection :
  forall (V : Set) (C : o_ctx V) l,
    IctxHandlesOp (toᵢ C) l -> OctxHandlesOp C l.
Proof.
  intros V C l. unfold o_to_i. intro.
  apply i_ctx_handles_op_add_i_distr1 in H.
  destruct H.
  - contradiction.
  - assumption.
Qed.

Lemma not_o_ctx_handles_op_bijection :
  forall (V : Set) (C : o_ctx V) l,
    ~OctxHandlesOp C l -> ~IctxHandlesOp (toᵢ C) l.
Proof.
  intros. intro. apply H.
  apply o_ctx_handles_op_bijection. assumption.
Qed.

Hint Resolve not_o_ctx_handles_op_bijection : core.

Lemma i_ctx_handles_op_bijection :
  forall (V : Set) (C : i_ctx V) l,
    OctxHandlesOp (toₒ C) l -> IctxHandlesOp C l.
Proof.
  intros V C l. unfold i_to_o. intro.
  apply i_ctx_handles_op_add_o_distr1 in H. destruct H.
  - assumption.
  - contradiction.
Qed.

Lemma not_i_ctx_handles_op_bijection :
  forall (V : Set) (C : i_ctx V) l,
    ~IctxHandlesOp C l -> ~OctxHandlesOp (toₒ C) l.
Proof.
  intros. intro. apply H.
  apply i_ctx_handles_op_bijection. assumption.
Qed.
