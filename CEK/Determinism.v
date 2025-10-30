Require Import CEK.Syntax.
Require Import CEK.Semantics.
Require Import CEK.Tactics.
Require Import General.Definitions.
Require Import General.Tactics.
Require Import Coq.Program.Equality.

Theorem cek_deterministic : 
  deterministic cek_red.
Proof.
  intros s1 s2 s3 Hstep1 Hstep2.
  inv Hstep1; inv Hstep2; easy.
  - Handles_contra.
  - Handles_contra.
  - specialize (HandlesOpWith_deterministic _ _ _ _ HHandlesOp HHandlesOp0) as ?.
    subst. reflexivity.
Qed.
