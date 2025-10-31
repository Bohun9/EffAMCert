Require Import Coq.Program.Equality.
Require Import General.Tactics.
Require Import Lang.Tactics.
Export Lang.Tactics.

Ltac destruct_existT :=
  repeat match goal with
  | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
      dependent destruction H
  end.

Ltac unify_equalities :=
  match goal with
  | [ H1 : ?X = ?A, H2 : ?X = ?B |- _ ] =>
      rewrite H1 in H2; subst
  end.

Ltac auto_inj :=
  match goal with
  | [ H : _ = _ |- _ ] =>
      inj H
  end.

Ltac easy :=
  repeat (
    destruct_existT ||
    unify_equalities ||
    auto_inj ||
    discriminate ||
    auto
  ).
