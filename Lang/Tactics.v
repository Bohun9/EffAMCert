Require Import Lang.Syntax.

Ltac Handles_contra :=
  match goal with
  | [ H1 : ~HandlesOp ?h ?l, H2 : HandlesOpWith ?h ?l ?e  |- _ ] =>
      exfalso; apply H1; exists e; apply H2
  end.
