Require Import Lang.Syntax.

Ltac inv H := inversion H; subst; clear H.

Ltac Handles_contra :=
  match goal with
  | [ H1 : ~HandlesOp ?h ?l, H2 : HandlesOpWith ?h ?l ?e  |- _ ] =>
      let H := fresh "H" in
      assert (H : HandlesOp h l);
      [ exists e; assumption | auto ]
  end.
