Ltac inv H := inversion H; subst; clear H.

Ltac inj H := injection H; intros; subst; clear H.
