Lemma not_or_and :
  forall (P Q : Prop),
    ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  tauto.
Qed.

Lemma not_and_or :
  forall (P Q : Prop),
  ~P /\ ~Q -> ~(P \/ Q).
Proof.
  tauto.
Qed.

Hint Resolve not_or_and : core.
Hint Resolve not_and_or : core.
