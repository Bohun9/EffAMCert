Lemma not_or_and :
  forall (P Q : Prop),
    ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  tauto.
Qed.
