Require Import List.

Lemma Forall2_exists_r {A B : Type} : 
  forall l1 l2 P, 
    Forall2 P l1 l2 ->
    forall (x2 : B), 
      In x2 l2 ->
      exists (x1 : A), In x1 l1 /\ P x1 x2.
Proof.
  induction l1.
  intros.
  inversion H.
  subst.
  simpl in H0.
  contradiction H0.
  intros.
  inversion H.
  subst.
  destruct H0.
  exists a; split; subst; intuition.
  destruct (IHl1 _ _ H5 _ H0).
  exists x.
  destruct H1.
  split; [right; eauto | assumption].
Qed.