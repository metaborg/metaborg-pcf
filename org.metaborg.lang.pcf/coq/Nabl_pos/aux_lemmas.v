Require Import List.
Require Export Setoid.
Require Import Program.
Require Import Relation_Operators.

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


Lemma in_nth {A} : forall l (p : A), In p l <-> exists n, nth_error l n = Some p.
Proof.
  induction l.
  unfold In.
  intros; split; intuition.
  destruct H.
  destruct x.
  simpl in H.
  discriminate H.
  simpl in H.
  discriminate H.
  intros; split; intros.
  destruct H.
  exists 0; simpl; subst; eauto.
  rewrite IHl in H.
  destruct H.
  exists (S x).
  simpl.
  eauto.
  destruct H.
  destruct x.
  simpl in H.
  inversion H; subst; left; eauto.
  simpl in H.
  destruct (IHl p).
  right.
  apply H1.
  exists x; eauto.
Qed.

 (* $(&!@ unbelievable that these aren't in the library! *) 
Lemma tn1_rtn1: forall {A:Type} (R : relation A) (x y: A), 
                  clos_trans_n1 A R x y -> clos_refl_trans_n1 A R x y. 
Proof.
  intros. induction H. 
  eapply rtn1_trans; eauto.  eapply rtn1_refl.
  eapply rtn1_trans with y; eauto. 
Qed.  

Lemma rtn1_tn1: forall {A:Type} (R: relation A) (x y:A),
                  clos_refl_trans_n1 A R x y -> x = y \/ clos_trans_n1 A R x y. 
Proof.
  induction 1. 
  intuition.
  inversion IHclos_refl_trans_n1. 
  right. subst. econstructor; eauto. 
  right. subst. eapply tn1_trans; eauto. 
Qed.
