Require Import sdf_definition.
Require Import List.
Require Import Arith.
Require Import Program.


Module Type Nabl_Sig (s : Sdf_Sig).

Module Term := Sdf_Term s.
Export Term.

(* The set of namespaces (eg for java method, variable field ... are in different namespaces)*)
Parameter NS : Set.

(* scopes_R t ns decide if term t scopes the namespace ns (eg in NABL : Class(_,_,_,_,_) scopes Method)*)
Parameter scopes_R : term -> NS -> Prop.

(* defines_R t x ns k decide if term t defines the variable x from namespace ns 
in the scope k (k is the key corresponding to the node Id x k that is a subterm of t) 
(eg in NABL (defines Method m ) *)
Parameter defines_R : term -> Ident -> NS -> key -> Prop.

(* refers_to_R t x ns k decide if term t refers to the variable x from namespace ns 
(k is the key corresponding to the node Id x k that is (likely) a subterm of t) 
(eg in NABL (Var(y) refers to Variable x ) *)
Parameter refers_to_R : term -> Ident -> NS -> key -> Prop.

End Nabl_Sig.

Module Nabl_wf (s : Sdf_Sig) (nas : Nabl_Sig s). 

Export nas.

Section With_main_program.
        
    Variable t : term.
    Variable wft : wf_term Main_Sort t.
    Variable def_of : key -> key -> Prop.

    Delimit Scope term_scope with term.
    Bind Scope term_scope with term.
    Notation " @ x " := (get x t) (at level 20) : term_scope.
    Notation " x |-> y " := (def_of x y) (at level 20) : term_scope.
    Notation " y @ x " := (@ x = Some y) (at level 19) : term_scope.

    Lemma at_inj : forall x y z, x @ z -> y @ z -> x = y.
    Proof. 
      intros.
      rewrite H in *; inversion H0; eauto.
    Qed.

    (* greatest lower scoping bound *)

    Lemma dir_prefix_nil : forall k, ~ k <d< nil.
      Proof.
        intros.
        intro.
        inversion H.
        discriminate H0.
      Qed.
        
    Lemma prefix_nil : forall k, ~ k << nil.
      Proof.
        intros.
        intro.
          dependent induction H.
          apply (dir_prefix_nil _ H).
          destruct H.
          discriminate H.
      Qed.

    Lemma prefix_refl_nil : forall k, k <<* nil -> k = nil.
      Proof.
        intros.
          dependent induction H.
          reflexivity.
          contradiction (dir_prefix_nil) with y.
      Qed.

    Lemma prefix_nil_forall : forall k, nil <<* k.
      Proof.
        induction k.
        apply rtn1_refl.
        apply (Relation_Operators.rtn1_trans) with k.
        exists a. reflexivity.
        eauto.
      Qed.
      
    Definition valid k := exists t0, @ k = Some t0.

    Definition valid_t := forall k t1, t1 @ k -> k = t1 'k.    

    Lemma val_subterm_aux : 
      valid_t ->
      forall c lp k,
        (Co c lp k) @ k ->
        forall p, (exists n, nth_error lp n = Some p) -> p @ (p 'k). 
    Proof.
      intro.
      intros.
      destruct H1.
      assert (p @ (x::k)).
      simpl. 
      rewrite H0.
      eauto.
      rewrite <- (H _ p H2).
      eauto.
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

    Lemma val_subterm :
      valid_t ->
      forall c lp k,
        (Co c lp k) @ k ->
        Forall (fun p => p @ (p 'k)) lp. 
    Proof.
      intros.
      rewrite Forall_forall.
      intros.
      rewrite in_nth in H1 .
      apply val_subterm_aux with c lp k; eauto.
    Qed.

    Lemma valid_nil : valid nil.
      Proof.
        unfold valid.
        exists t.
        unfold get. eauto.
      Qed.



    Lemma prefix_refl_add : forall k1 k2, k1 <<* k2 <-> exists k, k ++ k1 = k2. 
    Proof.
      intros k2 k0; generalize k2.
      induction k0.
      * intros.
        split; intros.
        + exists (nil : key).
          simpl.
          apply prefix_refl_nil.
          eauto.
        + destruct H.      
          unfold app in H.
          destruct x.
          subst.
          apply rtn1_refl.
          inversion H.
      * split; intros.
        inversion H.
        - exists (nil : key).
          simpl.
          reflexivity.
        - unfold direct_prefix in H0.
          destruct H0.
          inversion H0.
          subst.
          specialize (IHk0 k3).
          rewrite IHk0 in H1.
          destruct H1.
          subst.
          exists (a::x).
          eauto.
        - destruct H.
          destruct x.
          simpl in H.
          subst.
          apply rtn1_refl.
          inversion H.
          destruct (IHk0 k3).
          subst.          
          apply (Relation_Operators.rtn1_trans) with (x ++ k3).
          exists a.
          eauto.
          apply H3.
          exists x.
          reflexivity.
    Qed.
      

    Lemma prefix_add : forall k1 k2, k1 << k2 <-> exists a k, a:: k ++ k1 = k2. 
    Proof.
      intros k2 k0; generalize k2.
      induction k0.
      * intros.
        split; intros.
        + contradiction (prefix_nil _ H).
        + destruct H.      
          destruct H.
          inversion H.
       * split; intros.
         + inversion H.
           - unfold direct_prefix in H0.
             destruct H0.
             inversion H0.
             subst.
             exists a (nil : key).
             eauto.
           - unfold direct_prefix in H0.
             destruct H0.
             inversion H0.
             subst.
             specialize (IHk0 k3).
             rewrite IHk0 in H1.
             destruct H1 as [a1 [k eqa]].
             subst.
             exists a (a1::k).
             eauto.
        + destruct H as [a1 [k1 eqa]].
          destruct k1.
          simpl in eqa.
          rewrite <- eqa. 
          apply tn1_step.
          exists a1.
          reflexivity.
          inversion eqa.
          destruct (IHk0 k3).
          subst.          
          apply (Relation_Operators.tn1_trans) with (n :: k4 ++ k3).
          exists a.
          eauto.
          apply H2.
          exists n k4.
          reflexivity.
    Qed.
         Print Scopes.

    Definition irreflexive {A} (R : A -> A -> Prop) := forall x, ~ R x x.  

    Lemma irreflexive_prefix : irreflexive prefix. 
      intro.
      intro.
      rewrite (prefix_add _ _) in H.
      destruct H as [a [k keq]].
      induction x.
      discriminate keq. 
      inversion keq.
      assert (a::k = nil).
      apply (app_inv_tail (a0::x) (a::k) nil).
      eauto.
      discriminate H.
    Qed.

    Lemma valid_pre : forall k1 k2, valid k2 -> k1 <<* k2 -> valid k1. 
    Proof.
      intros k1 k2; generalize k1; induction k2.
      * intros.
        rewrite (prefix_refl_nil _ H0).
        exact valid_nil.
      * intros.
        rewrite prefix_refl_add in H0.
        destruct H0.
        destruct x.
        simpl in H0.
        subst; eauto.
        apply IHk2.
        unfold valid in H.
        simpl in H.
        unfold valid.
        destruct H.
        destruct (@ k2).
        exists t0; eauto.
        discriminate.
        rewrite prefix_refl_add.
        inversion H0.
        exists x; eauto.
    Qed.

    
    Inductive scope_of : key -> NS -> key -> Prop :=
(*     | Scope_of_nil ns : scope_of nil ns nil  (* APT: This clause seems surprising; really doesn't seem needed *) *)
    | Scope_of_scope n k t1 ns:  
        (t1 @ k /\ scopes_R t1 ns) ->
        valid (n::k) ->
        scope_of (n::k) ns k
    | Scope_of_trans n k t1 ns ks :
        (t1 @ k /\ ~ scopes_R t1 ns) ->
        scope_of k ns ks ->
        valid (n::k) ->
        scope_of (n::k) ns ks
    .

    Definition scope_of_bis k1 ns k2 :=
      valid k1 (* APT: added this for the proof that follows *) /\  
      k2 << k1 /\ 
      (exists t1, ( t1 @ k2 /\ scopes_R t1 ns )) /\ 
      forall k, k2 <<* k -> k << k1 -> (exists t1, (t1 @ k /\ scopes_R t1 ns)) -> k2 = k. 


    (* APT: A little experiment to check definition compatibility. *)    

    Ltac inv H := inversion H; subst; clear H. 

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
      inv IHclos_refl_trans_n1. 
        right. econstructor; eauto. 
        right. eapply tn1_trans; eauto. 
    Qed.

    Lemma bis_implies: forall k1 ns k2, scope_of_bis k1 ns k2 -> scope_of k1 ns k2. 
    Proof.
      intros. generalize dependent k2. induction k2; intros. 
      unfold scope_of_bis in H.  destruct H as (P0 & P1 & (t1 & Q1 & Q2) & P3).  
      exfalso. eapply prefix_nil; eauto.
      unfold scope_of_bis in H.  destruct H as (P0 & P1 & (t1 & Q1 & Q2) & P3). 
      inversion P1. subst. inv H. inv H0. 
      + eapply Scope_of_scope. split; eauto. auto.
      + subst. assert (scope_of_bis k2 ns k0). 
      { unfold scope_of_bis.  split. 
        eapply valid_pre. eauto. econstructor. econstructor. eauto. econstructor. split.
        inv H. inv H1. auto.  split. 
        econstructor; eauto. 
        intros. eapply P3; eauto. unfold prefix in H2|-*.
        eapply tn1_trans.  econstructor; eauto.  eauto. }
      assert (valid k2).  
      {eapply valid_pre. eauto. eapply rtn1_trans with k2. econstructor; eauto.
       eapply rtn1_refl. }
      destruct H2 as [t2 R]. 
      eapply Scope_of_trans; eauto.
      split; eauto. 
      intro. 
      assert (k0 = k2).
      { eapply P3. 
        - inv P1. 
          +  inv H3.  inv H4. eapply rtn1_refl. 
          +  inv H3.  inv H5.  eapply Operators_Properties.clos_rt_rtn1_iff. 
             eapply Operators_Properties.clos_rtn1_rt.
             eapply tn1_rtn1; eauto. 
        - unfold prefix. eapply tn1_step. econstructor. eauto.
        - exists t2.  intuition.  }
      subst.  
      inv H. inv H3. apply (irreflexive_prefix _ H0). 
    Qed.

    Lemma implies_bis: forall k1 ns k2, scope_of k1 ns k2 -> scope_of_bis k1 ns k2. 
      Proof.
        intros. unfold scope_of_bis. induction H. 
        + split. auto. split. eapply tn1_step. econstructor; eauto. split.
          eexists; eauto.
          intros. 
          inv H2. inv H4. inv H2. auto.
          inv H4. inv H2. 
          inv H1.  auto. 
          exfalso. assert (k0 << k0). 
          {  apply rtn1_tn1 in H4. inv H4. 
             - eapply tn1_trans; eauto. 
             - eapply tn1_trans; eauto.  eapply Operators_Properties.clos_trans_tn1. 
                 eapply t_trans; eapply Operators_Properties.clos_tn1_trans; eauto.  }
          eapply irreflexive_prefix; eauto.
        + destruct IHscope_of as (P1 & P2 & (ts & P3 & P4) & P5). split. auto. split.
          eapply tn1_trans with k.  econstructor; eauto. eauto. split.
          exists ts; intuition.
          intros. 
          inv H3. inv H5. inv H3. 
            destruct H4 as (t1' & R1 & R2). 
            destruct H as (R3 & R4).
            rewrite R3 in R1.  inv R1. contradiction.
            inv H5. inv H3. eauto.
      Qed.

    (* End of experiment. *)

    Definition mightreach kr kd ks ns :=
      scope_of kd ns ks /\ ks << kr. 

    Definition reaches kr x ns ksm kdm tdefm kdixm := 
          tdefm @ kdm /\
          defines_R tdefm x ns kdixm /\
          mightreach kr kdm ksm ns /\
    (* any other definition of x is out of ksm *)
          forall ks' kd' tdef' kdix', 
            tdef' @ kd' ->
            defines_R tdef' x ns kdix' -> 
            mightreach kr kd' ks' ns ->
            (ks' << ksm \/
            (* this avoids duplicate definition *)
            (ksm = ks' /\ kdm = kd')).
 
    Definition map_sound_def :=
      forall kx kdx, 
        kx |-> kdx ->
        exists x, 
          (* source of mapping is an identifier *)
          (Id x kx) @ kx /\ 
          (* target is a definition node *)
            exists ns tdef kdix, 
            tdef @ kdx /\
            defines_R tdef x ns kdix /\ 
            (* all the refers to this variable are reachable from kdx
               maybe add the all the refers to are done with same NS *)
            forall kr tr, 
              tr @ kr ->
              refers_to_R tr x ns kx  ->
              exists ks, reaches kr x ns ks kdx tdef kdix.

    (* ~ well ordered set (every non empty set has an upper bound *)

    Definition exists_reaches :=
      forall kr kd ks ns x kdix tdef,
        tdef @ kd ->
        mightreach kr kd ks ns ->
        defines_R tdef x ns kdix -> 
        exists ksm kdm tdefm kdixm, 
          reaches kr x ns ksm kdm tdefm kdixm.

    Lemma unique_reaches : 
      forall kr x ns ksm1 kdm1 tdefm1 kdixm1 ksm2 kdm2 tdefm2 kdixm2,
        reaches kr x ns ksm1 kdm1 tdefm1 kdixm1 ->
        reaches kr x ns ksm2 kdm2 tdefm2 kdixm2 ->
        ksm1 = ksm2 /\ kdm1 = kdm2 /\ tdefm1 = tdefm2.
    Proof.
      intros.
      destruct H as [at1 [def1 [rea1 min1]]].
      destruct H0 as [at2 [def2 [rea2 min2]]].
      specialize (min1 _ _ _ _ at2 def2 rea2).
      specialize (min2 _ _ _ _ at1 def1 rea1).
      destruct min1.
      destruct min2.
      contradiction (irreflexive_prefix ksm1).
      rewrite <- (Operators_Properties.clos_trans_tn1_iff _ direct_prefix) in *.
      apply t_trans with ksm2; assumption.
      intuition.
      subst.
      apply at_inj with kdm1; assumption.
      intuition.
      subst.
      apply at_inj with kdm2; assumption.
      rewrite H1 in *.
      apply at_inj with kdm2; assumption.
    Qed.

    Definition map_complete :=
      forall tref kr, 
        tref @ kr ->
        forall x ns kx,
          refers_to_R tref x ns kx ->
          exists kdef, 
            kx |-> kdef
    .


    Record valid_term_map := 
      mkvalid { 
          vt : valid_t;  
          ms : map_sound_def; 
          mc : map_complete 
        }. 

(*undef : exists_reaches;*)


    Variable valt : valid_term_map.

    (* General lemmas on terms *)

 
    Lemma get_par : 
      forall a k te, 
        te @ (a::k) ->
        exists c lp, Co c lp k @ k /\ In te lp.
    Proof.
      intros.
      simpl in H.
      set (ot := @ k); assert (ot = @ k);  eauto.
      destruct ot.
      destruct t0.
      exists c l.
      pose proof (vt valt).
      unfold valid_t in H1.
      symmetry in H0.
      specialize (H1 _ _ H0).
      simpl in H1.
      split.
      subst; eauto.
      rewrite H0 in H.
      pose proof (in_nth l).
      rewrite H2.
      exists a.
      eauto.
      rewrite <- H0 in H.
      simpl in H.
      destruct a; simpl in H; discriminate H.
      rewrite <- H0 in H.
      discriminate H.
    Qed.
    
    Lemma wf_at : 
      forall k te, 
        te @ k -> exists s, wf_term s te.
    Proof.
      pose proof wft.
      induction k.
      simpl; intros; inversion H0; exists Main_Sort; subst; eauto.
      intros.
      pose proof (get_par _ _ _ H0).
      destruct H1 as [c [lp att]].
      specialize (IHk _ (proj1 att)).
      destruct IHk.
      inversion H1.
      subst.
      destruct att.
      clear - rec H3.
      generalize rec.
      clear rec.    
      generalize ar.
      clear ar.
      generalize H3.
      clear H3.
      induction lp.
      intros.
      simpl in H3. contradiction H3.
      intros.
      destruct H3.
      subst.
      intros.
      inversion rec.
      subst.
      exists x; eauto.
      inversion rec.
      subst.
      apply IHlp with l; assumption.
    Qed. 


    Lemma child_cons : 
      forall e k n,
        e @ (n::k) ->
        forall c lp, (Co c lp k) @ k -> In e lp.
    Proof.
      intros.
      simpl in H.
      rewrite H0 in *.
      simpl in H.
      rewrite in_nth. 
      exists n.
      eauto.
    Qed.
    

    Lemma params_sup : 
      forall te e, 
        te @ (te 'k) ->
        In e (te 'args) ->
        e @ (e 'k) /\ te 'k <d< (e 'k). 
    Proof.
      intros.
      rewrite (in_nth (te 'args) e) in H0.
      destruct H0.
      assert (e @ (x::(te 'k))).
      simpl.
      rewrite H.
      assumption.
      pose proof (vt valt _ _ H1).
      rewrite <- H2.
      split; intuition.
      exists x; reflexivity.
    Qed.

    End With_main_program.

End Nabl_wf.