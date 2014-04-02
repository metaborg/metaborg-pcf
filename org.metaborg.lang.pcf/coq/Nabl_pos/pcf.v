Require Import Program.
Require Import Lists.List.
Require Import Peano_dec.
Require Import sdf_definition.
Require Import nabl_def.
Require Import Relation_Operators.
Require Import ts_nabl.
Require Import aux_lemmas.


(* INstantiation of the syntax definition of PCF *)

Module sdf_PCF <: Sdf_Sig.

  Inductive sorts := 
  | ID_S 
  | Term_S
  | Param_S
  | Type_S
  .
  Definition sort := sorts.
  Definition Ident_Sort := ID_S.

  Definition Ident := nat.
  Definition id_eq_dec := eq_nat_dec.


  Lemma sort_eq_dec : forall (x y : sort), {x=y} + {x <> y}.
  Proof.
    induction x; destruct y; 
    first [ left; reflexivity | (right; discriminate) ].
  Qed.


  Inductive Constructors :=
  | TNatC
  | TBoolC  (* APT: added for examples *) 
  | TFunC
  | VarC
  | LamC
  | FixC
  | AppC 
  | NatC (n :nat)
  | BoolC (b : bool)  (* APT: added for examples *) 
  | IfzC 
  (*| LetC *)
  | PlusC
  | TimesC
  | ParamC
  .

  Definition constructors := Constructors.

  Definition key := list nat.
  Definition k1 := [0]. 

  Fixpoint get_sig sc : list sort * sort :=
    match sc with
      | TNatC => ([],Type_S)
      | TBoolC => ([],Type_S)   (* APT *) 
      | TFunC => ([Type_S; Type_S], Type_S)
      | VarC => ([ID_S],Term_S)
      | LamC => ([Param_S; Term_S],Term_S)
      | FixC => ([Param_S; Term_S],Term_S)
      | AppC => ([Term_S; Term_S],Term_S)
      | NatC n => ([],Term_S)
      | BoolC b => ([],Term_S)    (* APT *) 
      | IfzC => ([Term_S; Term_S; Term_S],Term_S)
      | PlusC => ([Term_S;Term_S],Term_S)
      | TimesC => ([Term_S;Term_S],Term_S)
      | ParamC => ([ID_S;Type_S], Param_S)
    end. 

  Definition signature c ls s := get_sig c = (ls,s).

  Definition Main_Sort := Term_S.

End sdf_PCF.


Module nabl_PCF <: Nabl_Sig (sdf_PCF).

  Module Term := Sdf_Term sdf_PCF.
  Export Term.
  
  Set Printing Projections.

  Inductive ID_NS :=
  | VarNS 
  .

  Definition NS := ID_NS.
  Lemma id_eq_dec : forall (x y : NS), {x=y} + {x <> y}.
  Proof.
    induction x; destruct y; 
    first [ left; reflexivity | (right; discriminate)]. 
  Qed.


  Inductive scopesR : term -> NS -> Prop :=
  | Lam_scopes_Var lp k : scopesR (Co LamC lp k) VarNS 
  | Fix_scopes_Var lp k : scopesR (Co FixC lp k) VarNS 
  .
  Definition scopes_R := scopesR.

  Inductive definesR : term -> Ident -> NS -> key -> Prop :=
  | Param_defines_Var x t k kt : 
      definesR (Co ParamC ((Id x k)::t) kt) x VarNS k 
  .
  Definition defines_R := definesR.

  Inductive refers_toR : term -> Ident -> NS -> key -> Prop :=
  | Var_refers_Var x lp k kt : 
      refers_toR (Co VarC ((Id x k)::lp) kt) x VarNS k 
  .
  Definition refers_to_R := refers_toR.

End nabl_PCF.

(* TS definitions of PCF *)

Module ts_PCF. 


  Module nabl_pcf_mod := nabl_PCF. 
(*  Export nabl_PCF.
*)
  Module nabl_wf_mod := Nabl_wf sdf_PCF nabl_pcf_mod. 
  Export nabl_wf_mod.

  Definition type_sort := Type_S.

  Inductive typed_defines_R : term -> Ident -> NS -> term -> key -> Prop :=
  | Param_types_defines_Var x ty k kt :     
      typed_defines_R (Co ParamC [(Id x k);ty] kt) x VarNS ty k 
  . 

  Lemma typed_def_unique : forall tt id ns ty1 ty2 k1 k2, typed_defines_R tt id ns ty1 k1 -> typed_defines_R tt id ns ty2 k2 -> ty1 = ty2 /\ k1 = k2.
  Proof.
    intros.
    inversion H.
    subst.
    inversion H0; subst.
    eauto.
  Qed.

  Definition typed_definesR := typed_defines_R.
  
End ts_PCF.


Module sem_PCF.

  Module nabl_pcf_mod := nabl_PCF. 
  Module ts_pcf_mod := ts_PCF. 

  Module ts_wf := TS_NaBL_def sdf_PCF nabl_pcf_mod ts_pcf_mod. 
  Import ts_wf.

  (* Some inversion tactics *)

  Ltac r_clear_rl e := try (rewrite <- e in *); try clear e.  
  Ltac r_clear_lr e := try (rewrite e in *); try clear e.  

  Ltac inversion_typed_def td :=
    let x := fresh "x" in 
    let ty := fresh "ty" in 
    let k := fresh "k" in 
    let kt := fresh "kt" in 
    let xeq := fresh "xeq" in 
    let teq := fresh "teq" in 
    let tyeq := fresh "tyeq" in 
    let keq := fresh "keq" in 
    let nseq := fresh "nseq" in 
    inversion td as [x ty k kt teq xeq nseq tyeq keq];
      r_clear_rl teq; r_clear_lr xeq; r_clear_lr tyeq; r_clear_lr nseq; r_clear_lr keq;
      clear x ty k.

  Ltac inv_wft_Co wft rec :=
    let s := fresh "s" in
    let sc := fresh "sc" in
    let lp := fresh "lp" in
    let k := fresh "k" in
    let ar := fresh "ar" in
    let sg := fresh "sg" in
    let eq1 := fresh "eq" in
    let eq2 := fresh "eq" in
    let eq3 := fresh "eq" in
    let eq4 := fresh "eq" in
    inversion wft as [s sc lp k ar sg rec eq1 [eq2 eq3 eq4] | ];
      clear eq1 eq2 eq3 eq4;
      unfold signature in sg; simpl in sg;
      let areq := fresh "areq" in
      let seq := fresh "seq" in 
      first 
        [injection sg as seq areq; r_clear_rl seq; r_clear_rl areq; clear sg |
         injection sg as areq; r_clear_rl areq; clear sg];
        clear s sc lp k ar.

  Ltac inv_wft_cons wfl wfl1:=  
    let x1 := fresh "x" in
    let l1 := fresh "x" in
    let x2 := fresh "x" in
    let l2 := fresh "x" in
    let wft := fresh "wft" in
    let eq1 := fresh "eq" in
    let eq2 := fresh "eq" in
    let eq3 := fresh "eq" in
    let eq4 := fresh "eq" in
    inversion wfl as [|x1 l1 x2 l2 wft wfl1 [eq1 eq2] [eq3 eq4]];
      clear eq1 eq2 eq3 eq4 x1 l1 x2 l2.

  (* inversion of a well_formed term (for which we know the constructor) *)

  Ltac invCo wft := 
    let wfl := fresh "wfl" in
    inv_wft_Co wft wfl;
      let rec rep ls :=
          match type of ls with
            | Forall2 wf_term (?a::?q) _ => 
              let wfl := fresh "wfl" in 
              inv_wft_cons ls wfl; clear ls; try (rep wfl)
            | Forall2 wf_term [] _ => try (clear ls)
          end
      in rep wfl
  .

  Section With_term.

    (* we assume a well formed term with a valid mapping *)

    Variable t : term.
    Variable wft : wf_term Main_Sort t.
    Variable def_of : key -> key -> Prop.
    Variable valt : valid_term_map t def_of.    

    Delimit Scope term_scope with term.
    Bind Scope term_scope with term.
    Notation " @ x " := (get x t) (at level 20) : term_scope.
    Notation " x |-> y " := (def_of x y) (at level 20) : term_scope.
    Notation " y @ x " := (@ x = Some y) (at level 19) : term_scope.


    (* Type_define relation define terms of type type_sort*)

    Lemma typed_defines_types : 
      forall id NS ty k s, wf_term s t -> typed_definesR t id NS ty k -> wf_term Type_S ty.  
    Proof.
      intros id NS ty k s wft0 td.
      inversion_typed_def td.
      invCo wft0.
      assumption.
    Qed.


    (* A term is well_formed for a unique sort *)

    Lemma wf_unique : 
      forall e s1 s2,
        wf_term s1 e ->
        wf_term s2 e ->
        s1 = s2.
    Proof.
      intros.
      inversion H; subst; inversion H0.
      subst.
      unfold signature in *.
      rewrite sg0 in sg.
      inversion sg.
      subst; reflexivity.
      reflexivity.
    Qed.


    (* Definition of PCF type checking according to TS language well_typed_infer C t ty means C |- t : ty 
last case is the equality modulo key if c |- t : ty1 and ty1 ~t ty2 then c |- t : ty2 *)
    
    Inductive well_typed_infer : term -> term -> Prop :=
    | VarC_wt x k kt ty : 
        lookup t def_of x VarNS k ty ->
        well_typed_infer (Co VarC [Id x k] kt) ty
    | LamC_wt p e ty1 ty2 k kt:
        well_typed_infer p ty1 ->
        well_typed_infer e ty2 ->
        well_typed_infer (Co LamC [p;e] k) (Co TFunC [ty1;ty2] kt) 
    | FixC_wt p e ty k:
        well_typed_infer p ty ->
        well_typed_infer e ty ->
        well_typed_infer (Co FixC [p;e] k) ty
    | AppC_wt e1 e2 ty1 ty2 k kt:
        well_typed_infer e1 (Co TFunC [ty1;ty2] kt) ->
        well_typed_infer e2 ty1 ->
        well_typed_infer (Co AppC [e1;e2] k) ty2
    | NatC_wt n k kn : well_typed_infer (Co (NatC n) [] k) (Co TNatC [] kn)
    | BoolC_wt n k kn : well_typed_infer (Co (BoolC n) [] k) (Co TBoolC [] kn)  (* APT *)
    | IfzC_wt e1 e2 e3 ty kn kt:
        well_typed_infer e1 (Co TNatC [] kn) ->
        well_typed_infer e2 ty ->
        well_typed_infer e3 ty ->
        well_typed_infer (Co IfzC [e1;e2;e3] kt) ty
    | PlusC_wt e1 e2 kn1 kn2 kt : 
        well_typed_infer e1 (Co TNatC [] kn1) ->
        well_typed_infer e2 (Co TNatC [] kn2) ->
        well_typed_infer (Co PlusC [e1;e2] kt) (Co TNatC [] kn1)  
    | TimesC_wt e1 e2 kn1 kn2 kt : 
        well_typed_infer e1 (Co TNatC [] kn1) ->
        well_typed_infer e2 (Co TNatC [] kn2) ->
        well_typed_infer (Co TimesC [e1;e2] kt) (Co TNatC [] kn1)  
    | ParamC_wt e ty k : well_typed_infer (Co ParamC [e;ty] k) ty 
    | WT_eq tt ty1 ty2 
            (wty1 : well_typed_infer tt ty1)
            (tyeq : ty1 ~t ty2) :
        well_typed_infer tt ty2
    .


    (* The call by name definition of PCF semantics*)


    (* in call by name the environment is a mapping from identifier to pairs (term * environment) *)

    Inductive Env := 
    | Cons_Env : (Ident -> option (term * Env)) -> Env   
    .
    Definition Nenv := Cons_Env (fun x => None).
    Definition get_e x env :=
      match env with Cons_Env m => m x end.
    
    Definition env_extend (env : Env) x t :=
      Cons_Env (fun z => if x == z then Some t else get_e z env).

    Definition env_remove (env : Env) x :=
      Cons_Env (fun z => if x == z then None else get_e z env).


    (* a value is a nat, a bool, or a closure *)

    Inductive value :=
    | Natval (n : nat)
    | Boolval (b : bool) (* APT *) 
    | Clos (v : Ident) (t : term) (e : Env)
    .    

    Coercion Natval : nat >-> value.
    Coercion Boolval : bool >-> value. (* APT *) 

    (* Notations similar to spoofax ones *)
    Delimit Scope spoofax_scope with spfx.
    Bind Scope spoofax_scope with term.
    Notation " { a |--> t , env }" := (env_extend env a t) : spoofax_scope. 
    Notation " C |- t : ty " := (well_typed_infer C t ty) (at level 20) : spoofax_scope.
    Open Scope spoofax_scope.

    (* a lookup in the semantics environment *)
    
    Inductive get_env x : Env -> term -> Env -> Prop :=
    | get_env_C t te c: 
        c x = Some (t,te) ->
        get_env x (Cons_Env c) t te
    .

    (* Definition of the semantics, direct translation of dynsem rules,
   natural number arithmetic is represented with Coq natural numbers.
     *)

    Inductive semantics_cbn : Env -> term -> value -> Prop :=
    | VarC_sem x t k kt env va nenv  : 
        get_env x env t nenv ->
        semantics_cbn nenv t va ->            
        semantics_cbn env (Co VarC [Id x k] kt) va 
    | LamC_sem x kx t kp e kt env:
        semantics_cbn env (Co LamC [(Co ParamC [Id x kx;t] kp);e] kt) (Clos x e env) 
    | FixC_sem x t e kx kp kt v env:
        semantics_cbn { x |--> (Co FixC [(Co ParamC [Id x kx;t] kp);e] kt,env), env} e v ->
        semantics_cbn env (Co FixC [(Co ParamC [Id x kx;t] kp);e] kt) v
    | AppC_sem e1 e2 v e x env nenv k :
        semantics_cbn env e1 (Clos x e nenv) ->
        semantics_cbn { x |--> (e2,env), nenv} e v ->
        semantics_cbn env (Co AppC [e1;e2] k) v
    | NatC_sem n k e : semantics_cbn e (Co (NatC n) [] k) (Natval n)
    | BoolC_sem b k e : semantics_cbn e (Co (BoolC b) [] k) (Boolval b) (* APT *) 
    | IfzC_sem0 e1 e2 e3 env kt v :
        semantics_cbn env e1 (Natval 0) ->
        semantics_cbn env e2 v ->
        semantics_cbn env (Co IfzC [e1;e2;e3] kt) v
    | IfzC_semS e1 e2 e3 env kt v n :
        semantics_cbn env e1 (Natval (S n)) ->
        semantics_cbn env e3 v ->
        semantics_cbn env (Co IfzC [e1;e2;e3] kt) v
    | PlusC_sem e1 e2 env m n kt: 
        semantics_cbn env e1 (Natval n) ->
        semantics_cbn env e2 (Natval m) ->
        semantics_cbn env (Co PlusC [e1;e2] kt) (m + n)  
    | TimesC_sem e1 e2 env m n kt: 
        semantics_cbn env e1 (Natval n) ->
        semantics_cbn env e2 (Natval m) ->
        semantics_cbn env (Co TimesC [e1;e2] kt) (m * n) 
    .


    Notation " env |- t --> v " := (semantics_cbn env t v) (at level 20) : spoofax_scope.

    

    (* for type preservation with environments and not substitution we have to maintain a property on the 
   term we store, that is:
   "" the type of the term associated to x in the semantics environment is the same as the type of x "" 
     *)

    (* the type of a variable at a particular position *)

    Definition type_at k x ns ty := 
      exists kdef tdef kdix ks, 
        reaches t k x ns ks kdef tdef kdix /\ 
        typed_definesR tdef x ns ty kdix.

    (* Define a well typed environment *)

    Inductive compatible_env ns : key -> Env -> Prop :=
    | Compat_env k e :
        (forall x tr te,
           get_env x e tr te ->
           compatible_env ns (tr 'k) te /\
           wf_term Term_S tr /\
           tr @ (tr 'k) /\
           exists ty,
             type_at k x ns ty /\
             well_typed_infer tr ty) -> compatible_env ns k e.

    (* Define the type of a value *)

    Inductive type_value : value -> term -> Prop :=
    | Natval_type n k : 
        type_value (Natval n) (Co TNatC [] k)
    | Boolval_type b k :  (* APT *)
        type_value (Boolval b) (Co TBoolC [] k)
    | Clos_val_type x t env tyx ty k 
                    (wfntt : wf_term Term_S t) 
                    (wtyt : well_typed_infer t ty)
                    (subterm : t @ (t 'k) ) 
                    (compenv : compatible_env VarNS (t 'k) (env_remove env x))
                    (vist :  type_at (t 'k) x VarNS tyx)
      : type_value (Clos x t env) (Co TFunC [tyx;ty] k)  

    (* equivalence of type case (keys do not matter in types) *)

    | Type_value_eq v t1 t2 :
        type_value v t1 ->
        t1 ~t t2 ->
        type_value v t2 
    .
    
    (* first trivial lemma, I say that by using the get_env function on a compatible environment I get all the corresponding properties; induction on the compatible_get property *)

    Lemma compatible_get : 
      forall ns k env x tr te, 
        get_env x env tr te ->
        compatible_env ns k env ->
        exists ty,  
          compatible_env ns (tr 'k) te /\
          type_at k x ns ty /\
          wf_term Term_S tr /\ 
          tr @ (tr 'k) /\
          well_typed_infer tr ty .
    Proof.    
      intros ns k env x t0 te ge comp.
      destruct comp.
      destruct (H _ _ _ ge) as [cp [wft0 [att [ty [typ wt]]]]].
      exists ty.
      eauto.
    Qed.

    (* if a term is a constructor with well formed children, their sort is in the signature of the constructor*)

    Lemma sort_in_sig : 
      forall e k n,
        e @ (n::k) ->
        forall c lp, (Co c lp k) @ k ->
                     forall s, wf_term s e -> In s (fst (get_sig c)).
    Proof.
      intros.
      assert (In e lp).
      apply (child_cons _ _ _ _ H _ _ H0).
      pose proof (wf_at _ wft def_of valt _ _ H0).
      destruct H3.
      inversion H3.
      subst.
      unfold signature in sg.
      rewrite sg.
      simpl.
      destruct (Forall2_exists_r _ _ _ rec _ H2).
      destruct H4.
      rewrite (wf_unique _ _ _ H1 H5).
      assumption.
    Qed.

    (* The type of a param is equivalent to the one declared *)

    Lemma type_param_eq :
      forall x tx k ty, well_typed_infer (Co ParamC [x;tx] k) ty -> tx ~t ty.
    Proof.
      intros.
      clear wft valt.
      dependent induction H.
      reflexivity.
      apply transitivity with ty1; intuition.
    Qed.

    (* a Param is a child of Fix or Lam *)

    Lemma param_in_fun_fix : 
      forall c, 
        In Param_S (fst (get_sig c)) ->
        c = LamC \/ c = FixC.
    Proof.
      induction c;
      intros inp;
      simpl in inp;
      intuition; try (discriminate).
    Qed.


    Lemma defsc_is_fix_or_fun :
      forall te x kd k, 
        te @ (te 'k) ->
        defines_R te x VarNS kd ->
        scope_of t (te 'k) VarNS k ->
        exists e, (Co LamC [te;e] k) @ k \/  (Co FixC [te;e] k) @ k.
    Proof.
      intros.
      inversion H0.
      subst.
      inversion H1; subst.
      (*    - rewrite <- H2 in *.
      simpl in H.
      inversion H.
      pose proof wft.
      unfold Main_Sort in H3.
      rewrite H4 in H3.
      inversion H3.
      unfold signature in sg.
      simpl in sg.
      inversion sg. *)
      - destruct H2.
        inversion H5.
        + subst.
          simpl in H.
          simpl in H4.
          subst.
          destruct ( wf_at _ wft def_of valt _ _ H2).
          inversion H4.
          subst.
          unfold signature in sg.
          simpl in sg.
          inversion sg.
          subst.
          inversion rec.
          inversion H10.
          inversion H15.
          subst.
          pose proof (vt _ _ valt _ _ H2).
          simpl in H6.
          rewrite <- H6 in *. clear H6.
          simpl in H.
          rewrite H2 in H.
          destruct n.
          * simpl in H.
            inversion H.
            subst.
            exists y0.
            left.
            assumption.
          * simpl in H.
            destruct n.
            simpl in H.
            inversion H.
            subst.
            inversion H13.
            unfold signature in sg0.
            simpl in sg0; discriminate.
            simpl in H.
            pose proof (in_nth [] (Co ParamC (Id x kd :: t0) (S (S n) :: k))).
            destruct H6.
            contradiction H7.
            exists n.
            assumption.
        + subst.
          simpl in H.
          simpl in H4.
          subst.
          destruct ( wf_at _ wft def_of valt _ _ H2).
          inversion H4.
          subst.
          unfold signature in sg.
          simpl in sg.
          inversion sg.
          subst.
          inversion rec.
          inversion H10.
          inversion H15.
          subst.
          pose proof (vt _ _ valt _ _ H2).
          simpl in H6.
          rewrite <- H6 in *. clear H6.
          simpl in H.
          rewrite H2 in H.
          destruct n.
          * simpl in H.
            inversion H.
            subst.
            exists y0.
            right.
            assumption.
          * simpl in H.
            destruct n.
            simpl in H.
            inversion H.
            subst.
            inversion H13.
            unfold signature in sg0.
            simpl in sg0; discriminate.
            simpl in H.
            pose proof (in_nth [] (Co ParamC (Id x kd :: t0) (S (S n) :: k))).
            destruct H6.
            contradiction H7.
            exists n.
            assumption. 
      - simpl in *.
        subst.
        destruct H2.
        pose proof (get_par _ def_of valt _ _ _ H).
        destruct H6 as [c [lp [coat inp]]].
        pose proof (sort_in_sig _ _ _ H _ _ coat).
        rewrite coat in *. 
        inversion H2.
        subst.
        pose proof (wf_at _ wft def_of valt _ _ H).
        destruct H7.
        inversion H7.
        unfold signature in *.
        simpl in sg; inversion sg. 
        subst.
        specialize (H6 _ H7). 
        pose proof (param_in_fun_fix _ H6).
        contradiction H5.
        destruct H8; subst; constructor.
    Qed.

    (* LamC does not modify the type of variable other than the bound one *)

    Lemma LamC_pres_type :
      forall k z ns ty,
        type_at k z ns ty ->
        forall x tyx e kp kx, 
          x <> z ->
          (Co LamC [Co ParamC [Id x kx;tyx] kp; e] k) @ k ->
          type_at (e 'k) z ns ty.
    Proof.
      intros.
      unfold type_at in *.
      destruct H as [kdef [tdef [kdx [ ks [ min tydef]]]]].
      unfold reaches in min.
      exists kdef tdef kdx ks.
      split; [| assumption].
      unfold reaches.
      destruct min.
      destruct H2.
      destruct H3.
      split; [assumption |].
      split; [assumption |].
      split.
      unfold mightreach.
      unfold mightreach in H3.
      destruct H3.
      split; [assumption |].
      apply tn1_trans with k; [| assumption].
      destruct (params_sup) with t def_of (Co LamC [Co ParamC [Id x kx; tyx] kp; e] k) e; intuition.
      simpl; intuition.
      intros.
      apply (H4 _ _ _ _ H5 H6).
      unfold mightreach in *.
      destruct H7.
      split; [assumption|].
      inversion H8.
      * unfold direct_prefix in H9.
        destruct H9.
        assert (ks' = k).
        pose proof (params_sup _ def_of valt (Co LamC [Co ParamC [Id x kx; tyx] kp; e] k)).
        simpl in H11.
        destruct (H11 e); intuition.
        rewrite <- H9 in H13.
        destruct H13.
        inversion H3.
        reflexivity.
        subst.
        destruct ns.
        pose proof (defsc_is_fix_or_fun).
        destruct (H10 tdef' z kdix' k).
        pose proof (vt _ _ valt _ _ H5).
        subst; assumption.
        assumption.
        pose proof (vt _ _ valt _ _ H5).
        subst. assumption.
        destruct H11.
        rewrite H1 in H11.
        inversion H11.
        subst.
        inversion H6.
        contradiction.
        rewrite H1 in H11.
        inversion H11.
      * unfold direct_prefix in H9.
        destruct H9.
        assert (y = k).
        pose proof (params_sup _ def_of valt (Co LamC [Co ParamC [Id x kx; tyx] kp; e] k)).
        simpl in H12.
        destruct (H12 e); intuition.
        rewrite <- H9 in H14.
        destruct H14.
        inversion H3.
        reflexivity.
        subst.
        assumption.
    Qed.


    (* LamC does not modify the type of variable other than the bound one *)

    Lemma FixC_pres_type :
      forall k z ns ty,
        type_at k z ns ty ->
        forall x tyx e kp kx, 
          x <> z ->
          (Co FixC [Co ParamC [Id x kx;tyx] kp; e] k) @ k ->
          type_at (e 'k) z ns ty.
    Proof.
      intros.
      unfold type_at in *.
      destruct H as [kdef [tdef [kdx [ ks [ min tydef]]]]].
      unfold reaches in min.
      destruct min.
      destruct H2.
      destruct H3.
      exists kdef tdef kdx ks.
      split; [| assumption].
      unfold reaches.
      split; [assumption |].
      split; [assumption |].
      split.
      unfold mightreach.
      unfold mightreach in H2.
      destruct H3.
      split; [assumption |].
      apply tn1_trans with k; [| assumption].
      destruct (params_sup) with t def_of (Co FixC [Co ParamC [Id x kx; tyx] kp; e] k) e; simpl; intuition.
      intros.
      apply (H4 _ _ _ _ H5 H6).
      unfold mightreach in *.
      destruct H7.
      split; [assumption|].
      inversion H8.
      * unfold direct_prefix in H9.
        destruct H9.
        assert (ks' = k).
        destruct params_sup with t def_of (Co FixC [Co ParamC [Id x kx; tyx] kp; e] k) e; intuition.
        simpl; intuition.
        destruct H12.
        simpl in H3.
        rewrite <- H3 in H9.
        inversion H9.
        reflexivity.
        subst.
        destruct ns.
        pose proof (defsc_is_fix_or_fun).
        destruct (H10 tdef' z kdix' k).
        pose proof (vt _ _ valt _ _ H5).
        subst; assumption.
        assumption.
        pose proof (vt _ _ valt _ _ H5).
        subst. assumption.
        destruct H11.
        rewrite H1 in H11.
        inversion H11.
        rewrite H1 in H11.
        inversion H11.
        subst.
        inversion H6.
        contradiction.
      * unfold direct_prefix in H9.
        destruct H9.
        assert (y = k).
        pose proof (params_sup t def_of valt (Co FixC [Co ParamC [Id x kx; tyx] kp; e] k)).
        simpl in H12.
        destruct (H12 e); intuition.
        rewrite <- H9 in H14.
        destruct H14.
        inversion H3.
        reflexivity.
        subst.
        assumption.
    Qed.


    (* no variable has a type at root position*)

    Lemma type_at_root_nil : 
      forall x ty ns, ~ type_at nil x ns ty.  
    Proof.
      intros.
      intro.
      unfold type_at in H.
      destruct H as [kdef [tdef [kdix [ks [mins tyd]]]]].
      unfold reaches in mins.
      intuition.
      unfold mightreach in H0.
      destruct H0.
      apply (prefix_nil _ H2).
    Qed.

    (* something that scope is a scope *)

    Lemma scope_of_scopes :
      forall k1 ns k2, 
        scope_of t k1 ns k2 ->
        forall t, t @ k2 -> scopes_R t ns .
    Proof.
      intros k1 ns1 ks2 scof.
      induction scof.
      (*     intuition. *)
      intros.
      rewrite H1 in H.
      destruct H.
      inversion H.
      subst.
      (* left; *) assumption.
      intros.
      apply IHscof; intuition.
    Qed.

    (* if a node doesn't scope, it pereserves envirnoment compatibility *)
    
    Lemma compatible_env_trans_no_scope : 
      forall t k1 x env ns, 
        t @ k1 ->
        compatible_env ns k1 env ->
        ~ scopes_R t ns -> 
        compatible_env ns (x::k1) env.
    Proof.
      intros.
      constructor.
      inversion H0.
      intros.
      destruct (H2 x0 tr te).
      assumption.
      intuition.
      destruct H10.
      destruct H9.
      exists x1.
      split; [| assumption].
      unfold type_at in *.
      destruct H9 as [kdef [tdef [kdix [ks [mins tyd]]]]] .
      exists kdef tdef kdix ks.
      split; [| assumption].
      unfold reaches.
      unfold reaches in mins.
      intuition.
      unfold mightreach in *.
      intuition.
      apply tn1_trans with k2.
      exists x; intuition.
      assumption.
      apply (H14 _ _ _ _ H13 H15).
      unfold mightreach in H16.
      unfold mightreach.
      clear - H16 H H1 H5 H0.
      destruct H16.
      split; [assumption|].
      inversion H3.
      destruct H4.
      inversion H4.
      subst.
      pose proof (scope_of_scopes(* _or_nil*) _ _ _ H2 _ H).
      contradiction (H1 H6).
      subst.
      inversion H4; subst; clear H4. inversion H7; subst; clear H7. 
      inversion H6; subst; clear H6.  eapply tn1_step; eauto.
      eapply tn1_trans; eauto.
    Qed.

    (* Nil is compatible at any position *)

    Lemma compatible_Nenv :
      forall ns k, compatible_env ns k Nenv.
    Proof.
      intros.
      constructor.
      intros.
      inversion H.
      discriminate H1.
    Qed.

    (* Main type preservation lemma, with generalization over terms and environment  *)

    Lemma type_preservation_aux :
      forall t0, 
        wf_term Term_S t0 ->
        t0 @ (t0 'k) ->
        forall env v, 
          semantics_cbn env t0 v ->
          forall ty,
            well_typed_infer t0 ty -> 
            compatible_env VarNS (t0 'k) env ->
            type_value v ty
    .
    Proof.
      intros t0 wft0 att env v sem.
      induction sem; intros.
      - destruct (compatible_get _ _ _ _ _ _ H H1 ) as [tyc [compenv [tyxk [wftc [tcat wtytc]]]]].
        rename H0 into wtyv; rename H1 into compenvv.
        dependent induction wtyv.
        * destruct H0.
          specialize (IHsem wftc tcat tyc wtytc compenv).
          simpl in tyxk.
          unfold type_at in tyxk.
          pose proof (ms _ _ valt).
          unfold map_sound_def in H0.
          destruct (H0 _ _ mpkd) as [x0 [x0at [ns1 [tdef1 [kdix [tdefat [deftdef min]]]]]]] . clear H0. destruct ns1.
          assert (x0 = x).
          clear - att x0at valt.
          pose proof (vt _ _ valt).
          unfold valid_t in H.
          assert ((Id x k) @ (0::kt)).
          simpl.
          simpl in att.
          rewrite att.
          simpl.
          reflexivity.
          specialize (H _ _ H0). simpl in H.
          rewrite H in *.
          pose proof (at_inj _ _ _ _ x0at H0).
          inversion H1; 
            reflexivity.
          rewrite H0 in *. clear H0.
          simpl in att.
          specialize (min _ _ att).
          destruct min.
          apply Var_refers_Var.
          pose proof (at_inj _ _ _ _ atkdef tdefat).
          subst.
          destruct tyxk as [kdef1 [tdef [kdix1 [ks1 [min1 tyd1]]]]] .
          pose proof (unique_reaches _ def_of _ _ _ _ _ _ _ _ _ _ _ min1 H0).
          destruct H1 as [keq [kdeq tdeq]].
          subst.
          pose proof (typed_def_unique _ _ _ _ _ _ _ typdef tyd1).
          destruct H1; subst.
          assumption.
        * apply Type_value_eq with ty1; intuition.
          apply H1 with kt k x tyc; intuition.
      - dependent induction H.
        * clear IHwell_typed_infer1.
          clear IHwell_typed_infer2.
          rename H1 into compenv.
          invCo wft0.
          apply Type_value_eq with (Co TFunC [t0; ty2] kt0).
          apply Clos_val_type; subst; try constructor; try assumption.
        + simpl in att.
          pose proof (val_subterm _ (vt _ _ valt) _ _ _ att).
          inversion H1; subst.
          inversion H5; subst.
          eauto.
        + intros.
          inversion H1.
          destruct (x == x0).
          discriminate H3.
          inversion compenv.
          destruct (H6 x0 tr te).
          destruct env.
          apply get_env_C.
          simpl in H3.
          assumption.
          destruct H10 as [wftr [ attr [tyr [typeat wty]]]].
          repeat (try split; [assumption |]).
          exists tyr.
          split; [| assumption].
          simpl in att.
          apply (LamC_pres_type _ _ _ _ typeat _ _ _ _ _ n att).
        + unfold type_at.
          exists kp (Co ParamC [Id x kx; t0] kp) kx kt.
          split; [| constructor].
          unfold reaches.
          split; [| constructor].
          destruct (params_sup _ def_of valt0 _ (Co ParamC [Id x kx; t0] kp) att).
          simpl.
          left; reflexivity.
          simpl in H1; assumption.
          constructor.
          pose proof (params_sup _ def_of valt0 _ e att).
          destruct H1.
          simpl.
          intuition.
          split.
          unfold mightreach.
          simpl in H2.
          destruct H2.
          rewrite <- H2 in *.           
          split.
          pose proof (params_sup _ def_of valt _ (Co ParamC [Id x kx; t0] kp) att).
          destruct H3.
          simpl.
          intuition.
          simpl in H4.
          destruct H4.
          subst.
          apply Scope_of_scope with (Co LamC [Co ParamC [Id x kx; t0] (x1 :: kt); e] kt).
          split.
          simpl in att.
          assumption.
          constructor.
          unfold valid.
          exists (Co ParamC [Id x kx; t0] (x1 :: kt)).
          simpl in H3; assumption.
          apply tn1_step.
          exists x0; reflexivity.
          intros.
          destruct H5.
          destruct H2; simpl in H2; rewrite <- H2 in *.
          inversion H6.
          destruct H7.
          inversion H7.
          right. 
          split.
          reflexivity.
          pose proof (vt _ _ valt _ _ H3).
          subst.
          pose proof (defsc_is_fix_or_fun _ _ _ _ H3 H4 H5).
          destruct H8.
          destruct H8.
          simpl in att.
          rewrite att in *.
          inversion H8.
          subst.
          simpl; reflexivity.
          simpl in att.
          rewrite att in *.
          inversion H8.
          destruct H7; inversion H7; subst.
          left; assumption.
        + constructor.
          constructor; [|intuition].
          clear - H.
          dependent induction H.
          reflexivity.
          apply transitivity with ty1.
          eauto.
          eauto.
          * apply Type_value_eq with ty1; intuition.
            apply IHwell_typed_infer with kt kp t0 kx; intuition.
      - dependent induction H.
        * clear IHwell_typed_infer1.
          clear IHwell_typed_infer2.
          rename H1 into compenv.
          invCo wft0.
          pose proof (type_param_eq _ _ _ _ H).
          apply Type_value_eq with (t0); [|intuition].
          pose proof (params_sup _ def_of valt _ e att).
          destruct H2.
          simpl; intuition.
          apply IHsem; try assumption.
        + apply WT_eq with ty.
          assumption.
          symmetry; assumption.
        + intros.
          subst.
          constructor.
          intros.
          inversion H4.
          destruct (x == x0).
          clear H5; subst.
          inversion H6.
          subst.
          split; try assumption.
          split; try assumption.
          split; try assumption.
          exists t0.
          split.
          unfold type_at.
          exists kp (Co ParamC [Id x0 kx; t0] kp) kx kt.
          split; [| constructor].
          unfold reaches.
          split; [| constructor].
          destruct (params_sup _ def_of valt0 _ (Co ParamC [Id x0 kx; t0] kp) att).
          simpl.
          left; reflexivity.
          simpl in H6; assumption.
          constructor.
          pose proof (params_sup _ def_of valt0 _ e att).
          destruct H5.
          simpl.
          intuition.
          split.
          unfold mightreach.
          simpl in H7.
          destruct H7.
          rewrite <- H7 in *.           
          split.
          pose proof (params_sup _ def_of valt0 _ (Co ParamC [Id x0 kx; t0] kp) att).
          destruct H8.
          simpl.
          intuition.
          simpl in H9.
          destruct H9.
          subst.
          apply Scope_of_scope with (Co FixC [Co ParamC [Id x0 kx; t0] (x1 :: kt); e] kt).
          split.
          simpl in att.
          assumption.
          constructor.
          unfold valid.
          exists (Co ParamC [Id x0 kx; t0] (x1 :: kt)).
          simpl in H3; assumption.
          apply tn1_step.
          exists x; reflexivity.
          intros.
          destruct H10.
          destruct H7; simpl in H7; rewrite <- H7 in *.
          inversion H11.
          destruct H12.
          inversion H12.
          right. 
          split.
          reflexivity.
          pose proof (vt _ _ valt _ _ H8).
          subst.
          pose proof (defsc_is_fix_or_fun _ _ _ _ H8 H9 H10).
          destruct H13.
          destruct H13.
          simpl in att.
          rewrite att in *.
          inversion H13.
          simpl in att.
          rewrite att in *.
          inversion H13.
          subst.
          simpl; reflexivity.
          destruct H12; inversion H12; subst.
          left; assumption.
          (* wt main*)
          constructor; intuition.
          apply WT_eq with ty; intuition.
          apply WT_eq with ty; intuition.
          (* case x <> x0 *)
          destruct compenv.
          unfold get_e in H6.
          destruct (H9 x0 tr te).
          destruct e0.
          apply (get_env_C).
          assumption.
          destruct H11 as [comp [wftr [ tytr [tyate wttr]]]].
          split; try assumption.
          split; try assumption.
          split; try assumption.
          exists tytr.
          split; [| assumption].
          pose proof (vt _ _ valt _ _ att). 
          rewrite H11 in *; simpl in *; subst.
          apply (FixC_pres_type _ _ _ _ tyate _ _ _ _ _ n att).
          *  apply Type_value_eq with ty1; intuition.
             apply IHwell_typed_infer with kt kp kx e t0 x; intuition.
      - dependent induction H.
        clear IHwell_typed_infer1 IHwell_typed_infer2.
        rename H1 into compenv.
        invCo wft0.
        specialize (IHsem1 wft2).
        pose proof (params_sup _ def_of valt0 _ e1 att).
        destruct H1.
        simpl; intuition.
        specialize (IHsem1 H1 (Co TFunC [ty1; ty2] kt) H).
        destruct H2 as [n neq].
        pose proof (compatible_env_trans_no_scope _ _ n _ _ att compenv).
        simpl in neq.
        rewrite <- neq in *.
        simpl in H2.
        assert (~ scopes_R (Co AppC [e1; e2] k) VarNS).
        intros scop; inversion scop.
        specialize (H2 H3). 
        specialize (IHsem1 H2).
        dependent induction IHsem1.
        * apply (IHsem2 wfntt subterm _ wtyt).
          constructor.
          intros.
          inversion H4.
          destruct (x == x0).
        + inversion H6; subst.
          pose proof (params_sup _ def_of valt _ tr att).
          destruct H5.
          simpl; intuition.
          destruct H7 as [n2 neq2].
          pose proof (compatible_env_trans_no_scope _ _ n2 _ _ att compenv0).
          simpl in neq2.
          rewrite <- neq2 in *.
          simpl in H7.
          assert (~ scopes_R (Co AppC [e1; tr] k) VarNS).
          intros scop; inversion scop.
          specialize (H7 H8). 
          intuition.
          exists ty1. 
          intuition.
        + inversion compenv.
          destruct H9 with x0 tr te.
          constructor.
          destruct (x == x0).
          contradiction (n0 e3).
          assumption.
          intuition.
          * inversion H1.
            inversion H7.
            inversion H14.
            inversion H19.
            subst.
            apply Type_value_eq with x1.
            apply IHIHsem1 with e x nenv x0 k2; intuition. 
            apply WT_eq with (Co TFunC [ty1; ty2] kt); intuition.
            apply WT_eq with ty1; intuition.
            intuition.
          * apply Type_value_eq with ty1; intuition.
            apply IHwell_typed_infer with k e2 e1; intuition.
      - dependent induction H.
        constructor.
        apply Type_value_eq with ty1; intuition.
        apply IHwell_typed_infer with k; intuition.
      - dependent induction H.
        constructor.
        apply Type_value_eq with ty1; intuition.
        apply IHwell_typed_infer with k; intuition.
      - dependent induction H.
        * clear IHwell_typed_infer1 IHwell_typed_infer2 IHwell_typed_infer3.
          invCo wft0.
          pose proof (params_sup _ def_of valt _ e2 att).
          destruct H3.
          simpl; intuition.
          apply IHsem2; intuition.
          destruct H4.
          simpl in H4.
          rewrite <- H4 in *.
          pose proof (compatible_env_trans_no_scope _ _ x _ _ att H2).
          apply H6.
          intro scop; inversion scop.
        * apply Type_value_eq with ty1; intuition.
          apply IHwell_typed_infer with kt e3 e2 e1; intuition.
      - dependent induction H.
        * clear IHwell_typed_infer1 IHwell_typed_infer2 IHwell_typed_infer3.
          invCo wft0.
          pose proof (params_sup _ def_of valt _ e3 att).
          destruct H3.
          simpl; intuition.
          apply IHsem2; intuition.
          destruct H4.
          simpl in H4.
          rewrite <- H4 in *.
          pose proof (compatible_env_trans_no_scope _ _ x _ _ att H2).
          apply H6.
          intro scop; inversion scop.
        * apply Type_value_eq with ty1; intuition.
          apply IHwell_typed_infer with kt e3 e2 e1; intuition.
      - dependent induction H.
        constructor.
        apply Type_value_eq with ty1; intuition.
        apply IHwell_typed_infer with kt e2 e1; intuition.
      - dependent induction H.
        constructor.
        apply Type_value_eq with ty1; intuition.
        apply IHwell_typed_infer with kt e2 e1; intuition.
    Qed. 

    (* Main type preservation lemma *)

    Lemma type_preservation :
      forall v,  
        semantics_cbn Nenv t v ->
        forall ty,
          well_typed_infer t ty -> 
          type_value v ty.
    Proof.
      intros.
      apply type_preservation_aux with t Nenv; intuition.
      assert (t @ nil).
      intuition.
      rewrite <- (vt0 _ _ H1).
      assumption.
      apply compatible_Nenv.
    Qed.
    

    (* Experiment on divergence definition *)

    CoInductive diverge_cbn : Env -> term -> Prop :=
    | VarC_div x t k kt env nenv : 
        get_env x env t nenv ->
        diverge_cbn nenv t ->            
        diverge_cbn env (Co VarC [Id x k] kt) 
    | FixC_div x t e kx kp kt env:
        diverge_cbn { x |--> (Co FixC [(Co ParamC [Id x kx;t] kp);e] kt,env), env} e ->
        diverge_cbn env (Co FixC [(Co ParamC [Id x kx;t] kp);e] kt)
    | AppC_div1 e1 e2 env k :
        diverge_cbn env e1 ->
        diverge_cbn env (Co AppC [e1;e2] k)
    | AppC_div2 e1 e2 e x env nenv k :
        semantics_cbn env e1 (Clos x e nenv) ->
        diverge_cbn { x |--> (e2,env), nenv} e ->
        diverge_cbn env (Co AppC [e1;e2] k)
    | IfzC_div1 e1 e2 e3 env kt :
        diverge_cbn env e1 ->
        diverge_cbn env (Co IfzC [e1;e2;e3] kt)
    | IfzC_divT e1 e2 e3 env kt :
        semantics_cbn env e1 0 ->
        diverge_cbn env e2 ->
        diverge_cbn env (Co IfzC [e1;e2;e3] kt)
    | IfzC_divF e1 e2 e3 env kt n :
        semantics_cbn env e1 (S n) ->
        diverge_cbn env e3 ->
        diverge_cbn env (Co IfzC [e1;e2;e3] kt) 
    | PlusC_div1 e1 e2 env kt: 
        diverge_cbn env e1 ->
        diverge_cbn env (Co PlusC [e1;e2] kt)   
    | PlusC_div2 e1 e2 env v kt: 
        semantics_cbn env e1 v ->
        diverge_cbn env e2 ->
        diverge_cbn env (Co PlusC [e1;e2] kt)   
    | Times_div1 e1 e2 env kt: 
        diverge_cbn env e1 ->
        diverge_cbn env (Co TimesC [e1;e2] kt)   
    | Times_div2 e1 e2 env v kt: 
        semantics_cbn env e1 v ->
        diverge_cbn env e2 ->
        diverge_cbn env (Co TimesC [e1;e2] kt)   
    .





  End With_term.

  Check type_preservation.

End sem_PCF. 
