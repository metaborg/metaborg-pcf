Require Import List.
Require Export Relation_Operators.
Require Import Operators_Properties.  (* APT: Seems to introduce some very weird Notations, so don't export *)
Require Export Setoid.

Module Type Sdf_Sig.
(* Abstract definition of an SDF instance *)

(* 
Ident is the set for identifier (e.g. can be string or it but usually left abstract) 
sort is the set of the different sort of a language (syntactic categories, e.g. exrpessions, statement, formula, ... ) *)
Parameter Ident sort : Set.

(* Both ident and sort have a decidable equality (I started to look at a functionnal model) *)
Parameter id_eq_dec : forall (x y : Ident), {x=y} + {x <> y}.
Parameter sort_eq_dec : forall (x y : sort), {x=y} + {x <> y}.

(* There is a distinguished sort corresponding to identifiers *)
Parameter Ident_Sort : sort.
Parameter Main_Sort : sort.

(* The set of constructor of the language *)
Parameter constructors : Type.

(* The signature (gives the arrity and sort arguments of constructors) *)
Parameter get_sig : constructors -> (list sort * sort).
Parameter signature : constructors -> (list sort) -> sort -> Prop. 

End Sdf_Sig.


(* The following module defines the set of terms on this signature *)

Module Sdf_Term (s : Sdf_Sig).

Export s.

(* The set of keys, I see a key as an annotation on a term, 
left to see what we really want it to be *) 
Definition key := list nat.
Definition k1 : key:= nil.

(* The set of terms *)
Inductive term : Type :=
| Co : constructors -> list term -> key -> term
| Id : Ident -> key -> term
.

Definition my_term_ind : 
  forall (P : term -> Prop) (Pl : list term -> Prop),
    (forall x k, P (Id x k)) ->  
    (forall cn lp k, Pl lp -> P (Co cn lp k)) ->
    Pl nil ->
    (forall t l, P t -> Pl l -> Pl (t :: l)) ->
    forall t, P t :=
  fun P Pl Pid Pco Pnil Pcons =>
    fix ti t :=  
      match t with 
        | Id x k => Pid x k
        | Co cn lp k =>
          let plp := 
              (fix pl l := match l return (Pl l) with 
                               nil => Pnil 
                             | cons a q => Pcons a q (ti a) (pl q) 
                           end)
          in Pco cn lp k (plp lp) 
      end
.

Definition direct_prefix (x y : key) := exists z, z::x = y.     
Definition prefix := clos_trans_n1 _ direct_prefix.
Definition prefix_star := clos_refl_trans_n1 _ direct_prefix.

(* occ represents an occurence (a path to a node in the term) 
this will be used when we will add features to the nabl model *)
Definition occ := list nat.

(* Predicates on terms *)
Inductive is_constructor : term -> Prop := Is_cons c l k : is_constructor (Co c l k).
Inductive is_ident : term -> Prop := Is_ident x k : is_ident (Id x k).

(* accessors on the elements of a term *)
Definition get_key t : key := 
match t with | Co _ _ k => k | Id _ k => k end.
Definition get_cons t : option constructors := 
match t with | Co cn _ _ => Some cn | Id _ _ => None end.
Definition get_args t : list term := 
match t with | Co _ lp _ => lp | Id _ _ => nil end.
Definition get_arg t n : Exc term := 
match t with | Co _ lp _ => nth_error lp n | _ => None end.

(* and the corresponding notations *)
Delimit Scope term_scope with term.
Bind Scope term_scope with term.
Notation " x == y " := (id_eq_dec x y) (at level 20) : term_scope.
Notation " Id? t " := (is_ident t) (at level 20) : term_scope.
Notation " Co? t " := (is_constructor t) (at level 20) : term_scope.
Notation " t 'k " := (get_key t) (at level 20) : term_scope.
Notation " t 'c " := (get_cons t) (at level 20) : term_scope.
Notation " t 'args " := (get_args t) (at level 20) : term_scope.
Notation " x <d< y " := (direct_prefix x y) (at level 20) : term_scope.
Notation " x << y " := (prefix x y) (at level 20) : term_scope.
Notation " x <<* y " := (prefix_star x y) (at level 20) : term_scope.

(* definition of a syntatically well-formed term, we just check that it match the signature*)

Inductive wf_term : sort -> term -> Prop :=
| Co_wf 
    s cn lp k ar
    ( sg : signature cn ar s) 
    ( rec : Forall2 wf_term ar lp)
    : wf_term s (Co cn lp k)
| Id_wf x k : wf_term Ident_Sort (Id x k)
.


Open Scope term_scope.

Fixpoint get key t :=
  match key with 
    | nil => Some t 
    | n::q => 
      match (get q t) with
        | Some t => nth_error (t 'args) n 
        | None => None
      end
  end.




(* defines term equality modulo key (used when terms represents types, which are varaibles free (so far ...))) *)
Inductive term_eq : term -> term -> Prop := 
| Co_eq cn lp1 lp2 k1 k2 : Forall2 term_eq lp1 lp2 -> term_eq (Co cn lp1 k1) (Co cn lp2 k2) 
| Id_eq i k1 k2 : term_eq (Id i k1) (Id i k2)
.
Notation " x ~t y" := (term_eq x y) (at level 20) : term_scope.  
Notation " x ~l y" := (Forall2 term_eq x y) (at level 20) : term_scope.  


Ltac term_induction :=
  match goal with
    | [|- forall x, ?P x] => 
      let l := fresh "l" in
          apply (my_term_ind (fun x => P x) (fun l => Forall (fun x => P x) l)) 
  end.

Lemma term_eq_refl: reflexive _ term_eq.
Proof.
unfold reflexive. 
term_induction; simpl; constructor; try assumption.
induction H; constructor; intuition.
Qed.


Lemma term_eq_sym: symmetric _ term_eq.
unfold symmetric. 
apply (my_term_ind 
      (fun x => forall y, x ~t y -> y ~t x) (fun l => forall lp, l ~l lp -> lp ~l l)); intros.
inversion H; constructor.
inversion H0; constructor; intuition.
inversion H; constructor.
inversion H1; constructor; intuition.
Qed.

Lemma term_eq_trans: transitive _ term_eq.
unfold transitive. 
apply (my_term_ind (fun x => forall y z : term, x ~t y -> y ~t z -> x ~t z) 
                (fun x => forall y z, x ~l y -> y ~l z -> x ~l z)); intros.
inversion H. rewrite <- H1 in *. inversion H0. constructor.
inversion H0. rewrite <- H3 in *. inversion H1. constructor. apply H with lp2; intuition.
inversion H. rewrite <- H2 in *. inversion H0. constructor.
inversion H1. rewrite <- H6 in *. inversion H2. constructor. 
 apply H with y0; intuition.
 apply H0 with l'; intuition.
Qed.

Add Relation term term_eq
 reflexivity proved by (@term_eq_refl)
 symmetry proved by (@term_eq_sym)
 transitivity proved by (@term_eq_trans)
 as eq_term.

End Sdf_Term.