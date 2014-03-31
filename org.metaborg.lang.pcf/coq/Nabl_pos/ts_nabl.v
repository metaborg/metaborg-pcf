
Require Import Program.
Require Import Lists.List.
Require Import sdf_definition.
Require Import Relation_Operators.
Require Import nabl_def.

Module Type TS_Nabl_Sig (s : Sdf_Sig) (n : Nabl_Sig s).

Module nabl_wf_mod := Nabl_wf s n.
Export nabl_wf_mod.

(* the (main) sort of types *)
Parameter type_sort : sort.

(* !!! Warning, types are terms so many times a term in the signature has to be interpreted as a type, term that represent types will usually have names starting with ty
eg :*)

(* Nabl definitions can include type, so just as the scope_R, defines_R rules in nabl_definitions, we have a relation 
corresponding to term t defines x in namespace ns of type ty with key k : typed_definesR t x ns ty k *)
Parameter typed_definesR : term -> Ident -> NS -> term -> key -> Prop.

End TS_Nabl_Sig.

Module TS_NaBL_def (ssig : Sdf_Sig) (nsig : Nabl_Sig ssig) (tssig : TS_Nabl_Sig ssig nsig).

  Export tssig.

  Section With_program.
    
    (* I'm not found of sigma types but maybe this can be used *)
    Definition types := { te | wf_term type_sort te }.
    
    Variable t : term.
    Variable wft : wf_term Main_Sort t.
    Variable def_of : key -> key -> Prop.
    
    Delimit Scope term_scope with term.
    Bind Scope term_scope with term.
    Notation " @ x " := (get x t) (at level 20) : term_scope.
    Notation " x |-> y " := (def_of x y) (at level 20) : term_scope.
    Notation " y @ x " := (@ x = Some y) (at level 19) : term_scope.

    
    (* and the definition of a lookup *)
    Inductive lookup x ns kx ty : Prop := 
     | Lookup_ty kdef (mpkd : kx |-> kdef) tdef (atkdef : tdef @ kdef) ki (typdef : typed_definesR tdef x ns ty ki) :
         lookup x ns kx ty
        .
    
  End With_program.

End TS_NaBL_def.

