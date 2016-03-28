From mathcomp Require Import ssreflect.
Require Import MSets Equalities.

Module TAPL_Set.

Module SetNotation (E:DecidableType) (Import S:WSetsOn E).

  Notation " {{ }} " := empty (at level 100) : set_scope.
  Notation " {{ x }} " := (add x empty) (at level 100) : set_scope.
  Notation " {{ x ; .. ; y }} " := (add x .. (add y empty) ..) (at level 100) : set_scope.

  Notation " x @ s " := ((mem x s) = true) (at level 90, no associativity) : set_scope.
  Notation " x @? s " := (mem x s) (at level 90, no associativity) : set_scope.
 
  Notation " x :: s " := (add x s) (at level 60, right associativity) : set_scope.
  Notation " x \/ y " := (union x y) (at level 85, right associativity) : set_scope.
  Notation " x /\ y " := (inter x y) (at level 80, right associativity) : set_scope.
  Notation " x \ y " := (diff x y) (at level 60, no associativity) : set_scope.

  Notation " # x " := (cardinal x) (at level 35, x at next level) : set_scope.

  Delimit Scope set_scope with set.

End SetNotation.

Module SetExt (E:DecidableType) (Import S:WSetsOn E).
  Module Notations := SetNotation E S.
  Import Notations.
  Local Open Scope set_scope.

  Lemma cardinal_union : forall (s1 s2 : t), #(s1 \/ s2) <= #s1 + #s2.
  Admitted.

  Lemma cardinal_inter : forall (s1 s2 : t), #(s1 /\ s2) <= #s1 /\ #(s1 /\ s2) <= #s2.
  Admitted.

End SetExt.

Module Ex_Inductive.

  Inductive bool : Set := t | f.

  (* generates bool_eq_dec *)
  Scheme Equality for bool.

  Module BoolMDT <: MiniDecidableType.
    Definition t := bool.
    Definition eq_dec := bool_eq_dec.
  End BoolMDT.

  Module BoolDT := Make_UDT BoolMDT.
  Module BoolSet := MSetWeakList.Make BoolDT.
  Module BoolSetNotation := SetNotation BoolDT BoolSet.

  Notation bool_set := BoolSet.t.
  Import BoolSetNotation.

  Section NotationCheck.
    Local Open Scope set_scope.

    Check {{}}.
    Check {{t; f}}.
    Eval compute in #{{t; t; f}}.
    Eval compute in #({{t; t; f}} \ {{t}}).

  End NotationCheck.

End Ex_Inductive.  

Module NatSetNotation (E:OrderedType) (Import S:WSetsOn E).

  Notation " {{ }} " := empty (at level 100) : nat_set_scope.
  Notation " {{ x }} " := (add x empty) (at level 100) : nat_set_scope.
  Notation " {{ x ; .. ; y }} " := (add x .. (add y empty) ..) (at level 100) : nat_set_scope.

  Notation " x @ s " := ((mem x s) = true) (at level 90, no associativity) : nat_set_scope.
  Notation " x @? s " := (mem x s) (at level 90, no associativity) : nat_set_scope.
 
  Notation " x :: s " := (add x s) (at level 60, right associativity) : nat_set_scope.
  Notation " x \/ y " := (union x y) (at level 85, right associativity) : nat_set_scope.
  Notation " x /\ y " := (inter x y) (at level 80, right associativity) : nat_set_scope.
  Notation " x \ y " := (diff x y) (at level 60, no associativity) : nat_set_scope.

  Notation " # x " := (cardinal x) (at level 35, x at next level) : nat_set_scope.

  Delimit Scope nat_set_scope with nat_set.

End NatSetNotation.

Module NatSet := MSetList.Make PeanoNat.Nat.
Module NatSetNotationM := NatSetNotation PeanoNat.Nat NatSet.

Notation nat_set := NatSet.t.

Export MSets Equalities NatSetNotationM.

End TAPL_Set.

