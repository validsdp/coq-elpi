From elpi Require Import elpi.
Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".

Module Generics.
  Record class (T : Type) := Class { rep : Type;
                                     f   : T -> rep;
                                     g   : rep -> option T;
                                     inj : forall (x : T), g (f x) = Some x
                                   }.
  Structure type := Pack { obj : Type; class_of : class obj }.
  Arguments Class {T} rep f g inj.

  Definition from (e : type) : obj e -> rep (obj e) (class_of e) :=
    let 'Pack _ (Class _ f _ _) := e in f.
  Definition to (e : type) : rep (obj e) (class_of e) -> option (obj e) :=
    let 'Pack _ (Class _ _ g _) := e in g.
  Arguments from {e} x : simpl never.
  Arguments to   {e} x : simpl never.

  Definition to_from_id (e : type) : forall (x : obj e), to (from x) = Some x :=
    let 'Pack _ (Class _ _ _ inj) := e in inj.
  Arguments to_from_id {e} : simpl never.
End Generics.

Inductive SumType (A B : Type) : Type :=
| MkSumL : A -> SumType A B
| MkSumR : B -> SumType A B.

Inductive ProdType (A B : Type) : Type :=
| MkProd : A -> B -> ProdType A B.

Inductive UnitType : Type :=
| MkUnit.

Elpi Accumulate File "genincoq.elpi".
Elpi Run "make-rep-test.".

