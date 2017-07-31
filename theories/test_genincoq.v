From elpi Require Import elpi.
Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".

Module Generics.
  Record class (T : Type) := Class { rep  : Type;
                                     f    : T -> rep;
                                     g    : rep -> T;
                                     inj  : forall (x : T), g (f x) = x;
                                     surj : forall (x : rep), f (g x) = x
                                   }.
  Structure type := Pack { obj : Type; class_of : class obj }.
  Arguments Class {T} rep f g inj surj.

  Definition from (e : type) : obj e -> rep (obj e) (class_of e) :=
    let 'Pack _ (Class _ f _ _ _) := e in f.
  Definition to (e : type) : rep (obj e) (class_of e) -> (obj e) :=
    let 'Pack _ (Class _ _ g _ _) := e in g.
  Arguments from {e} x : simpl never.
  Arguments to   {e} x : simpl never.

  Definition to_from_id (e : type) : forall (x : obj e), to (from x) = x :=
    let 'Pack _ (Class _ _ _ inj _) := e in inj.
  Definition from_to_id (e : type) : forall (x : rep (obj e) (class_of e)), from (to x) = x :=
    let 'Pack _ (Class _ _ _ _ surj) := e in surj.
  Arguments to_from_id {e} : simpl never.
  Arguments from_to_id {e} : simpl never.
End Generics.

Inductive SumType (A B : Type) : Type :=
| MkSumL : A -> SumType A B
| MkSumR : B -> SumType A B.

Inductive ProdType (A B : Type) : Type :=
| MkProd : A -> B -> ProdType A B.

Inductive UnitType : Type :=
| MkUnit.


Inductive MList (A B : Type) :=
| MCons : A -> B -> MList A B -> MList A B
| MNil : MList A B.

Inductive MTree (A : Type) :=
| MNode : MList A (MTree (A * A)) -> MTree A.


Elpi Accumulate File "genincoq.elpi".
Elpi Run "derive-generics ""list"".".
Print list_generics.
Elpi Run "derive-generics ""nat"".".
Print nat_generics.
Elpi Run "derive-generics ""MList"".".
Print MList_generics.
Elpi Run "derive-generics ""MTree"".".
Print MTree_generics.

