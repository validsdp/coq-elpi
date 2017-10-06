Cd "~/git/coq-elpi".
(* Set Universe Polymorphism. *)

From elpi Require Import elpi.

Class param_db {X X1 XR : Type} (x : X) (x : X1) (xR : XR) := store_param {}.
Class param {X : Type} {XR : X -> X -> Type} (x : X) (xR : XR x x) := Param {}.

Elpi Tactic param " typecheck.".
Elpi Accumulate File "coq-extra.elpi".
Elpi Accumulate File "coq-param.elpi".
Elpi Run param "typecheck".

Elpi Print param "param.html"
  "pervasives.elpi"
  "coq-lib.elpi"
  "lp-lib.elpi"
  "coq-refiner.elpi".


Set Printing Universes.
(* Elpi Run param "env-add-param {{@nat}} ""natR""". *)
Inductive natR : nat -> nat -> Set :=
    natR_O : natR 0 0
  | natR_S : (fun f g : nat -> nat => forall H H0 : nat, natR H H0 -> natR (f H) (g H0)) S S.
Instance: param_db nat nat natR.
Instance: param_db O O natR_O.
Instance: param_db S S natR_S.

Inductive vec (A : Type) : nat -> Type :=
    nil : vec A 0 | cons : A -> forall n : nat, vec A n -> vec A (S n).
(* Elpi Run param "env-add-param {{@vec}} ""vecR"")". *)
Inductive
vecR (A A0 : Type) (A1 : A -> A0 -> Type) : forall H H0 : nat, natR H H0 -> vec A H -> vec A0 H0 -> Type :=
    vecR_nil : vecR A A0 A1 0 0 natR_O (nil A) (nil A0)
  | vecR_cons : forall (H : A) (H0 : A0),
                A1 H H0 ->
                forall (n n0 : nat) (n1 : natR n n0) (H1 : vec A n) (H2 : vec A0 n0),
                vecR A A0 A1 n n0 n1 H1 H2 ->
                vecR A A0 A1 (S n) (S n0) (natR_S n n0 n1) (cons A H n H1) (cons A0 H0 n0 H2).
Instance: param_db vec vec vecR.
Instance: param_db nil nil vecR_nil.
Instance: param_db cons cons vecR_cons.

Definition vec_length_type := forall (A : Type) (n : nat), vec A n -> nat.
Fail Elpi Run param "env-add-param {{@vec_length_type}} ""vec_length_typeR"")".

Definition vec_length_typeR : (forall (A : Type) (n : nat), vec A n -> nat) ->
       (forall (A : Type) (n : nat), vec A n -> nat) -> Type :=
fun f g : forall (A : Type) (n : nat), vec A n -> nat =>
forall (A A0 : Type) (A1 : A -> A0 -> Type) (n n0 : nat) (n1 : natR n n0) (H : vec A n) (H0 : vec A0 n0),
vecR A A0 A1 n n0 n1 H H0 -> natR (f A n H) (g A0 n0 H0).
Instance: param_db vec_length_type vec_length_type vec_length_typeR.

Definition vec_length_rec (vec_length : vec_length_type)
  (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi Run param "env-add-param {{@vec_length_rec}} ""vec_length_recR"")".

Elpi Run param "param-const {{@vec_length_rec}} _ _ _ _ XR TR".

(* Elpi Run param " *)
(*      coq-env-const {term->gr {{@vec_length_rec}}} X _, *)
(*      with-TC-param (param X X1 XR), *)
(*      coq-elaborate X X' T', *)
(*      coq-elaborate X1 X1' T1', *)
(*      coq-elaborate XR XR' TR', *)
(*      coq-env-add-const ""vec_length_recR'"" XR' TR' _)". *)

Definition vec_length_recR' :=
fun (vec_length vec_length0 : vec_length_type) (vec_length1 : vec_length_typeR vec_length vec_length0)
  (A A0 : Type) (A1 : A -> A0 -> Type) (n n0 : nat) (n1 : natR n n0) (v : vec A n) 
  (v0 : vec A0 n0) (v1 : vecR A A0 A1 n n0 n1 v v0) =>
match
  v1 in (vecR _ _ _ n2 n3 n4 v2 v3)
  return
    (natR match v2 with
          | nil _ => 0
          | cons _ _ n5 w => S (vec_length A n5 w)
          end match v3 with
              | nil _ => 0
              | cons _ _ n5 w => S (vec_length0 A0 n5 w)
              end)
with
| vecR_nil _ _ _ => natR_O
| vecR_cons _ _ _ _ _ _ n2 n3 n4 w w0 w1 =>
    natR_S (vec_length A n2 w) (vec_length0 A0 n3 w0) (vec_length1 A A0 A1 n2 n3 n4 w w0 w1)
end.

Fail Elpi Run param "env-add-param {{@vec_length_rec}} ""vec_length_recR"")".

(* Definition vec_length_recR := vec_length_recR'. *)

Inductive fin : nat -> Type :=
    FO : fin 0 | FS : forall n : nat, fin n -> fin (S n).
Elpi Run param "env-add-param {{@fin}} ""finR"")".

Fixpoint fin_length  n (v : fin n) :=
  match v with FO => 0 | FS _ w => S (fin_length _ w) end.
Elpi Run param "env-add-param {{@fin_length}} ""fin_lengthR"")".

Fixpoint vec_length (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi Run param "env-add-param {{@vec_length}} ""vec_lengthR"")".


Elpi Run param "env-add-param {{@list}} ""listR""".
Elpi Run param "env-add-param {{@eq}} ""eqR""".

Fixpoint plus' m n := match n with 0 => m | S n => S (plus' m n) end.
Elpi Run param "env-add-param {{@plus'}} ""plus'R""".
Elpi Run param "env-add-param {{@plus}} ""plusR""".

Definition test m n p q r := m + n + p + q + r.
Elpi Run param "env-add-param {{@test}} ""testR""".

(* Elpi Run param " *)
(*   X = {{@testR}}, coq-typecheck X Ty, Nb is 5, Nb3 is 3 * Nb, *)
(*   eta-perm demix (Nb3) Ty X Ty' X'.". *)
  
(* Elpi Run param " *)
(*   term->gr {{@testR}} GR, *)
(*   coq-env-const GR X TX, *)
(*   Nb is 5, *)
(*   perm-op lam demix (3 * Nb) X Y, *)
(*   perm-op lam (mix Nb) (3 * Nb) Y Z, *)
(*   perm-op prod demix (3 * Nb) TX TY, *)
(*   perm-op prod (mix Nb) (3 * Nb) TY TZ, *)
(*   coq-typecheck Y TY, *)
(*   Z = X, TZ = TX. *)
(* ". *)



Elpi Run param "with-TC-param (param {{O}} X Y)".
Elpi Run param "with-TC-param (param {{S (S 0)}} X Y)".

Fail Elpi Run param "param-const {{@eq_refl}} _ _ _ _ _".

Elpi Run param "with-TC {{@param_db}} retrieve-param (param {{nat}} X Y)".

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi Run param "env-add-param {{@nat2nat}} ""nat2natR""".
Elpi Run param "env-add-param {{@nat2nat2nat}} ""nat2nat2natR""".
Elpi Run param "env-add-param {{@pred}} ""predR""".
Print predR.
Check (predR : nat2natR pred pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi Run param "env-add-param {{@predn}} ""prednR""".

Check (prednR : nat2natR predn predn).
Check (plusR : nat2nat2natR plus plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi Run param "param-const {{@quasidn}} _ _ _ _ _".

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi Run param "param-const {{@weirdn}} _ _ _ _ _".

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi Run param "env-add-param {{@bla}} ""blaR"")".

Elpi Run param "coq-TC-db-for {term->gr {{@param_db}}} _".
