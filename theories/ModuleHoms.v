Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
From algebra Require Import Modules GroupHoms CommRings.
Section ModuleHoms.
Context {R: Type}.
Context (Requiv: relation R).
Context {Requiv_equiv: Equivalence Requiv}.
Context (Radd: R -> R -> R).
Context {Radd_proper: Proper (Requiv ==> Requiv ==> Requiv) Radd}.
Context (Rzero: R).
Context (Rminus: R -> R).
Context {Rminus_proper: Proper (Requiv ==> Requiv) Rminus}.
Context (Rmul: R -> R -> R).
Context {Rmul_proper: Proper (Requiv ==> Requiv ==> Requiv) Rmul}.
Context (Rone: R).
Context {R_cring: CommRing Requiv Radd Rzero Rminus Rmul Rone}.
Context {M1: Type}.
Context (M1equiv: relation M1).
Context {M1equiv_equiv: Equivalence M1equiv}.
Context (M1add: M1 -> M1 -> M1).
Context {M1add_proper: Proper (M1equiv ==> M1equiv ==> M1equiv) M1add}.
Context (M1zero: M1).
Context (M1minus: M1 -> M1).
Context {M1minus_proper: Proper (M1equiv ==> M1equiv) M1minus}.
Context (action1: R -> M1 -> M1).
Context {action1_proper: Proper (Requiv ==> M1equiv ==> M1equiv) action1}.
Context {M2: Type}.
Context (M2equiv: relation M2).
Context {M2equiv_equiv: Equivalence M2equiv}.
Context (M2add: M2 -> M2 -> M2).
Context {M2add_proper: Proper (M2equiv ==> M2equiv ==> M2equiv) M2add}.
Context (M2zero: M2).
Context (M2minus: M2 -> M2).
Context {M2minus_proper: Proper (M2equiv ==> M2equiv) M2minus}.
Context (action2: R -> M2 -> M2).
Context {action2_proper: Proper (Requiv ==> M2equiv ==> M2equiv) action2}.
Context {module1: Module_ Radd Rmul Rone M1equiv M1add M1zero M1minus action1}.
Context {module2: Module_ Radd Rmul Rone M2equiv M2add M2zero M2minus action2}.
Context (hom: M1 -> M2).
Context {hom_proper: Proper (M1equiv ==> M2equiv) hom}.

Infix "=R=" := Requiv (at level 60, no associativity).
Infix "[+]" := Radd (at level 50, left associativity).
Infix "[*]" := Rmul (at level 40, left associativity).
Infix "=M1=" := M1equiv (at level 60, no associativity).
Infix "=M2=" := M2equiv (at level 60, no associativity).
Infix "<+1>" := M1add (at level 50, left associativity).
Infix "<+2>" := M2add (at level 50, left associativity).
Infix "<.1>" := action1 (at level 40, no associativity).
Infix "<.2>" := action2 (at level 40, no associativity).

Class ModuleHom := {
    module_hom_group_hom :> GroupHom M1add M2equiv M2add hom;
    module_hom_action: forall (r: R)(a: M1), hom (r <.1> a) =M2= r <.2> hom a;
}.

Definition module_isomorphism :=
  exists (moh: M2 -> M1),
    (forall (a: M1), moh (hom a) =M1= a) /\
    (forall (b: M2), hom (moh b) =M2= b).
End ModuleHoms.