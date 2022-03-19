Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
Require Import Setoid.

Section Semigroups.
Context {Carrier: Type}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (op: Carrier -> Carrier -> Carrier).
Context {op_proper: Proper (equiv ==> equiv ==> equiv) op}.

Infix "==" := equiv (at level 60, no associativity).
Infix "<o>" := op (at level 40, left associativity).

Class Semigroup := {
  semigroup_assoc:
    forall (a b c: Carrier),
      a <o> b <o> c == a <o> (b <o> c);
}.

Context {semigroup: Semigroup}.

Lemma semigroup_op_l (a b: Carrier):
  a == b -> forall (c: Carrier), c <o> a == c <o> b.
Proof.
  intros Hab c.
  setoid_rewrite Hab.
  reflexivity.
Qed.

Lemma semigroup_op_r (a b: Carrier):
  a == b -> forall (c: Carrier), a <o> c == b <o> c.
Proof.
  intros Hab c.
  setoid_rewrite Hab.
  reflexivity.
Qed.

Class Commutative := {
    commutative:
      forall (a b: Carrier),
        a <o> b == b <o> a;
}.
End Semigroups.
