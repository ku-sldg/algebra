Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
From algebra Require Import Semigroups Monoids Groups AbelianGroups.

Section Rings.
Context {Carrier: Type}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (add: Carrier -> Carrier -> Carrier).
Context {add_proper: Proper (equiv ==> equiv ==> equiv) add}.
Context (zero: Carrier).
Context (minus: Carrier -> Carrier).
Context {minus_proper: Proper (equiv ==> equiv) minus}.
Context (mul: Carrier -> Carrier -> Carrier).
Context {mul_proper: Proper (equiv ==> equiv ==> equiv) mul}.

Infix "==" := equiv (at level 60, no associativity).
Infix "<+>" := add (at level 50, left associativity).
Infix "<*>" := mul (at level 40, left associativity).

Class Ring := {
  ring_add_abelian :> AbelianGroup equiv add zero minus;
  ring_mul_semigroup :> Semigroup equiv mul;
  ring_distrib_l:
    forall (a b c: Carrier),
      a <*> (b <+> c) == a <*> b <+> a <*> c;
  ring_distrib_r:
    forall (a b c: Carrier),
      (b <+> c) <*> a == b <*> a <+> c <*> a;
}.

Context {ring: Ring}.

Theorem ring_mul_0_l (a: Carrier):
  zero <*> a == zero.
Proof.
  apply (group_idemp_ident equiv add zero minus).
  setoid_rewrite <- ring_distrib_r.
  setoid_rewrite (monoid_ident_r equiv add zero).
  reflexivity.
Qed.

Theorem ring_mul_0_r (a: Carrier):
  a <*> zero == zero.
Proof.
  apply (group_idemp_ident equiv add zero minus).
  setoid_rewrite <- ring_distrib_l.
  setoid_rewrite (monoid_ident_r equiv add zero).
  reflexivity.
Qed.

Theorem ring_mul_minus_l (a b: Carrier):
  (minus a) <*> b == minus (a <*> b).
Proof.
  apply (group_inv_r_unique equiv add zero minus).
  setoid_rewrite <- ring_distrib_r.
  setoid_rewrite (group_inv_r equiv add zero minus).
  apply ring_mul_0_l.
Qed.

Theorem ring_mul_minus_r (a b: Carrier):
  a <*> (minus b) == minus (a <*> b).
Proof.
  apply (group_inv_r_unique equiv add zero minus).
  setoid_rewrite <- ring_distrib_l.
  setoid_rewrite (group_inv_r equiv add zero minus).
  apply ring_mul_0_r.
Qed.

Theorem ring_mul_minus_minus (a b: Carrier):
  (minus a) <*> (minus b) == a <*> b.
Proof.
  setoid_rewrite ring_mul_minus_l.
  setoid_rewrite ring_mul_minus_r.
  apply (group_inv_involute equiv add zero minus).
Qed.
End Rings.
