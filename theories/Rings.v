Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
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

Infix "~" := equiv (at level 60, no associativity).
Infix "<+>" := add (at level 50, left associativity).
Infix "<*>" := mul (at level 40, left associativity).

Class Ring := {
  ring_add_abelian :> AbelianGroup equiv add zero minus;
  ring_mul_semigroup :> Semigroup equiv mul;
  ring_distrib_l:
    forall (a b c: Carrier),
      a <*> (b <+> c) ~ a <*> b <+> a <*> c;
  ring_distrib_r:
    forall (a b c: Carrier),
      (b <+> c) <*> a ~ b <*> a <+> c <*> a;
}.

Context {ring: Ring}.

Theorem ring_mul_0_l (a: Carrier):
  zero <*> a ~ zero.
Proof.
  apply (group_idemp_ident equiv add zero minus).
  transitivity ((zero <+> zero) <*> a);
    [symmetry; apply ring_distrib_r |].
  apply (semigroup_op_r equiv mul).
  apply (monoid_ident_r equiv add zero).
Qed.

Theorem ring_mul_0_r (a: Carrier):
  a <*> zero ~ zero.
Proof.
  apply (group_idemp_ident equiv add zero minus).
  transitivity (a <*> (zero <+> zero));
    [symmetry; apply ring_distrib_l |].
  apply (semigroup_op_l equiv mul).
  apply (monoid_ident_r equiv add zero).
Qed.

Theorem ring_mul_minus_l (a b: Carrier):
  (minus a) <*> b ~ minus (a <*> b).
Proof.
  apply (group_inv_r_unique equiv add zero minus).
  transitivity ((a <+> minus a) <*> b);
    [symmetry; apply ring_distrib_r |].
  transitivity (zero <*> b);
    [apply (semigroup_op_r equiv mul);
      apply (group_inv_r equiv add zero minus) |].
  apply ring_mul_0_l.
Qed.

Theorem ring_mul_minus_r (a b: Carrier):
  a <*> (minus b) ~ minus (a <*> b).
Proof.
  apply (group_inv_r_unique equiv add zero minus).
  transitivity (a <*> (b <+> minus b));
    [symmetry; apply ring_distrib_l |].
  transitivity (a <*> zero);
    [apply (semigroup_op_l equiv mul);
      apply (group_inv_r equiv add zero minus) |].
  apply ring_mul_0_r.
Qed.

Theorem ring_mul_minus_minus (a b: Carrier):
  (minus a) <*> (minus b) ~ a <*> b.
Proof.
  transitivity (minus (a <*> minus b));
    [apply ring_mul_minus_l |].
  transitivity (minus (minus (a <*> b)));
    [apply minus_proper;
      apply ring_mul_minus_r |].
  apply (group_inv_involute equiv add zero minus).
Qed.
End Rings.
