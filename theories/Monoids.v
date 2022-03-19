Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
From algebra Require Import Semigroups.
Require Import Setoid.

Section Monoids.
Context {Carrier: Type}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (op: Carrier -> Carrier -> Carrier).
Context {op_proper: Proper (equiv ==> equiv ==> equiv) op}.
Context (ident: Carrier).

Infix "==" := equiv (at level 60, no associativity).
Infix "<o>" := op (at level 40, no associativity).

Class Monoid := {
  monoid_semigroup :> Semigroup equiv op;
  monoid_ident_l:
    forall (a: Carrier), ident <o> a == a;
  monoid_ident_r:
    forall (a: Carrier), a <o> ident == a;
}.

Context {monoid: Monoid}.

Theorem group_ident_l_unique (e: Carrier):
  (forall (a: Carrier), e <o> a == a) ->
  e == ident.
Proof.
  intros Hl.
  specialize (Hl ident).
  setoid_rewrite <- Hl.
  symmetry.
  apply monoid_ident_r.
Qed.

Theorem group_ident_r_unique (e: Carrier):
  (forall (a: Carrier), a <o> e == a) ->
  e == ident.
Proof.
  intros Hr.
  specialize (Hr ident).
  setoid_rewrite <- Hr.
  symmetry.
  apply monoid_ident_l.
Qed.

Lemma monoid_op_l_solo (a b: Carrier):
  a == ident -> b <o> a == b.
Proof.
  intros H.
  setoid_rewrite H.
  apply monoid_ident_r.
Qed.

Lemma monoid_op_r_solo (a b: Carrier):
  a == ident -> a <o> b == b.
Proof.
  intros H.
  setoid_rewrite H.
  apply monoid_ident_l.
Qed.
End Monoids.
