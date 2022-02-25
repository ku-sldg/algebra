Require Import Algebra.Semigroup.
Section Monoids.
Context {G: Set}(mult: G -> G -> G)(ident: G).

Class Monoid := {
  monoid_assoc: forall (a b c: G), mult (mult a b) c = mult a (mult b c);
  monoid_ident_left: forall (a: G), mult ident a = a;
  monoid_ident_right: forall (a: G), mult a ident = a;
}.

Theorem monoid_semigroup:
  Monoid -> Semigroup mult.
Proof.
  intros Gmonoid.
  constructor.
  apply monoid_assoc.
Qed.

Context `{Gmonoid: Monoid}.

Lemma monoid_left_mult (a b: G):
  a = b -> forall (c: G), mult c a = mult c b.
Proof.
  intros <-;
    reflexivity.
Qed.

Lemma monoid_right_mult (a b: G):
  a = b -> forall (c: G), mult a c = mult b c.
Proof.
  intros <-;
    reflexivity.
Qed.

Theorem monoid_ident_unique (ident': G):
  (forall (a: G), mult ident' a = a) ->
  (forall (a: G), mult a ident' = a) ->
  ident' = ident.
Proof.
  intros Hlident' Hrident'.
  rewrite <- (Hrident' ident).
  rewrite <- (monoid_ident_left ident').
  rewrite (monoid_ident_left (mult ident ident')).
  reflexivity.
Qed.
End Monoids.
