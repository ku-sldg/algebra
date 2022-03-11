Require Import Algebra.Semigroup.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.

Section RingTheory.
Context {R: Set}(plus: R -> R -> R)(zero: R)(minus: R -> R)(mult: R -> R -> R).

Class Ring := {
  ring_plus_assoc: forall (a b c: R), plus (plus a b) c = plus a (plus b c);
  ring_plus_comm: forall (a b: R), plus a b = plus b a;
  ring_plus_ident: forall (a: R), plus a zero = a;
  ring_plus_inv: forall (a: R), plus a (minus a) = zero;
  ring_mult_assoc: forall (a b c: R), mult (mult a b) c = mult a (mult b c);
  ring_distrib_left: forall (a b c: R), mult a (plus b c) = plus (mult a b) (mult a c);
  ring_distrib_right: forall (a b c: R), mult (plus b c) a = plus (mult b a) (mult c a);
}.

Lemma ring_agroup_plus:
  Ring -> AbelianGroup plus zero minus.
Proof.
  intros Rring.
  constructor.
  { apply ring_plus_assoc. }
  { apply ring_plus_comm. }
  { apply ring_plus_ident. }
  { apply ring_plus_inv. }
Qed.

Lemma ring_semigroup_mult:
  Ring -> Semigroup mult.
Proof.
  intros Rring.
  constructor.
  apply ring_mult_assoc.
Qed.

Lemma agroup_plus_semigroup_mult_distrib_ring:
  AbelianGroup plus zero minus ->
  Semigroup mult ->
  (forall (a b c: R), mult a (plus b c) = plus (mult a b) (mult a c)) ->
  (forall (a b c: R), mult (plus b c) a = plus (mult b a) (mult c a)) ->
  Ring.
Proof.
  intros Ragroup_plus Rsemigrp_mult Hld Hrd.
  constructor;
    try assumption.
  { apply semigroup_assoc.
    apply (agroup_semigroup plus zero minus).
    assumption. }
  { apply (agroup_comm plus zero minus). }
  { apply (agroup_ident plus zero minus). }
  { apply (agroup_inv plus zero minus). }
  { apply semigroup_assoc.
    assumption. }
Qed.

Context `{Rring: Ring}.

Theorem ring_left_mult_zero (a: R):
  mult zero a = zero.
Proof.
  cut (AbelianGroup plus zero minus).
  { intros Ragroup_plus.
    cut (mult (plus zero zero) a = mult zero a).
    { intros H.
      rewrite ring_distrib_right in H.
      apply (agroup_idemp_zero plus zero minus) in H.
      assumption. }
    { rewrite ring_plus_ident.
      reflexivity. } }
  { apply ring_agroup_plus.
    assumption. }
Qed.

Theorem ring_right_mult_zero (a: R):
  mult a zero = zero.
Proof.
  cut (AbelianGroup plus zero minus).
  { intros Ragroup_plus.
    cut (mult a (plus zero zero) = mult a zero).
    { intros H.
      rewrite ring_distrib_left in H.
      apply (agroup_idemp_zero plus zero minus) in H.
      assumption. }
    { rewrite (agroup_ident plus zero minus zero).
      reflexivity. } }
  { apply ring_agroup_plus.
    assumption. }
Qed.

Theorem ring_mult_minus_left (a b: R):
  mult (minus a) b = minus (mult a b).
Proof.
  cut (AbelianGroup plus zero minus).
  { intros Ragroup_plus.
    apply (agroup_minus_unique plus zero minus);
    rewrite <- ring_distrib_right.
    rewrite (agroup_inv plus zero minus).
    apply ring_left_mult_zero. }
  { apply ring_agroup_plus.
    assumption. }
Qed.

Theorem ring_mult_minus_right (a b: R):
  mult a (minus b) = minus (mult a b).
Proof.
  cut (AbelianGroup plus zero minus).
  { intros Ragroup_plus.
    apply (agroup_minus_unique plus zero minus);
      rewrite <- ring_distrib_left.
    rewrite (agroup_inv plus zero minus).
    apply ring_right_mult_zero. }
  { apply ring_agroup_plus.
    assumption. }
Qed.

Theorem ring_mult_minus_minus (a b: R):
  mult (minus a) (minus b) = mult a b.
Proof.
  cut (AbelianGroup plus zero minus).
  { intros Ragroup_plus.
    rewrite ring_mult_minus_left.
    rewrite ring_mult_minus_right.
    apply (agroup_minus_involute plus zero minus). }
  { apply ring_agroup_plus.
    assumption. }
Qed.
End RingTheory.
