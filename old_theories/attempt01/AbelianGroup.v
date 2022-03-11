Require Import Algebra.Semigroup.
Require Import Algebra.Monoid.
Require Import Algebra.Group.
Section AbelianGroupTheory.
Context {G: Set}(plus: G -> G -> G)(zero: G)(minus: G -> G).

Class AbelianGroup := {
  agroup_assoc: forall (a b c: G), plus (plus a b) c = plus a (plus b c);
  agroup_comm: forall (a b: G), plus a b = plus b a;
  agroup_ident: forall (a: G), plus a zero = a;
  agroup_inv: forall (a: G), plus a (minus a) = zero;
}.

Theorem agroup_group:
  AbelianGroup -> Group plus zero minus.
Proof.
  intros Gagroup.
  constructor.
  { apply agroup_assoc. }
  { intros a.
    rewrite agroup_comm.
    apply agroup_ident. }
  { apply agroup_ident. }
  { intros a.
    rewrite agroup_comm.
    apply agroup_inv. }
  { apply agroup_inv. }
Qed.

Theorem comm_group_abelian:
  Commutative plus ->
  Group plus zero minus ->
  AbelianGroup.
Proof.
  intros Gcomm Ggroup.
  constructor.
  { apply (group_assoc plus zero minus). }
  { apply (commutative plus). }
  { apply (group_ident_right plus zero minus). }
  { apply (group_inv_right plus zero minus). }
Qed.

Theorem agroup_monoid:
  AbelianGroup -> Monoid plus zero.
Proof.
  intros Gagroup.
  apply (group_monoid plus zero minus).
  apply agroup_group.
  assumption.
Qed.

Theorem agroup_semigroup:
  AbelianGroup -> Semigroup plus.
Proof.
  intros Ggroup.
  constructor.
  apply agroup_assoc.
Qed.

Context `{Gagroup: AbelianGroup}.

Lemma agroup_zero_left (a: G):
  plus zero a = a.
Proof.
  rewrite agroup_comm.
  apply agroup_ident.
Qed.

Lemma agroup_zero_right (a: G):
  plus a zero = a.
Proof.
  apply agroup_ident.
Qed.

Lemma agroup_minus_left (a: G):
  plus (minus a) a = zero.
Proof.
  rewrite agroup_comm.
  apply agroup_inv.
Qed.

Lemma agroup_minus_right (a: G):
  plus a (minus a) = zero.
Proof.
  apply agroup_inv.
Qed.

Lemma agroup_plus (a b: G):
  a = b -> forall (c: G), plus a c = plus b c.
Proof.
  intros <-;
    reflexivity.
Qed.

Definition agroup_plus_right := agroup_plus.

Lemma agroup_plus_left (a b: G):
  a = b -> forall (c: G), plus c a = plus c b.
Proof.
  intros <-;
    reflexivity.
Qed.

Theorem agroup_zero_unique (ident': G):
  (forall (a: G), plus a ident' = a) ->
  ident' = zero.
Proof.
  intros Hident'.
  rewrite <- (Hident' zero).
  rewrite <- (agroup_ident ident').
  generalize (plus ident' zero) as e.
  intros e.
  rewrite agroup_zero_left.
  reflexivity.
Qed.

Theorem agroup_idemp_zero (a: G):
  plus a a = a ->
  a = zero.
Proof.
  apply agroup_group in Gagroup.
  apply (group_idemp_ident plus zero minus).
Qed.

Theorem agroup_left_cancel (a b c: G):
  plus c a = plus c b -> a = b.
Proof.
  apply agroup_group in Gagroup.
  apply (group_left_cancel plus zero minus).
Qed.

Theorem agroup_right_cancel (a b c: G):
  plus a c = plus b c -> a = b.
Proof.
  apply agroup_group in Gagroup.
  apply (group_right_cancel plus zero minus).
Qed.

Theorem agroup_minus_unique (a aInv: G):
  plus a aInv = zero ->
  aInv = minus a.
Proof.
  intros Hrinv.
  rewrite <- (agroup_minus_right a) in Hrinv.
  apply agroup_left_cancel in Hrinv.
  assumption.
Qed.

Theorem agroup_minus_involute (a: G):
  minus (minus a) = a.
Proof.
  apply agroup_group in Gagroup.
  apply (group_inv_involute plus zero minus).
Qed.

Theorem agroup_minus_plus (a b: G):
  minus (plus a b) = plus (minus a) (minus b).
Proof.
  symmetry.
  apply agroup_minus_unique;
    rewrite agroup_assoc.
  remember (plus (minus a) (minus b)) as mapmb.
  rewrite agroup_comm in Heqmapmb.
  subst mapmb.
  remember (plus b (plus (minus b) (minus a))) as minusa.
  rewrite <- agroup_assoc in Heqminusa.
  rewrite agroup_inv in Heqminusa.
  rewrite agroup_zero_left in Heqminusa.
  subst minusa.
  apply agroup_inv.
Qed.

Theorem agroup_left_plus_soln (a b: G):
  exists! (x: G), plus a x = b.
Proof.
  apply agroup_group in Gagroup.
  apply (group_left_mult_soln plus zero minus).
Qed.

Theorem agroup_right_plus_soln (a b: G):
  exists! (x: G), plus x a = b.
Proof.
  apply agroup_group in Gagroup.
  apply (group_right_mult_soln plus zero minus).
Qed.

Theorem group_minus_ident:
  minus zero = zero.
Proof.
  symmetry.
  apply agroup_minus_unique.
  apply agroup_ident.
Qed.
End AbelianGroupTheory.

Section CommSemigroupTheory.
Context {G: Set}(plus: G -> G -> G).
Context `{Gsubgroup: Semigroup G plus}.
Context `{Gcomm: Commutative G plus}.
Context (zero: G)(minus: G -> G).

Theorem agroup_semigroup_left_zero_left_minus:
  (Monoid plus zero /\ AbelianGroup plus zero minus) ->
  forall (a: G), plus zero a = a /\ plus (minus a) a = zero.
Proof.
  intros [Gmonoid Gagroup] a.
  apply agroup_group in Gagroup.
  apply group_semigroup_left_ident_left_inv.
  split;
    assumption.
Qed.

Theorem agroup_semigroup_right_zero_right_minus:
  (Monoid plus zero /\ AbelianGroup plus zero minus) ->
  forall (a: G), plus a zero = a /\ plus a (minus a) = zero.
Proof.
  intros [Gmonoid Gagroup] a.
  apply agroup_group in Gagroup.
  apply group_semigroup_right_ident_right_inv.
  split;
    assumption.
Qed.

Theorem semigroup_left_zero_left_minus_group:
  (forall (a: G), plus zero a = a) ->
  (forall (a: G), plus (minus a) a = zero) ->
  Monoid plus zero /\ AbelianGroup plus zero minus.
Proof.
  intros Hlzero Hlminus.
  cut (forall (a: G), plus a (minus a) = zero).
  { intros Hrminus.
    split;
      constructor;
      try apply semigroup_assoc;
      try apply commutative;
      try assumption;
    intros a;
    rewrite <- (Hlminus a);
    rewrite <- semigroup_assoc;
      try assumption;
    rewrite Hrminus;
    apply Hlzero. }
  { intros a.
    apply (semigroup_left_ident_left_inv_idemp_ident plus zero minus);
      try assumption.
    rewrite semigroup_assoc;
      try assumption.
    remember (plus (minus a) (plus a (minus a))) as minusa.
    rewrite <- semigroup_assoc in Heqminusa;
      try assumption.
    rewrite Hlminus in Heqminusa.
    rewrite Hlzero in Heqminusa.
    subst minusa.
    reflexivity. }
Qed.

Theorem semigroup_right_zero_right_minus_group:
  (forall (a: G), plus a zero = a) ->
  (forall (a: G), plus a (minus a) = zero) ->
  Monoid plus zero /\ Group plus zero minus.
Proof.
  intros Hrzero Hrminus.
  cut (forall (a: G), plus (minus a) a = zero).
  { intros Hlminus.
    split;
      constructor;
      try apply semigroup_assoc;
      try assumption;
    intros a;
    rewrite <- (Hrminus a);
    rewrite semigroup_assoc;
      try assumption;
    rewrite Hlminus;
    rewrite Hrzero;
    reflexivity. }
  { intros a.
    apply (semigroup_right_ident_right_inv_idemp_ident plus zero minus);
      try assumption.
    rewrite <- semigroup_assoc;
      try assumption.
    remember (plus (plus (minus a) a) (minus a)) as minusa.
    rewrite semigroup_assoc in Heqminusa;
      try assumption.
    rewrite Hrminus in Heqminusa.
    rewrite Hrzero in Heqminusa.
    subst minusa.
    reflexivity. }
Qed.
End CommSemigroupTheory.
