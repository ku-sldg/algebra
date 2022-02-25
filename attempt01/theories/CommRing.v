Require Import Algebra.Semigroup.
Require Import Algebra.Monoid.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Algebra.Ring.

Section CommRingTheory.
Context {R: Set}(plus: R -> R -> R)(zero: R)(minus: R -> R).
Context (mult: R -> R -> R)(one: R).

Class CommRing := {
  cring_plus_assoc: forall (a b c: R), plus (plus a b) c = plus a (plus b c);
  cring_plus_comm: forall (a b: R), plus a b = plus b a;
  cring_plus_ident: forall (a: R), plus a zero = a;
  cring_plus_inv: forall (a: R), plus a (minus a) = zero;
  cring_mult_assoc: forall (a b c: R), mult (mult a b) c = mult a (mult b c);
  cring_mult_comm: forall (a b: R), mult a b = mult b a;
  cring_mult_ident: forall (a: R), mult a one = a;
  cring_distrib: forall (a b c: R), mult a (plus b c) = plus (mult a b) (mult a c);
}.


Lemma cring_ring:
  CommRing -> Ring plus zero minus mult.
Proof.
  intros Rcring.
  constructor.
  { apply cring_plus_assoc. }
  { apply cring_plus_comm. }
  { apply cring_plus_ident. }
  { apply cring_plus_inv. }
  { apply cring_mult_assoc. }
  { apply cring_distrib. }
  { intros a b c.
    rewrite cring_mult_comm.
    remember (mult b a) as ba.
    rewrite cring_mult_comm in Heqba.
    subst ba.
    remember (mult c a) as ca.
    rewrite cring_mult_comm in Heqca.
    subst ca.
    apply cring_distrib. }
Qed.

Lemma cring_agroup_plus:
  CommRing -> AbelianGroup plus zero minus.
Proof.
  intros Rcring.
  apply cring_ring in Rcring.
  apply (ring_agroup_plus plus zero minus mult).
  assumption.
Qed.

Lemma cring_comm_monoid_mult:
  CommRing ->
  Monoid mult one /\ Commutative mult.
Proof.
  intros Rcring.
  split;
    constructor.
  { apply cring_mult_assoc. }
  { intros a.
    rewrite cring_mult_comm.
    apply cring_mult_ident. }
  { apply cring_mult_ident. }
  { apply cring_mult_comm. }
Qed.

Lemma agroup_plus_semigroup_mult_distrib_ring:
  AbelianGroup plus zero minus ->
  Monoid mult one ->
  Commutative mult ->
  (forall (a b c: R), mult a (plus b c) = plus (mult a b) (mult a c)) ->
  CommRing.
Proof.
  intros Ragroup_plus Rmon_mult Rcomm_mult Hd.
  constructor;
    try assumption.
  { apply semigroup_assoc.
    apply (agroup_semigroup plus zero minus).
    assumption. }
  { apply (agroup_comm plus zero minus). }
  { apply (agroup_ident plus zero minus). }
  { apply (agroup_inv plus zero minus). }
  { apply (monoid_assoc mult one). }
  { apply (commutative mult). }
  { apply (monoid_ident_right mult one). }
Qed.

Context `{Rcring: CommRing}.

Theorem cring_left_mult_zero (a: R):
  mult zero a = zero.
Proof.
  apply cring_ring in Rcring.
  apply (ring_left_mult_zero plus zero minus mult).
Qed.

Theorem cring_right_mult_zero (a: R):
  mult a zero = zero.
Proof.
  apply cring_ring in Rcring.
  apply (ring_right_mult_zero plus zero minus mult).
Qed.

Theorem cring_mult_minus_left (a b: R):
  mult (minus a) b = minus (mult a b).
Proof.
  apply cring_ring in Rcring.
  apply (ring_mult_minus_left plus zero minus mult).
Qed.

Theorem cring_mult_minus_right (a b: R):
  mult a (minus b) = minus (mult a b).
Proof.
  apply cring_ring in Rcring.
  apply (ring_mult_minus_right plus zero minus mult).
Qed.

Theorem cring_mult_minus_minus (a b: R):
  mult (minus a) (minus b) = mult a b.
Proof.
  apply cring_ring in Rcring.
  apply (ring_mult_minus_minus plus zero minus mult).
Qed.
End CommRingTheory.

Section Ideals.
Context {R: Set}(plus: R -> R -> R)(zero: R)(minus: R -> R).
Context (mult: R -> R -> R)(one: R).
Context `{Rcring: CommRing R plus zero minus mult one}.
Context (P: R -> Prop).

Class Ideal := {
  ideal_plus_closed: forall (a b: R), P a -> P b -> P (plus a b);
  ideal_zero: P zero;
  ideal_minus_closed: forall (a: R), P a -> P (minus a);
  ideal_mult_absorb: forall (a: R), P a -> forall (r: R), P (mult a r);
}.

Theorem ideal_subtract_closed:
  Ideal ->
  forall (a b: R), P a -> P b -> P (plus a (minus b)).
Proof.
  intros Pideal.
  intros a b Pa Pb.
  apply ideal_plus_closed;
    try assumption.
  apply ideal_minus_closed;
    assumption.
Qed.

Theorem subset_subtract_closed_mult_absorb_ideal:
  {a: R | P a} ->
  (forall (a b: R), P a -> P b -> P (plus a (minus b))) ->
  (forall (a: R), P a -> forall (r: R), P (mult a r)) ->
  Ideal.
Proof.
  intros [r Pr] Hsubtract Habsorb.
  cut (Subgroup plus zero minus P).
  { intros Psubgroup.
    constructor;
      try assumption.
    { apply (subgroup_mult_closed plus zero minus).
      assumption. }
    { apply (subgroup_ident plus zero minus).
      assumption. }
    { apply (subgroup_inv_closed plus zero minus).
      assumption. } }
  { apply subset_mult_inv_closed_subgroup;
      try assumption.
    { apply cring_agroup_plus in Rcring.
      apply agroup_monoid in Rcring.
      assumption.  }
    { apply cring_agroup_plus in Rcring.
      apply agroup_group in Rcring.
      assumption. }
    { exists r.
      assumption. } }
Qed.

Context `{Pideal: Ideal}.

Lemma ideal_one_entire:
  P one ->
  forall (r: R), P r.
Proof.
  intros Pone r.
  rewrite <- (cring_mult_ident plus zero minus mult one).
  rewrite (cring_mult_comm plus zero minus mult one).
  apply ideal_mult_absorb.
  assumption.
Qed.

Theorem ideal_unit_entire:
  {u: R | P u /\ exists (uInv: R), mult u uInv = one} ->
  forall (r: R), P r.
Proof.
  intros [u [Pu HuInv]] r.
  inversion_clear HuInv as [uInv HuuInv].
  apply ideal_one_entire.
  rewrite <- HuuInv.
  apply ideal_mult_absorb.
  assumption.
Qed.
End Ideals.

Section KindsOfIdeals.
Context {R: Set}(plus: R -> R -> R)(zero: R)(minus: R -> R).
Context (mult: R -> R -> R)(one: R).
Context `{Rcring: CommRing R plus zero minus mult one}.
Context (P: R -> Prop).
Context `{Pideal: Ideal R plus zero minus mult P}.

Definition prime_ideal :=
  forall (a b: R), P (mult a b) -> P a \/ P b.

Definition maximal_ideal :=
  forall (Q: R -> Prop)`{_: Ideal R plus zero minus mult Q},
    (exists (r: R), ~ (P r)) ->
    (forall (r: R), P r -> Q r) ->
    (forall (r: R), Q r) \/ (forall (r: R), Q r -> P r).
End KindsOfIdeals.

Section LocalRing.
Context {R: Set}(plus: R -> R -> R)(zero: R)(minus: R -> R).
Context (mult: R -> R -> R)(one: R).
Context `{Rcring: CommRing R plus zero minus mult one}.

Definition local_ring :=
  exists! (P: R -> Prop),
    forall `{Pideal: Ideal R plus zero minus mult P},
      maximal_ideal plus zero minus mult P.
End LocalRing.