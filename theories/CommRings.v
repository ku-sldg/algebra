Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From algebra Require Import Semigroups Monoids Groups.
From algebra Require Import AbelianGroups Rings.

Section CommRings.
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
Context (one: Carrier).

Infix "~" := equiv (at level 60, no associativity).
Infix "<+>" := add (at level 50, left associativity).
Infix "<*>" := mul (at level 40, left associativity).

Class CommRing := {
  comm_ring :> Ring equiv add zero minus mul;
  comm_ring_mul_monoid :> Monoid equiv mul one;
  comm_ring_mul_comm :> Commutative equiv mul;
}.

Context {cring: CommRing}.

Section Ideals.
Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.

Class Ideal := {
  ideal_add_subgroup :> Subgroup add zero minus P;
  ideal_mul_absorb_r:
    forall (a: Carrier),
      P a -> forall (r: Carrier), P (r <*> a);
}.

Theorem subset_subtract_closed_mul_absorb_ideal:
  (exists (a: Carrier), P a) ->
  (forall (a b: Carrier),
    P a -> P b -> P (a <+> minus b)) ->
  (forall (a: Carrier),
    P a -> forall (r: Carrier), P (r <*> a)) ->
  Ideal.
Proof.
  intros Hx Hsubtract Habsorb.
  constructor;
    [apply (subset_op_inv_closed_subgroup equiv add zero minus) |];
    assumption.
Qed.

Context {ideal: Ideal}.

Theorem ideal_mul_absorb_l (a: Carrier):
  P a -> forall (r: Carrier), P (a <*> r).
Proof.
  intros HPa r.
  assert (a <*> r ~ r <*> a) by apply comm_ring_mul_comm.
  apply P_proper in H.
  apply H.
  apply ideal_mul_absorb_r.
  assumption.
Qed.

Lemma ideal_one_entire:
  P one ->
  forall (r: Carrier), P r.
Proof.
  intros Pone r.
  assert (r <*> one ~ r)
    by apply (monoid_ident_r equiv mul one).
  apply P_proper in H.
  apply H.
  apply ideal_mul_absorb_r.
  assumption.
Qed.

Theorem ideal_unit_entire:
  (exists (u: Carrier),
    P u /\ exists (uInv: Carrier), u <*> uInv ~ one) ->
  forall (r: Carrier), P r.
Proof.
  intros [u [Pu [uInv Hinv]]] r.
  apply ideal_one_entire.
  apply P_proper in Hinv.
  apply Hinv.
  apply ideal_mul_absorb_l.
  assumption.
Qed.

Let quot_congru := left_congru add minus P.

Lemma quotient_ideal_mul_proper:
  Proper (quot_congru ==> quot_congru ==> quot_congru) mul.
Proof.
  intros a0 a1 Ha b0 b1 Hb.
  assert (minus (a0 <*> b0) <+> a1 <*> b1 ~ (minus a0 <+> a1) <*> b0 <+> a1 <*> (minus b0 <+> b1)).
  { transitivity (minus a0 <*> b0 <+> a1 <*> b1);
      [symmetry;
        apply (semigroup_op_r equiv add);
        apply (ring_mul_minus_l equiv add zero minus mul) |].
    transitivity (minus a0 <*> b0 <+> zero <+> a1 <*> b1);
      [symmetry;
        apply (semigroup_op_r equiv add);
        apply (monoid_ident_r equiv add zero) |].
    transitivity (minus a0 <*> b0 <+> (a1 <*> b0 <+> minus (a1 <*> b0)) <+> a1 <*> b1);
      [symmetry;
        apply (semigroup_op_r equiv add);
        apply (semigroup_op_l equiv add);
        apply (group_inv_r equiv add zero minus) |].
    transitivity (minus a0 <*> b0 <+> a1 <*> b0 <+> minus (a1 <*> b0) <+> a1 <*> b1);
      [symmetry;
        apply (semigroup_op_r equiv add);
        apply (semigroup_assoc equiv add) |].
    transitivity ((minus a0 <+> a1) <*> b0 <+> minus (a1 <*> b0) <+> a1 <*> b1);
      [symmetry;
        repeat apply (semigroup_op_r equiv add);
        apply (ring_distrib_r equiv add zero minus mul) |].
    transitivity ((minus a0 <+> a1) <*> b0 <+> (minus (a1 <*> b0) <+> a1 <*> b1));
      [apply (semigroup_assoc equiv add) |].
    apply (semigroup_op_l equiv add).
    transitivity (a1 <*> minus b0 <+> a1 <*> b1);
      [apply (semigroup_op_r equiv add);
        symmetry;
        apply (ring_mul_minus_r equiv add zero minus mul) |].
    symmetry.
    apply (ring_distrib_l equiv add zero minus mul). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_op_closed add zero minus P);
      [ apply ideal_mul_absorb_l | apply ideal_mul_absorb_r];
      assumption. }
Qed.

Lemma quotient_ideal_mul_comm:
  Commutative quot_congru mul.
Proof.
  constructor.
  intros a b.
  assert (minus (a <*> b) <+> b <*> a ~ zero).
  { transitivity (minus (a <*> b) <+> a <*> b);
      [apply (semigroup_op_l equiv add);
        apply comm_ring_mul_comm |].
    apply (group_inv_l equiv add zero minus). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident add zero minus P). }
Qed.

Lemma quotient_ideal_mul_semigroup:
  Semigroup quot_congru mul.
Proof.
  constructor.
  intros a b c.
  assert (minus (a <*> b <*> c) <+> (a <*> (b <*> c)) ~ zero).
  { symmetry.
    apply (group_move_l equiv add zero minus).
    transitivity (a <*> b <*> c);
      [apply (monoid_ident_r equiv add zero)
      | apply (semigroup_assoc equiv mul)]. }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident add zero minus P). }
Qed.

Lemma quotient_ideal_distrib_l (a b c: Carrier):
  quot_congru (a <*> (b <+> c)) (a <*> b <+> a <*> c).
Proof.
  assert (minus (a <*> (b <+> c)) <+> (a <*> b <+> a <*> c) ~ zero).
  { symmetry.
    apply (group_move_l equiv add zero minus).
    transitivity (a <*> (b <+> c));
      [apply (monoid_ident_r equiv add zero)
      | apply (ring_distrib_l equiv add zero minus mul)]. }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident add zero minus P). }
Qed.

Lemma quotient_ideal_distrib_r (a b c: Carrier):
  quot_congru ((b <+> c) <*> a)  (b <*> a <+> c <*> a).
  Proof.
    assert (minus ((b <+> c) <*> a) <+> (b <*> a <+> c <*> a) ~ zero).
    { symmetry.
      apply (group_move_l equiv add zero minus).
      transitivity ((b <+> c) <*> a);
        [apply (monoid_ident_r equiv add zero)
        | apply (ring_distrib_r equiv add zero minus mul)]. }
    { apply P_proper in H.
      apply H.
      apply (subgroup_ident add zero minus P). }
Qed.
  
Lemma quotient_ideal_mul_1_r (a: Carrier):
  quot_congru (a <*> one) a.
Proof.
  assert (minus (a <*> one) <+> a ~ zero).
  { symmetry.
    apply (group_move_l equiv add zero minus).
    transitivity (a <*> one);
      [apply (monoid_ident_r equiv add zero)
      | apply (monoid_ident_r equiv mul one)]. }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident add zero minus P). }
Qed.

Lemma quotient_ideal_mul_1_l (a: Carrier):
  quot_congru (one <*> a) a.
Proof.
  assert (minus (one <*> a) <+> a ~ zero).
  { symmetry. 
    apply (group_move_l equiv add zero minus).
    transitivity (one <*> a);
      [apply (monoid_ident_r equiv add zero)
      | apply (monoid_ident_l equiv mul one)]. }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident add zero minus P). }
Qed.
End Ideals.
End CommRings.

Section Ideals.
Context {Carrier: Set}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (add: Carrier -> Carrier -> Carrier).
Context {add_proper: Proper (equiv ==> equiv ==> equiv) add}.
Context (zero: Carrier).
Context (minus: Carrier -> Carrier).
Context {minus_proper: Proper (equiv ==> equiv) minus}.
Context (mul: Carrier -> Carrier -> Carrier).
Context {mul_proper: Proper (equiv ==> equiv ==> equiv) mul}.
Context (one: Carrier).
Context {comm_ring: CommRing equiv add zero minus mul one}.
Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.
Context {ideal: Ideal add zero minus mul P}.

Infix "~" := equiv (at level 60, no associativity).
Infix "<+>" := add (at level 50, left associativity).
Infix "<*>" := mul (at level 40, left associativity).

Let quot_congru := left_congru add minus P.

Theorem quotient_ideal_comm_ring:
  CommRing quot_congru add zero minus mul one.
Proof.
  constructor.
  { constructor.
    apply (quotient_subgroup_abelian equiv add zero minus _ P).
    apply (quotient_ideal_mul_semigroup equiv add zero minus mul one P).
    apply (quotient_ideal_distrib_l equiv add zero minus mul one P).
    apply (quotient_ideal_distrib_r equiv add zero minus mul one P). }
  { constructor.
    apply (quotient_ideal_mul_semigroup equiv add zero minus mul one P).
    apply (quotient_ideal_mul_1_l equiv add zero minus mul one P).
    apply (quotient_ideal_mul_1_r equiv add zero minus mul one P). }
  { constructor.
    apply (quotient_ideal_mul_comm equiv add zero minus mul one P). }
Qed.

Definition prime_ideal :=
  forall (a b: Carrier), P (a <*> b) -> P a \/ P b.

Definition maximal_ideal :=
  forall (Q: Carrier -> Prop),
    (exists (r: Carrier), ~ (P r)) ->
    (forall (r: Carrier), P r -> Q r) ->
    (forall (r: Carrier), Q r) \/
      (forall (r: Carrier), Q r -> P r).
End Ideals.

Section LocalRing.
Context {Carrier: Set}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (add: Carrier -> Carrier -> Carrier).
Context {add_proper: Proper (equiv ==> equiv ==> equiv) add}.
Context (zero: Carrier).
Context (minus: Carrier -> Carrier).
Context {minus_proper: Proper (equiv ==> equiv) minus}.
Context (mul: Carrier -> Carrier -> Carrier).
Context {mul_proper: Proper (equiv ==> equiv ==> equiv) mul}.
Context (one: Carrier).
Context {comm_ring: CommRing equiv add zero minus mul one}.
Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.
Context {ideal: Ideal add zero minus mul P}.

Definition local_ring :=
  exists! (P: Carrier -> Prop),
      maximal_ideal P.
End LocalRing.
