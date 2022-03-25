Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
From algebra Require Import Semigroups Monoids Groups AbelianGroups Rings.
From Coq.Logic Require Import Classical_Pred_Type Classical_Prop.
Require Import Setoid.

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

Infix "==" := equiv (at level 60, no associativity).
Infix "<+>" := add (at level 50, left associativity).
Infix "<*>" := mul (at level 40, left associativity).

Class CommRing := {
  comm_ring :> Ring equiv add zero minus mul;
  comm_ring_mul_monoid :> Monoid equiv mul one;
  comm_ring_mul_comm :> Commutative equiv mul;
}.

Context {cring: CommRing}.

Definition is_unit (u: Carrier) :=
  exists (uInv: Carrier), u <*> uInv == one.

Theorem comm_ring_units_closed_mul (u0 u1: Carrier):
  is_unit u0 ->
  is_unit u1 ->
  is_unit (u0 <*> u1).
Proof.
  unfold is_unit.
  intros [u0Inv Hu0] [u1Inv Hu1].
  exists (u1Inv <*> u0Inv).
  setoid_rewrite <- (semigroup_assoc equiv mul).
  transitivity (u0Inv <*> (u0 <*> u1 <*> u1Inv));
    [apply comm_ring_mul_comm |].
  repeat setoid_rewrite <- (semigroup_assoc equiv mul).
  transitivity (u0 <*> u0Inv <*> u1 <*> u1Inv);
    [repeat apply (semigroup_op_r equiv mul);
      apply comm_ring_mul_comm |].
  setoid_rewrite Hu0.
  setoid_rewrite (monoid_ident_l equiv mul one).
  apply Hu1.
Qed.

Theorem comm_ring_nonunits_absorb_mul (r: Carrier):
  ~ is_unit r ->
  forall (s: Carrier), ~ is_unit (r <*> s).
Proof.
  unfold is_unit.
  intros Hnonunit s [rsInv Hcontra].
  apply Hnonunit.
  exists (s <*> rsInv).
  setoid_rewrite <- (semigroup_assoc equiv mul).
  apply Hcontra.
Qed.

Section Ideals.
Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.

Class Ideal := {
  ideal_add_subgroup :> Subgroup add zero minus P;
  ideal_mul_absorb_l:
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

Theorem ideal_mul_absorb_r (a: Carrier):
  P a -> forall (r: Carrier), P (a <*> r).
Proof.
  intros HPa r.
  assert (a <*> r == r <*> a) by apply comm_ring_mul_comm.
  apply P_proper in H.
  apply H.
  apply ideal_mul_absorb_l.
  assumption.
Qed.

Lemma ideal_1_entire:
  P one ->
  forall (r: Carrier), P r.
Proof.
  intros Pone r.
  assert (r <*> one == r)
    by apply (monoid_ident_r equiv mul one).
  apply P_proper in H.
  apply H.
  apply ideal_mul_absorb_l.
  assumption.
Qed.

Theorem ideal_unit_entire:
  (exists (u: Carrier),
    P u /\ is_unit u) ->
  forall (r: Carrier), P r.
Proof.
  intros [u [Pu [uInv Hinv]]] r.
  apply ideal_1_entire.
  apply P_proper in Hinv.
  apply Hinv.
  apply ideal_mul_absorb_r.
  assumption.
Qed.

Let quot_congru := left_congru add minus P.

Lemma quotient_ideal_mul_proper:
  Proper (quot_congru ==> quot_congru ==> quot_congru) mul.
Proof.
  intros a0 a1 Ha b0 b1 Hb.
  assert (minus (a0 <*> b0) <+> a1 <*> b1 == (minus a0 <+> a1) <*> b0 <+> a1 <*> (minus b0 <+> b1)).
  { setoid_rewrite <- (ring_mul_minus_l equiv add zero minus mul).
    transitivity (minus a0 <*> b0 <+> zero <+> a1 <*> b1);
      [symmetry;
        apply (semigroup_op_r equiv add);
        apply (monoid_ident_r equiv add zero) |].
    setoid_rewrite <- (group_inv_r equiv add zero minus (a1 <*> b0)).
    setoid_rewrite <- (semigroup_assoc equiv add).
    setoid_rewrite <- (ring_distrib_r equiv add zero minus mul).
    setoid_rewrite (semigroup_assoc equiv add).
    apply (semigroup_op_l equiv add).
    setoid_rewrite <- (ring_mul_minus_r equiv add zero minus mul).
    setoid_rewrite <- (ring_distrib_l equiv add zero minus mul).
    reflexivity. }
  { apply P_proper in H.
    apply H.
    apply (subgroup_op_closed add zero minus P);
      [ apply ideal_mul_absorb_r | apply ideal_mul_absorb_l];
      assumption. }
Qed.

Lemma quotient_ideal_mul_comm:
  Commutative quot_congru mul.
Proof.
  constructor.
  intros a b.
  assert (minus (a <*> b) <+> b <*> a == zero).
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
  assert (minus (a <*> b <*> c) <+> (a <*> (b <*> c)) == zero).
  { symmetry.
    apply (group_move_l equiv add zero minus).
    setoid_rewrite (monoid_ident_r equiv add zero).
    apply (semigroup_assoc equiv mul). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident add zero minus P). }
Qed.

Lemma quotient_ideal_distrib_l (a b c: Carrier):
  quot_congru (a <*> (b <+> c)) (a <*> b <+> a <*> c).
Proof.
  assert (minus (a <*> (b <+> c)) <+> (a <*> b <+> a <*> c) == zero).
  { symmetry.
    apply (group_move_l equiv add zero minus).
    setoid_rewrite (monoid_ident_r equiv add zero).
    apply (ring_distrib_l equiv add zero minus mul). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident add zero minus P). }
Qed.

Lemma quotient_ideal_distrib_r (a b c: Carrier):
  quot_congru ((b <+> c) <*> a)  (b <*> a <+> c <*> a).
  Proof.
    assert (minus ((b <+> c) <*> a) <+> (b <*> a <+> c <*> a) == zero).
    { symmetry.
      apply (group_move_l equiv add zero minus).
      setoid_rewrite (monoid_ident_r equiv add zero).
      apply (ring_distrib_r equiv add zero minus mul). }
    { apply P_proper in H.
      apply H.
      apply (subgroup_ident add zero minus P). }
Qed.
  
Lemma quotient_ideal_mul_1_r (a: Carrier):
  quot_congru (a <*> one) a.
Proof.
  assert (minus (a <*> one) <+> a == zero).
  { symmetry.
    apply (group_move_l equiv add zero minus).
    setoid_rewrite (monoid_ident_r equiv add zero).
    apply (monoid_ident_r equiv mul one). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident add zero minus P). }
Qed.

Lemma quotient_ideal_mul_1_l (a: Carrier):
  quot_congru (one <*> a) a.
Proof.
  assert (minus (one <*> a) <+> a == zero).
  { symmetry. 
    apply (group_move_l equiv add zero minus).
    setoid_rewrite (monoid_ident_r equiv add zero).
    apply (monoid_ident_l equiv mul one). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident add zero minus P). }
Qed.
End Ideals.
End CommRings.

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
Context {cring: CommRing equiv add zero minus mul one}.

Infix "==" := equiv (at level 60, no associativity).
Infix "<+>" := add (at level 50, left associativity).
Infix "<*>" := mul (at level 40, left associativity).

Section Ideals.
Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.
Context {ideal: Ideal add zero minus mul P}.

Let quot_congru := left_congru add minus P.

Theorem quotient_ideal_comm_ring:
  CommRing quot_congru add zero minus mul one.
Proof.
  constructor.
  { constructor.
    apply (quotient_subagroup equiv add zero minus _ P).
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
  exists (r: Carrier), (not (P r) /\
    forall (Q: Carrier -> Prop)(Q_proper: Proper (equiv ==> iff) Q)(Q_ideal: Ideal add zero minus mul Q),
      (forall (r: Carrier), P r -> Q r) ->
      (forall (r: Carrier), Q r) \/
        (forall (r: Carrier), Q r -> P r)).

Lemma comm_ring_maximal_ideal_omits_1:
  maximal_ideal ->
  ~ P one.
Proof.
  intros [r [HPr' Hother_ideals]] Hcontra.
  apply (ideal_1_entire equiv add zero minus mul one P) with (r := r) in Hcontra.
  apply HPr'.
  assumption.
Qed.
End Ideals.

Section LocalRing.
(* Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.
Context {ideal: Ideal add zero minus mul P}. *)

Definition local_ring :=
  exists (P: Carrier -> Prop)(P_proper: Proper (equiv ==> iff) P)(P_ideal: Ideal add zero minus mul P),
      maximal_ideal P /\
      (forall (Q: Carrier -> Prop)(Q_proper: Proper (equiv ==> iff) Q)(Q_ideal: Ideal add zero minus mul Q),
        maximal_ideal Q -> forall (r: Carrier), P r <-> Q r).

Axiom comm_ring_nonunit_maximal_ideal:
  forall (x: Carrier),
    ~ is_unit equiv mul one x ->
    exists (P: Carrier -> Prop)(P_proper: Proper (equiv ==> iff) P)(P_ideal: Ideal add zero minus mul P),
      P x /\ maximal_ideal P.

Theorem local_comm_ring_sub_1_nonunit:
  local_ring ->
  forall (x: Carrier),
    ~ is_unit equiv mul one x ->
    is_unit equiv mul one (one <+> minus x).
Proof.
  unfold local_ring.
  intros [M [M_proper [M_ideal [HM_maximal HM_unique]]]] x Hx_nonunit.
  apply comm_ring_nonunit_maximal_ideal in Hx_nonunit.
  inversion_clear Hx_nonunit as [P [P_proper [P_ideal [HPx HP_maximal]]]].
  apply (HM_unique P P_proper P_ideal HP_maximal) in HPx.
  apply NNPP.
  intros Hcontra.
  apply comm_ring_nonunit_maximal_ideal in Hcontra.
  inversion_clear Hcontra as [Q [Q_proper [Q_ideal [HQ1mx HQ_maximal]]]].
  apply (HM_unique Q Q_proper Q_ideal HQ_maximal) in HQ1mx.
  apply (comm_ring_maximal_ideal_omits_1 M HM_maximal).
  assert (one == one <+> minus x <+> x).
  { setoid_rewrite (semigroup_assoc equiv add).
    setoid_rewrite (group_inv_l equiv add zero minus).
    symmetry.
    apply (monoid_ident_r equiv add zero). }
  { apply M_proper in H.
    apply H.
    apply (subgroup_op_closed add zero minus M);
      assumption. }
Qed.
End LocalRing.

Section PrincipalIdeal.
Definition principal_ideal (x: Carrier): Carrier -> Prop :=
  fun y => exists (r: Carrier), y == r <*> x.

Lemma principal_ideal_proper:
  Proper (equiv ==> equiv ==> iff) principal_ideal.
Proof.
  intros x0 x1 Hx y0 y1 Hy.
  split;
    [intros [r0 Hr] | intros [r1 Hr]].
  { exists r0.
    setoid_rewrite <- Hy.
    setoid_rewrite Hr.
    apply (semigroup_op_l equiv mul).
    assumption. }
  { exists r1.
    setoid_rewrite Hy.
    setoid_rewrite Hr.
    apply (semigroup_op_l equiv mul).
    symmetry.
    assumption. }
Qed.

Context (x: Carrier).

Lemma principal_ideal_add_closed (a b: Carrier):
  principal_ideal x a ->
  principal_ideal x b ->
  principal_ideal x (a <+> b).
Proof.
  intros [r Hr] [s Hs].
  exists (r <+> s).
  setoid_rewrite Hr.
  setoid_rewrite Hs.
  symmetry.
  apply (ring_distrib_r equiv add zero minus mul).
Qed.

Lemma principal_ideal_minus_closed (a: Carrier):
  principal_ideal x a ->
  principal_ideal x (minus a).
Proof.
  intros [r Hr].
  exists (minus r).
  setoid_rewrite Hr.
  symmetry.
  apply (ring_mul_minus_l equiv add zero minus mul).
Qed.

Lemma principal_ideal_zero:
  principal_ideal x zero.
Proof.
  exists zero.
  symmetry.
  apply (ring_mul_0_l equiv add zero minus mul).
Qed.

#[global]
Instance principal_ideal_subgroup: Subgroup add zero minus (principal_ideal x) := {
  subgroup_op_closed := principal_ideal_add_closed;
  subgroup_inv_closed := principal_ideal_minus_closed;
  subgroup_ident := principal_ideal_zero;
}.

Lemma principal_ideal_mul_absorb_l (a: Carrier):
  principal_ideal x a ->
  forall (r: Carrier),
    principal_ideal x (r <*> a).
Proof.
  intros [s Hs] r.
  exists (r <*> s).
  setoid_rewrite Hs.
  symmetry.
  apply (semigroup_assoc equiv mul).
Qed.

#[global]
Instance principal_ideal_ideal: Ideal add zero minus mul (principal_ideal x) := {
  ideal_add_subgroup := principal_ideal_subgroup;
  ideal_mul_absorb_l := principal_ideal_mul_absorb_l;
}.
End PrincipalIdeal.

Section UnionOfIdealChains.
Context {Index: Type}.
Context (index_inhabited: Index).
Context (ord: relation Index).
Context {ord_preorder: PreOrder ord}.
Context {ord_partial_order: PartialOrder eq ord}.
Context (index_chain: forall (i0 i1: Index), ord i0 i1 \/ ord i1 i0).
Context (Family: Index -> Carrier -> Prop).
Context (ideal_family: forall (i: Index), Ideal add zero minus mul (Family i)).
Context (ideal_family_subset:
          forall (i0 i1: Index), ord i0 i1 ->
            forall (r: Carrier), Family i0 r -> Family i1 r).

Definition union_ideal_chain: Carrier -> Prop :=
  fun r => exists (i: Index), Family i r.

Lemma union_ideal_chain_add_closed (a b: Carrier):
  union_ideal_chain a ->
  union_ideal_chain b ->
  union_ideal_chain (a <+> b).
Proof.
  intros [ia Ha] [ib Hb].
  case (index_chain ia ib);
    intros Hord.
  { exists ib.
    apply (subgroup_op_closed add zero minus (Family ib));
      [| assumption].
    apply (ideal_family_subset _ _ Hord _ Ha). }
  { exists ia.
    apply (subgroup_op_closed add zero minus (Family ia));
      [assumption |].
    apply (ideal_family_subset _ _ Hord _ Hb). }
Qed.

Lemma union_ideal_chain_minus_closed (a: Carrier):
  union_ideal_chain a ->
  union_ideal_chain (minus a).
Proof.
  intros [ia Ha].
  exists ia.
  apply (subgroup_inv_closed add zero minus (Family ia)).
  assumption.
Qed.

Lemma union_ideal_chain_zero:
  union_ideal_chain zero.
Proof.
  exists index_inhabited.
  apply (subgroup_ident add zero minus (Family index_inhabited)).
Qed.

Lemma union_ideal_chain_mul_absorb_l (a: Carrier):
  union_ideal_chain a ->
  forall (r: Carrier),
    union_ideal_chain (r <*> a).
Proof.
  intros [ia Ha] r.
  exists ia.
  apply (ideal_mul_absorb_l add zero minus mul (Family ia)).
  assumption.
Qed.

#[global]
Instance union_ideal_chain_subgroup: Subgroup add zero minus union_ideal_chain := {
  subgroup_op_closed := union_ideal_chain_add_closed;
  subgroup_inv_closed := union_ideal_chain_minus_closed;
  subgroup_ident := union_ideal_chain_zero;
}.

#[global]
Instance union_ideal_chain_ideal: Ideal add zero minus mul union_ideal_chain := {
  ideal_add_subgroup := union_ideal_chain_subgroup;
  ideal_mul_absorb_l := union_ideal_chain_mul_absorb_l;
}.
End UnionOfIdealChains.
End CommRings.