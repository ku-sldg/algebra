Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From algebra Require Import Semigroups Monoids Groups.

Section AbelianGroups.
Context {Carrier: Type}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (op: Carrier -> Carrier -> Carrier).
Context {op_proper: Proper (equiv ==> equiv ==> equiv) op}.
Context (ident: Carrier).
Context (inv: Carrier -> Carrier).
Context {inv_proper: Proper (equiv ==> equiv) inv}.

Infix "==" := equiv (at level 60, no associativity).
Infix "<o>" := op (at level 40, left associativity).

Class AbelianGroup := {
  abelian_group :> Group equiv op ident inv;
  abelian_comm :> Commutative equiv op;
}.

Context {abelian: AbelianGroup}.

Section Subgroups.
Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.
Context {subgroup: Subgroup op ident inv P}.

Theorem subagroup_cosets_coincide:
  forall (m: Carrier),
    P m ->
    (forall (a: Carrier),
      exists (n: Carrier),
        P n /\ a <o> m == n <o> a).
Proof.
  intros m HPm a.
  exists m.
  split;
    [assumption | apply abelian_comm].
Qed.

Corollary subagroup_congru_coincide:
  forall (a b: Carrier),
   left_congru op inv P a b <->
   right_congru op inv P a b.
Proof.
  apply (normal_subgroup_equiv_congru_cosets equiv op ident inv);
    try assumption.
  apply subagroup_cosets_coincide.
Qed.

Corollary subagroup_coset_eq_coincide:
  forall (a b: Carrier),
    left_cosets_eq equiv op P a b <->
    right_cosets_eq equiv op P a b.
Proof.
  apply (normal_subgroup_equiv_cosets_eq_cosets equiv op ident inv);
    try assumption.
  apply subagroup_cosets_coincide.
Qed.

Corollary subagroup_conj_closed:
  forall (n: Carrier),
    P n ->
    forall (a: Carrier), P (a <o> n <o> inv a).
Proof.
  apply (normal_subgroup_equiv_cosets_conj equiv op ident inv);
    try assumption.
  apply subagroup_cosets_coincide.
Qed.

Corollary subagroup_conj_closed_exact:
  forall (n a: Carrier),
    P n <-> P (a <o> n <o> inv a).
Proof.
  apply (normal_subgroup_equiv_cosets_conj_exact equiv op ident inv).
    try assumption.
  apply subagroup_cosets_coincide.
Qed.

#[global]
Instance quotient_subagroup_group: Group (left_congru op inv P) op ident inv.
Proof.
  apply (quotient_normal_subgroup_group equiv op ident inv P).
  apply subagroup_congru_coincide.
Qed.
End Subgroups.
End AbelianGroups.

Section AbelianSubgroups.
Context {Carrier: Type}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (op: Carrier -> Carrier -> Carrier).
Context {op_proper: Proper (equiv ==> equiv ==> equiv) op}.
Context (ident: Carrier).
Context (inv: Carrier -> Carrier).
Context {inv_proper: Proper (equiv ==> equiv) inv}.
Context (abelian: AbelianGroup equiv op ident inv).
Infix "==" := equiv (at level 60, no associativity).
Infix "<o>" := op (at level 40, left associativity).
Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.
Context {subgroup: Subgroup op ident inv P}.

#[global]
Instance quotient_subagroup: AbelianGroup (left_congru op inv P) op ident inv.
Proof.
  constructor.
  { apply (quotient_subagroup_group equiv op ident inv P). }
  { constructor.
    intros a b.
    assert (inv (a <o> b) <o> (b <o> a) == ident).
    { transitivity (inv (a <o> b) <o> (a <o> b));
        [apply (semigroup_op_l equiv op);
          apply (abelian_comm equiv op ident inv) |].
      apply (group_inv_l equiv op ident inv). }
    { apply P_proper in H.
      apply H.
      apply (subgroup_ident op ident inv P). } }
Qed.
End AbelianSubgroups.
