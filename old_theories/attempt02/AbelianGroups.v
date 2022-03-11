Require Import Coq.Classes.Morphisms.
Require Import Semigroups Monoids Groups.

Module Type AbelianGroupSig.
  Include GroupSig.
  Axiom commutivity:
    forall (a b: Carrier), a <*> b ~ b <*> a.
End AbelianGroupSig.

Module AbelianGroupTheory (Import AGS: AbelianGroupSig).
  Include GroupTheory AGS.

  Section Subgroups.
  Variable (P: Carrier -> Prop).
  Variable (P_proper: Proper (Req ==> iff) P).
  Hypothesis subgroup_op_closed:
    forall (a b: Carrier), P a -> P b -> P (a <*> b).
  Hypothesis subgroup_inv_closed:
    forall (a: Carrier), P a -> P (inv a).
  Hypothesis subgroup_ident: P e.

  Theorem normal_subgroup_cosets_coincide:
    forall (m: Carrier), (* 3 *)
      P m ->
      (forall (a: Carrier),
        exists (n: Carrier),
          P n /\ a <*> m ~ n <*> a).
  Proof.
    intros m HPm a.
    exists m.
    split;
      [assumption | apply commutivity].
  Qed.

  Corollary normal_subgroup_congru_coincide:
    forall (a b: Carrier),
      left_congru P a b <-> right_congru P a b.
  Proof.
    apply normal_subgroup_equiv_congru_cosets;
      try assumption.
    apply normal_subgroup_cosets_coincide.
  Qed.

  Corollary normal_subgroup_coset_eq_coincide:
    forall (a b: Carrier),
      left_cosets_eq P a b <-> right_cosets_eq P a b.
  Proof.
    apply normal_subgroup_equiv_coset_eq_cosets;
      try assumption.
    apply normal_subgroup_cosets_coincide.
  Qed.

  Corollary normal_subgroup_conj_closed:
    forall (n: Carrier),
      P n ->
      forall (a: Carrier), P (a <*> n <*> inv a).
  Proof.
    apply normal_subgroup_equiv_cosets_conj;
      try assumption.
    apply normal_subgroup_cosets_coincide.
  Qed.

  Corollary normal_subgroup_conj_closed_exact:
    forall (n: Carrier),
      P n <->
      forall (a: Carrier), P (a <*> n <*> inv a).
  Proof.
    apply normal_subgroup_equiv_cosets_conj_exact;
      try assumption.
    apply normal_subgroup_cosets_coincide.
  Qed.
  End Subgroups.
End AbelianGroupTheory.
