Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From algebra Require Import Groups.

Section GroupHoms.
Context {Domain Range: Type}.
Context (Dequiv: relation Domain).
Context {Dequiv_equiv: Equivalence Dequiv}.
Context (Dop: Domain -> Domain -> Domain).
Context {Dop_proper: Proper (Dequiv ==> Dequiv ==> Dequiv) Dop}.
Context (Dident: Domain).
Context (Dinv: Domain -> Domain).
Context {Dinv_proper: Proper (Dequiv ==> Dequiv) Dinv}.
Context {Dgroup: Group Dequiv Dop Dident Dinv}.
Context (Requiv: relation Range).
Context {Requiv_equiv: Equivalence Requiv}.
Context (Rop: Range -> Range -> Range).
Context {Rop_proper: Proper (Requiv ==> Requiv ==> Requiv) Rop}.
Context (Rident: Range).
Context (Rinv: Range -> Range).
Context {Rinv_proper: Proper (Requiv ==> Requiv) Rinv}.
Context {Rgroup: Group Requiv Rop Rident Rinv}.
Context (hom: Domain -> Range).
Context {hom_proper: Proper (Dequiv ==> Requiv) hom}.

Infix "~" := Dequiv (at level 60, no associativity).
Infix "<o>" := Dop (at level 40, left associativity).
Infix "&" := Requiv (at level 60, no associativity).
Infix ">o<" := Rop (at level 40, left associativity).

Class GroupHom := {
  group_hom_op:
    forall (a b: Domain),
      hom (a <o> b) & hom a >o< hom b;
}.

Context {grouphom: GroupHom}.

Theorem group_hom_ident:
  hom Dident & Rident.
Proof.
  apply (group_idemp_ident Requiv Rop Rident Rinv).
  transitivity (hom (Dident <o> Dident));
    [symmetry; apply group_hom_op |].
  apply hom_proper.
  apply (group_ident_r Dequiv Dop Dident Dinv).
Qed.

Theorem group_hom_inv (a: Domain):
  hom (Dinv a) & Rinv (hom a).
Proof.
  apply (group_inv_r_unique Requiv Rop Rident Rinv).
  transitivity (hom (a <o> Dinv a));
    [symmetry; apply group_hom_op |].
  transitivity (hom Dident);
    [apply hom_proper | apply group_hom_ident].
  apply (group_inv_r Dequiv Dop Dident Dinv).
Qed.

Definition kernelPred (a: Domain) := hom a & Rident.

Theorem group_hom_injective:
  (forall (a b: Domain), hom a & hom b -> a ~ b) <->
  (forall (a: Domain), kernelPred a -> a ~ Dident).
Proof.
  split;
    [intros Hinj | intros Hkern].
  { intros a Hk.
    assert (hom a & hom Dident).
    { transitivity (Rident);
        [assumption | symmetry; apply group_hom_ident]. }
    { apply Hinj in H.
      assumption. } }
  { intros a b Hab.
    assert (hom (a <o> Dinv b) & Rident).
    { transitivity (hom a >o< hom (Dinv b));
        [apply group_hom_op |].
      transitivity (hom a >o< Rinv (hom b));
        [apply (group_op_l Requiv Rop);
          apply group_hom_inv |].
      symmetry.
      apply (group_move_r Requiv Rop Rident Rinv).
      transitivity (hom b);
        [apply (group_ident_l Requiv Rop Rident Rinv) |].
      symmetry.
      assumption. }
    { apply Hkern in H.
      apply (group_cancel_r Dequiv Dop Dident Dinv) with (c := Dinv b).
      transitivity (Dident);
        [| symmetry; apply (group_inv_r Dequiv Dop Dident Dinv) ].
      assumption. } }
Qed.

Lemma group_hom_kern_proper:
  Proper (Dequiv ==> iff) kernelPred.
Proof.
  intros a0 a1 Ha.
  unfold kernelPred.
  split;
    [intros Hka0 | intros Hka1].
  { transitivity (hom a0);
      [apply hom_proper; symmetry |];
      assumption. }
  { transitivity (hom a1);
      [apply hom_proper |];
      assumption. }
Qed.

Lemma group_hom_kern_op_closed (a b: Domain):
  kernelPred a ->
  kernelPred b ->
  kernelPred (a <o> b).
Proof.
  unfold kernelPred.
  intros Hka Hkb.
  transitivity (hom a >o< hom b);
    [apply group_hom_op |].
  transitivity (hom a >o< Rident);
    [apply (group_op_l Requiv Rop); assumption |].
  transitivity (hom a);
    [apply (group_ident_r Requiv Rop Rident Rinv)
    | assumption].
Qed.

Lemma group_hom_kern_inv_closed (a: Domain):
  kernelPred a ->
  kernelPred (Dinv a).
Proof.
  unfold kernelPred.
  intros Hka.
  transitivity (Rinv (hom a));
    [apply group_hom_inv |].
  symmetry.
  apply (group_inv_r_unique Requiv Rop Rident Rinv).
  transitivity (hom a);
    [apply (group_ident_r Requiv Rop Rident Rinv)
    | assumption].
Qed.

#[global]
Instance group_hom_kern_subgroup: Subgroup Dop Dident Dinv kernelPred := {
  subgroup_op_closed := group_hom_kern_op_closed;
  subgroup_inv_closed := group_hom_kern_inv_closed;
  subgroup_ident := group_hom_ident;
}.

Theorem group_hom_kern_conj_closed (a: Domain):
  kernelPred a ->
  forall (g: Domain), kernelPred (g <o> a <o> Dinv g).
Proof.
  unfold kernelPred.
  intros Hka g.
  transitivity (hom (g <o> a) >o< hom (Dinv g));
    [apply group_hom_op |].
  transitivity (hom g >o< hom a >o< hom (Dinv g));
    [apply (group_op_r Requiv Rop);
      apply group_hom_op |].
  transitivity (hom g >o< hom a >o< Rinv (hom g));
    [apply (group_op_l Requiv Rop);
      apply group_hom_inv |].
  symmetry.
  apply (group_move_r Requiv Rop Rident Rinv).
  transitivity (hom g);
    [apply (group_ident_l Requiv Rop Rident Rinv) |].
  symmetry.
  transitivity (hom g >o< Rident);
    [apply (group_op_l Requiv Rop); assumption |].
  apply (group_ident_r Requiv Rop Rident Rinv).
Qed.

Corollary group_hom_kern_congru_coincide:
  forall (a b: Domain),
    left_congru Dop Dinv kernelPred a b <->
    right_congru Dop Dinv kernelPred a b.
Proof.
  apply (normal_subgroup_equiv_congru_conj Dequiv Dop Dident Dinv kernelPred).
  { apply group_hom_kern_proper. }
  { apply group_hom_kern_subgroup. }
  { apply group_hom_kern_conj_closed. }
Qed.

Corollary group_hom_kern_cosets_eq_coincide:
  forall (a b: Domain),
    left_cosets_eq Dequiv Dop kernelPred a b <->
    right_cosets_eq Dequiv Dop kernelPred a b.
Proof.
  apply (normal_subgroup_equiv_cosets_eq_conj Dequiv Dop Dident Dinv kernelPred).
  { apply group_hom_kern_proper. }
  { apply group_hom_kern_subgroup. }
  { apply group_hom_kern_conj_closed. }
Qed.

Corollary group_hom_kern_cosets_coincide:
  forall (m: Domain),
    kernelPred m ->
    forall (a: Domain),
      exists (n: Domain),
        kernelPred n /\
        a <o> m ~ n <o> a.
Proof.
  apply (normal_subgroup_equiv_cosets_conj Dequiv Dop Dident Dinv kernelPred).
  { apply group_hom_kern_proper. }
  { apply group_hom_kern_conj_closed. }
Qed.

Corollary group_hom_kern_conj_closed_exact:
  forall (n a: Domain),
    kernelPred n <->
    kernelPred (a <o> n <o> Dinv a).
Proof.
  apply (normal_subgroup_equiv_conj_closed Dequiv Dop Dident Dinv kernelPred).
  { apply group_hom_kern_proper. }
  { apply group_hom_kern_conj_closed. }
Qed.

Theorem group_hom_kern_congru_inj (a b: Domain):
  hom a & hom b -> left_congru Dop Dinv kernelPred a b.
Proof.
  intros Hhom.
  unfold left_congru, kernelPred.
  transitivity (hom (Dinv a) >o< hom b);
    [apply group_hom_op |].
  transitivity (Rinv (hom a) >o< hom b);
    [apply (group_op_r Requiv Rop);
      apply group_hom_inv |].
  symmetry.
  apply (group_move_l Requiv Rop Rident Rinv).
  transitivity (hom a);
    [apply (group_ident_r Requiv Rop Rident Rinv)
    | assumption].
Qed.
End GroupHoms.

Section QuotientProjections.
Context {Carrier : Type}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (op: Carrier -> Carrier -> Carrier).
Context {op_proper: Proper (equiv ==> equiv ==> equiv) op}.
Context (ident: Carrier).
Context (inv: Carrier -> Carrier).
Context {inv_proper: Proper (equiv ==> equiv) inv}.
Context {group: Group equiv op ident inv}.
Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.
Context {subgroup: Subgroup op ident inv P}.

Infix "<o>" := op (at level 40, left associativity).
Infix "~" := equiv (at level 60, no associativity).

Let lcongru := left_congru op inv P.
Let rcongru := right_congru op inv P.
Let congru_coincide :=
    forall (a b: Carrier),
      lcongru a b <-> rcongru a b.
Context (normal: congru_coincide).

Definition quotient_projection (a: Carrier): Carrier := a.
Let hom := quotient_projection.

Lemma quotient_projection_proper:
  Proper (equiv ==> lcongru) hom.
Proof.
  intros a0 a1 Ha.
  unfold quotient_projection.
  assert (lcongru a0 a0 <-> lcongru a0 a1).
  { apply (left_congru_proper equiv op inv P);
      try assumption;
      try reflexivity. }
  { apply H.
    reflexivity. }
Qed.

Lemma quotient_projection_op (a b: Carrier):
  lcongru (hom (a <o> b)) (hom a <o> hom b).
Proof.
  unfold hom.
  reflexivity.
Qed.

#[global]
Instance quotient_projection_hom: GroupHom op lcongru op hom := {
  group_hom_op := quotient_projection_op;
}.

Let kernel := kernelPred lcongru ident hom.

Theorem quotient_projection_kernel (a: Carrier):
  lcongru a ident <-> kernel a.
Proof.
  unfold kernel, kernelPred, hom.
  reflexivity.
Qed.
End QuotientProjections.
