Require Import Algebra.Semigroup.
Require Import Algebra.Monoid.
Section GroupTheory.
Context {G: Set}(mult: G -> G -> G)(ident: G)(inv: G -> G).

Class Group := {
  group_assoc: forall (a b c: G), mult (mult a b) c = mult a (mult b c);
  group_ident_left: forall (a: G), mult ident a = a;
  group_ident_right: forall (a: G), mult a ident = a;
  group_inv_left: forall (a: G), mult (inv a) a = ident;
  group_inv_right: forall (a: G), mult a (inv a) = ident;
}.

Theorem group_monoid:
  Group -> Monoid mult ident.
Proof.
  intros Ggroup.
  constructor.
  { apply group_assoc. }
  { apply group_ident_left. }
  { apply group_ident_right. }
Qed.

Theorem group_semigroup:
  Group -> Semigroup mult.
Proof.
  intros Ggroup.
  constructor.
  apply group_assoc.
Qed.

Context `{Ggroup: Group}.

Lemma group_left_mult (a b: G):
  a = b -> forall (c: G), mult c a = mult c b.
Proof.
  intros <-;
    reflexivity.
Qed.

Lemma group_right_mult (a b: G):
  a = b -> forall (c: G), mult a c = mult b c.
Proof.
  intros <-;
    reflexivity.
Qed.

Theorem group_ident_unique (ident': G):
  (forall (a: G), mult ident' a = a) ->
  (forall (a: G), mult a ident' = a) ->
  ident' = ident.
Proof.
  intros Hlident' Hrident'.
  rewrite <- (Hrident' ident).
  rewrite <- (group_ident_left ident').
  rewrite (group_ident_left (mult ident ident')).
  reflexivity.
Qed.

Theorem group_idemp_ident (a: G):
  mult a a = a ->
  a = ident.
Proof.
  intros Hidemp.
  apply group_right_mult with (c := inv a) in Hidemp.
  rewrite group_assoc in Hidemp.
  rewrite group_inv_right in Hidemp.
  rewrite group_ident_right in Hidemp.
  assumption.
Qed.

Theorem group_left_cancel (a b c: G):
  mult c a = mult c b -> a = b.
Proof.
  intros Hcacb.
  apply group_left_mult with (c := inv c) in Hcacb.
  rewrite <- 2 group_assoc in Hcacb.
  rewrite group_inv_left in Hcacb.
  rewrite 2 group_ident_left in Hcacb.
  assumption.
Qed.

Theorem group_right_cancel (a b c: G):
  mult a c = mult b c -> a = b.
Proof.
  intros Hacbc.
  apply group_right_mult with (c := inv c) in Hacbc.
  rewrite 2 group_assoc in Hacbc.
  rewrite group_inv_right in Hacbc.
  rewrite 2 group_ident_right in Hacbc.
  assumption.
Qed.

Theorem group_inv_unique (a aInv: G):
  mult aInv a = ident ->
  mult a aInv = ident ->
  aInv = inv a.
Proof.
  intros Hlinv Hrinv.
  rewrite <- (group_inv_right a) in Hrinv.
  apply group_left_cancel in Hrinv.
  assumption.
Qed.

Theorem group_inv_involute (a: G):
  inv (inv a) = a.
Proof.
  symmetry.
  apply group_inv_unique.
  { apply group_inv_right. }
  { apply group_inv_left. }
Qed.

Theorem group_inv_mult (a b: G):
  inv (mult a b) = mult (inv b) (inv a).
Proof.
  symmetry.
  apply group_inv_unique;
    rewrite group_assoc.
  { remember (mult (inv a) (mult a b)) as b'.
    rewrite <- group_assoc in Heqb'.
    rewrite group_inv_left in Heqb'.
    rewrite group_ident_left in Heqb'.
    subst b'.
    apply group_inv_left. }
  { remember (mult b (mult (inv b) (inv a))) as inva.
    rewrite <- group_assoc in Heqinva.
    rewrite group_inv_right in Heqinva.
    rewrite group_ident_left in Heqinva.
    subst inva.
    apply group_inv_right. }
Qed.

Theorem group_left_mult_soln (a b: G):
  exists! (x: G), mult a x = b.
Proof.
  exists (mult (inv a) b).
  split.
  { rewrite <- group_assoc.
    rewrite group_inv_right.
    rewrite group_ident_left.
    reflexivity. }
  { intros x Haxb.
    apply group_left_mult with (c := inv a) in Haxb.
    rewrite <- group_assoc in Haxb.
    rewrite group_inv_left in Haxb.
    rewrite group_ident_left in Haxb.
    symmetry.
    assumption. }
Qed.

Theorem group_right_mult_soln (a b: G):
  exists! (x: G), mult x a = b.
Proof.
  exists (mult b (inv a)).
  split.
  { rewrite group_assoc.
    rewrite group_inv_left.
    rewrite group_ident_right.
    reflexivity. }
  { intros x Hxab.
    apply group_right_mult with (c := inv a) in Hxab.
    rewrite group_assoc in Hxab.
    rewrite group_inv_right in Hxab.
    rewrite group_ident_right in Hxab.
    symmetry.
    assumption. }
Qed.

Theorem group_inv_ident:
  inv ident = ident.
Proof.
  symmetry.
  apply group_inv_unique;
    apply group_ident_right.
Qed.
End GroupTheory.

Section SemigroupTheory.
Context {G: Set}(mult: G -> G -> G).
Context `{Gsubgroup: Semigroup G mult}.
Context (ident: G)(inv: G -> G).

Theorem group_semigroup_left_ident_left_inv:
  (Monoid mult ident /\ Group mult ident inv) ->
  forall (a: G), mult ident a = a /\ mult (inv a) a = ident.
Proof.
  intros [Gmonoid Ggroup] a.
  split;
    [apply monoid_ident_left | apply group_inv_left];
    assumption.
Qed.

Theorem group_semigroup_right_ident_right_inv:
  (Monoid mult ident /\ Group mult ident inv) ->
  forall (a: G), mult a ident = a /\ mult a (inv a) = ident.
Proof.
  intros [Gmonoid Ggroup] a.
  split;
    [apply monoid_ident_right | apply group_inv_right];
    assumption.
Qed.

Lemma semigroup_left_ident_left_inv_idemp_ident:
  (forall (a: G), mult ident a = a) ->
  (forall (a: G), mult (inv a) a = ident) ->
  forall (a: G), mult a a = a -> a = ident.
Proof.
  intros Hlident Hlinv a Hidemp.
  apply semigroup_left_mult with (c := inv a)(mult0 := mult) in Hidemp.
  rewrite <- semigroup_assoc in Hidemp;
    try assumption.
  rewrite Hlinv in Hidemp.
  rewrite Hlident in Hidemp.
  assumption.
Qed.

Lemma semigroup_right_ident_right_inv_idemp_ident:
  (forall (a: G), mult a ident = a) ->
  (forall (a: G), mult a (inv a) = ident) ->
  forall (a: G), mult a a = a -> a = ident.
Proof.
  intros Hrident Hrinv a Hidemp.
  apply semigroup_right_mult with (c := inv a)(mult0 := mult) in Hidemp.
  rewrite semigroup_assoc in Hidemp;
    try assumption.
  rewrite Hrinv in Hidemp.
  rewrite Hrident in Hidemp.
  assumption.
Qed.

Theorem semigroup_left_ident_left_inv_group:
  (forall (a: G), mult ident a = a) ->
  (forall (a: G), mult (inv a) a = ident) ->
  Monoid mult ident /\ Group mult ident inv.
Proof.
  intros Hlident Hlinv.
  cut (forall (a: G), mult a (inv a) = ident).
  { intros Hrinv.
    split;
      constructor;
      try apply semigroup_assoc;
      try assumption;
    intros a;
    rewrite <- (Hlinv a);
    rewrite <- semigroup_assoc;
      try assumption;
    rewrite Hrinv;
    apply Hlident. }
  { intros a.
    apply semigroup_left_ident_left_inv_idemp_ident;
      try assumption.
    rewrite semigroup_assoc;
      try assumption.
    remember (mult (inv a) (mult a (inv a))) as inva.
    rewrite <- semigroup_assoc in Heqinva;
      try assumption.
    rewrite Hlinv in Heqinva.
    rewrite Hlident in Heqinva.
    subst inva.
    reflexivity. }
Qed.

Theorem semigroup_right_ident_right_inv_group:
  (forall (a: G), mult a ident = a) ->
  (forall (a: G), mult a (inv a) = ident) ->
  Monoid mult ident /\ Group mult ident inv.
Proof.
  intros Hrident Hrinv.
  cut (forall (a: G), mult (inv a) a = ident).
  { intros Hlinv.
    split;
      constructor;
      try apply semigroup_assoc;
      try assumption;
    intros a;
    rewrite <- (Hrinv a);
    rewrite semigroup_assoc;
      try assumption;
    rewrite Hlinv;
    rewrite Hrident;
    reflexivity. }
  { intros a.
    apply semigroup_right_ident_right_inv_idemp_ident;
      try assumption.
    rewrite <- semigroup_assoc;
      try assumption.
    remember (mult (mult (inv a) a) (inv a)) as inva.
    rewrite semigroup_assoc in Heqinva;
      try assumption.
    rewrite Hrinv in Heqinva.
    rewrite Hrident in Heqinva.
    subst inva.
    reflexivity. }
Qed.
End SemigroupTheory.

Section SubgroupTheory.
Context {G: Set}(mult: G -> G -> G)(ident: G)(inv: G -> G).
Context `{Gsubgroup: Semigroup G mult}.
Context `{Gmonoid: Monoid G mult ident}.
Context `{Ggroup: Group G mult ident inv}.
Context (P: G -> Prop).

Class Subgroup := {
  subgroup_mult_closed: forall (a b: G), P a -> P b -> P (mult a b);
  subgroup_ident: P ident;
  subgroup_inv_closed: forall (a: G), P a -> P (inv a);
}.

Theorem subgroup_mult_inv_closed:
  Subgroup ->
  forall (a b: G), P a -> P b -> P (mult a (inv b)).
Proof.
  intros Psubgroup a b Pa Pb.
  apply subgroup_mult_closed;
    try assumption.
  apply subgroup_inv_closed;
    assumption.
Qed.

Lemma subset_mult_inv_closed_ident:
  {a: G | P a} ->
  (forall (a b: G), P a -> P b -> P (mult a (inv b))) ->
  P ident.
Proof.
  intros [a Ha] Hmultinv.
  rewrite <- (group_inv_right mult ident inv a).
  apply Hmultinv;
    assumption.
Qed.

Theorem subset_mult_inv_closed_subgroup:
  {a: G | P a} ->
  (forall (a b: G), P a -> P b -> P (mult a (inv b))) ->
  Subgroup.
Proof.
  intros [g Pg] Hmultinv.
  constructor.
  { intros a b Pa Pb.
    rewrite <- (group_inv_involute mult ident inv b).
    apply Hmultinv;
      try assumption.
    rewrite <- (monoid_ident_left mult ident).
    apply Hmultinv;
      try assumption.
    apply subset_mult_inv_closed_ident;
      try exists g;
      try assumption. }
  { apply subset_mult_inv_closed_ident;
      try exists g;
      try assumption. }
  { intros a Pa.
    rewrite <- (monoid_ident_left mult ident).
    apply Hmultinv;
      try assumption.
    apply subset_mult_inv_closed_ident;
      try exists g;
      try assumption. }
Qed.
End SubgroupTheory.
