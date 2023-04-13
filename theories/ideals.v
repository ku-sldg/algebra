From mathcomp Require Import ssralg eqtype.
From Coq.ssr Require Import ssrbool.
From Coq.Bool Require Import Bool.
From mathcomp.algebra Require Import ring_quotient.

Definition maximal_ideal (R: ringType)(P: {pred R})(_: proper_ideal P): Prop :=
    forall (P': {pred R})(_: proper_ideal P'),
        (forall (x: R), (P x) -> (P' x)) ->
        (forall (x: R), (P' x) -> (P x)).

Definition local_ring (R: ringType): Prop :=
    exists (P: {pred R}),
        (forall (Pideal: proper_ideal P),
            maximal_ideal R P Pideal) /\
        (forall (P': {pred R})(Pideal': proper_ideal P'),
            maximal_ideal R P' Pideal' ->
                forall (r: R), P r <-> P' r).

Lemma in_ideal_not_unit (R: unitRingType)(P: {pred R})(Pideal: proper_ideal P):
    forall (x: R), P x -> (x \isn't a GRing.unit).
Proof.
    intros x HPx.
    apply contraT.
    intros HxUnit.
    rewrite unfold_in in HxUnit.
    apply negbNE in HxUnit.
    rewrite <- (reflect_iff _ _ (GRing.unitrP x)) in HxUnit.
    inversion_clear HxUnit as [xinv [Hxinvx Hxxinv]].
    unfold proper_ideal in Pideal.
    inversion_clear Pideal as [HP1 HPabsorb].
    specialize (HPabsorb xinv x HPx).
    simpl in HPabsorb.
    rewrite Hxinvx in HPabsorb.
    rewrite HPabsorb in HP1.
    apply HP1.
Qed.

Axiom comm_ring_maximal_ideal_nonunits:
    forall (R: unitRingType)(x: R),
        x \isn't a GRing.unit ->
        exists (P: {pred R})(Pideal: proper_ideal P),
            x \in P /\ maximal_ideal R P Pideal.
