Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses.

Section ZornsLemma.
Context (Index Carrier: Type).
Context (Family: Index -> Carrier -> Prop).
(*
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
*)

Definition index_subset: relation Index :=
  fun i0 i1 =>
    forall (x: Carrier),
      Family i0 x -> Family i1 x.

#[global]
Instance index_subset_refl: Reflexive index_subset.
Proof.
  intros i x H.
  assumption.
Qed.

#[global]
Instance index_subset_trans: Transitive index_subset.
Proof.
  intros i0 i1 i2 H01 H12 x H0.
  apply H12.
  apply H01.
  assumption.
Qed.
End ZornsLemma.