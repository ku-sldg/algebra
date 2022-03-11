Require Import Coq.Classes.RelationClasses.
Require Import Semigroups.

Module Type MonoidSig.
  Include SemigroupSig.

  Parameter (e: Carrier).

  Axiom ident_l:
    forall (a: Carrier), e <*> a ~ a.
  Axiom ident_r:
    forall (a: Carrier), a <*> e ~ a.
End MonoidSig.

Module MonoidTheory (Import MS: MonoidSig).
  Include SemigroupTheory MS.

  Theorem ident_l_unique (e': Carrier):
    (forall (a: Carrier), e' <*> a ~ a) ->
    e' ~ e.
  Proof.
    intros Hl.
    specialize (Hl e).
    transitivity (e' <*> e);
      try assumption.
    symmetry.
    apply ident_r.
  Qed.

  Theorem ident_r_unique (e': Carrier):
    (forall (a: Carrier), a <*> e' ~ a) ->
    e' ~ e.
  Proof.
    intros Hr.
    specialize (Hr e).
    transitivity (e <*> e');
      try assumption.
    symmetry.
    apply ident_l.
  Qed.

  Theorem op_l_solo (a b: Carrier):
    a ~ e -> b <*> a ~ b.
  Proof.
    intros H.
    transitivity (b <*> e);
      try apply ident_r.
    apply op_l.
    assumption.
  Qed.

  Theorem op_r_solo (a b: Carrier):
    a ~ e -> a <*> b ~ b.
  Proof.
    intros H.
    transitivity (e <*> b);
      try apply ident_l.
    apply op_r.
    assumption.
  Qed.
End MonoidTheory.
