Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From algebra Require Import Semigroups.

Section Monoids.
Context {Carrier: Type}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (op: Carrier -> Carrier -> Carrier).
Context {op_proper: Proper (equiv ==> equiv ==> equiv) op}.
Context (ident: Carrier).

Infix "~" := equiv (at level 60, no associativity).
Infix "<o>" := op (at level 40, no associativity).

Class Monoid := {
  monoid_semigroup :> Semigroup equiv op;
  monoid_ident_l:
    forall (a: Carrier), ident <o> a ~ a;
  monoid_ident_r:
    forall (a: Carrier), a <o> ident ~ a;
}.

Context {monoid: Monoid}.

Theorem group_ident_l_unique (e: Carrier):
  (forall (a: Carrier), e <o> a ~ a) ->
  e ~ ident.
Proof.
  intros Hl.
  specialize (Hl ident).
  transitivity (e <o> ident);
    [| assumption].
  symmetry.
  apply monoid_ident_r.
Qed.

Theorem group_ident_r_unique (e: Carrier):
  (forall (a: Carrier), a <o> e ~ a) ->
  e ~ ident.
Proof.
  intros Hr.
  specialize (Hr ident).
  transitivity (ident <o> e);
    [| assumption].
  symmetry.
  apply monoid_ident_l.
Qed.

Definition monoid_op_l := semigroup_op_l equiv op.
Lemma monoid_op_l_solo (a b: Carrier):
  a ~ ident -> b <o> a ~ b.
Proof.
  intros H.
  transitivity (b <o> ident);
    [| apply monoid_ident_r].
  apply monoid_op_l.
  assumption.
Qed.

Definition monoid_op_r := semigroup_op_r equiv op.
Lemma monoid_op_r_solo (a b: Carrier):
  a ~ ident -> a <o> b ~ b.
Proof.
  intros H.
  transitivity (ident <o> b);
    [| apply monoid_ident_l].
  apply monoid_op_r.
  assumption.
Qed.
End Monoids.
