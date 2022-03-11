Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Module Type SemigroupSig.
  Parameters (Carrier: Type)(Req: relation Carrier).
  Context `{Requiv: Equivalence Carrier Req}.
  Parameters (op: Carrier -> Carrier -> Carrier).
  Parameters (op_proper: Proper (Req ==> Req ==> Req) op).

  Infix "~" := Req (at level 60, no associativity).
  Infix "<*>" := op (at level 40, left associativity).

  Axiom associativity:
    forall (a b c: Carrier),
      a <*> b <*> c ~ a <*> (b <*> c).
End SemigroupSig.

Module SemigroupTheory (Import SS: SemigroupSig).
  Context `{Requiv: Equivalence Carrier Req}.
  Theorem op_l:
    forall (a b: Carrier),
      a ~ b ->
      forall (c: Carrier), c <*> a ~ c <*> b.
  Proof.
    intros a b Hab c.
    apply op_proper;
      [reflexivity | assumption].
  Qed.

  Theorem op_r:
    forall (a b: Carrier),
      a ~ b ->
      forall (c: Carrier), a <*> c ~ b <*> c.
  Proof.
    intros a b Hab c.
    apply op_proper;
      [assumption | reflexivity].
  Qed.
End SemigroupTheory.
