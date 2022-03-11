Require Import Coq.Classes.Morphisms.
Require Import Groups.

Module Type GroupHomSig.
  Declare Module DomainSig: GroupSig.
  Declare Module CodomainSig: GroupSig.
  Module Domain := GroupTheory DomainSig.
  Module Codomain := GroupTheory CodomainSig.
  Definition A := DomainSig.Carrier.
  Definition B := CodomainSig.Carrier.
  Infix "<*>" := DomainSig.op (at level 40, left associativity).
  Infix "<o>" := CodomainSig.op (at level 40, left associativity).
  Infix "~" := DomainSig.Req (at level 60, no associativity).
  Infix "&" := CodomainSig.Req (at level 60, no associativity).
  Parameter (f: A -> B).
  Parameter (f_proper: Proper (DomainSig.Req ==> CodomainSig.Req) f).
  Axiom hom_preserves_op: forall (a b: A), (f (a <*> b)) & (f a <o> f b).
End GroupHomSig.

Module GroupHomTheory (Import GHS: GroupHomSig).
  Definition Ainv := DomainSig.inv.
  Definition Binv := CodomainSig.inv.
  Definition Ae := DomainSig.e.
  Definition Be := CodomainSig.e.
  Theorem hom_preserves_ident: (f Ae) & Be.
  Proof.
    apply Codomain.op_idemp_ident.
    transitivity (f (Ae <*> Ae));
      try (symmetry; apply hom_preserves_op).
    apply f_proper.
    apply DomainSig.ident_r.
  Qed.

  Theorem hom_preserves_inv (a: A): (f (Ainv a)) & (Binv (f a)).
  Proof.
    apply Codomain.inv_r_unique.
    transitivity (f (a <*> Ainv a));
      try (symmetry; apply hom_preserves_op).
    transitivity (f Ae);
      try apply hom_preserves_ident.
    apply f_proper.
    apply DomainSig.inv_r.
  Qed.
End GroupHomTheory.
