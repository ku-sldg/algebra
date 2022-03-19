Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
From algebra Require Import AbelianGroups Groups CommRings.

Section Modules.
Context {R: Type}.
Context (Requiv: relation R).
Context {Requiv_equiv: Equivalence Requiv}.
Context (Radd: R -> R -> R).
Context {Radd_proper: Proper (Requiv ==> Requiv ==> Requiv) Radd}.
Context (Rzero: R).
Context (Rminus: R -> R).
Context {Rminus_proper: Proper (Requiv ==> Requiv) Rminus}.
Context (Rmul: R -> R -> R).
Context {Rmul_proper: Proper (Requiv ==> Requiv ==> Requiv) Rmul}.
Context (Rone: R).
Context {R_cring: CommRing Requiv Radd Rzero Rminus Rmul Rone}.
Context {M: Type}.
Context (Mequiv: relation M).
Context {Mequiv_equiv: Equivalence Mequiv}.
Context (Madd: M -> M -> M).
Context {Madd_proper: Proper (Mequiv ==> Mequiv ==> Mequiv) Madd}.
Context (Mzero: M).
Context (Mminus: M -> M).
Context {Mminus_proper: Proper (Mequiv ==> Mequiv) Mminus}.
Context {Magroup: AbelianGroup Mequiv Madd Mzero Mminus}.
Context (action: R -> M -> M).
Context {action_proper: Proper (Requiv ==> Mequiv ==> Mequiv) action}.

Infix "=R=" := Requiv (at level 60, no associativity).
Infix "[+]" := Radd (at level 50, left associativity).
Infix "[*]" := Rmul (at level 40, left associativity).
Infix "=M=" := Mequiv (at level 60, no associativity).
Infix "<+>" := Madd (at level 50, left associativity).
Infix "<.>" := action (at level 40, no associativity).

Class Module_ := {
  module_distrib_Madd:
    forall (r: R)(a b: M),
      r <.> (a <+> b) =M= r <.> a <+> r <.> b;
  module_distrib_Radd:
    forall (r s: R)(a: M),
      (r [+] s) <.> a =M= r <.> a <+> s <.> a;
  module_distrib_Rmul:
    forall (r s: R)(a: M),
      (r [*] s) <.> a =M= r <.> (s <.> a);
  module_Rone:
    forall (a: M), Rone <.> a =M= a;
}.

Context `{module: Module_}.

Lemma module_op_l (a b: M):
  a =M= b -> forall (r: R), r <.> a =M= r <.> b.
Proof.
  intros Hab r.
  apply action_proper;
    try assumption;
    try reflexivity.
Qed.

Lemma module_op_r (r s: R):
  r =R= s -> forall (a: M), r <.> a =M= s <.> a.
Proof.
  intros Hrs a.
  apply action_proper;
    try assumption;
    try reflexivity.
Qed.

Theorem module_0_l (a: M):
  Rzero <.> a =M= Mzero.
Proof.
  apply (group_idemp_ident Mequiv Madd Mzero Mminus).
  setoid_rewrite <- module_distrib_Radd.
  apply module_op_r.
  apply (group_ident_r Requiv Radd Rzero Rminus).
Qed.

Theorem module_0_r (r: R):
  r <.> Mzero =M= Mzero.
Proof.
  apply (group_idemp_ident Mequiv Madd Mzero Mminus).
  setoid_rewrite <- module_distrib_Madd.
  apply module_op_l.
  apply (group_ident_r Mequiv Madd Mzero Mminus).
Qed.

Theorem module_minus_l (r: R)(a: M):
  (Rminus r) <.> a =M= Mminus (r <.> a).
Proof.
  apply (group_inv_r_unique Mequiv Madd Mzero Mminus).
  setoid_rewrite <- module_distrib_Radd.
  setoid_rewrite (group_inv_r Requiv Radd Rzero Rminus).
  apply module_0_l.
Qed.

Theorem module_minus_r (r: R)(a: M):
  r <.> Mminus a =M= Mminus (r <.> a).
Proof.
  apply (group_inv_r_unique Mequiv Madd Mzero Mminus).
  setoid_rewrite <- (module_distrib_Madd).
  setoid_rewrite (group_inv_r Mequiv Madd Mzero Mminus).
  apply module_0_r.
Qed.

Theorem module_minus_minus (r: R)(a: M):
  Rminus r <.> Mminus a =M= r <.> a.
Proof.
  setoid_rewrite module_minus_l.
  setoid_rewrite module_minus_r.
  apply (group_inv_involute Mequiv Madd Mzero Mminus).
Qed.
End Modules.
