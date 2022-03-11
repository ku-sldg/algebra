Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From algebra Require Import Groups.
From algebra Require Import AbelianGroups CommRings.

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

Infix "&" := Requiv (at level 60, no associativity).
Infix "[+]" := Radd (at level 50, left associativity).
Infix "[*]" := Rmul (at level 40, left associativity).
Infix "~" := Mequiv (at level 60, no associativity).
Infix "<+>" := Madd (at level 50, left associativity).
Infix "<.>" := action (at level 40, no associativity).

Class Module_ := {
  module_distrib_Madd:
    forall (r: R)(a b: M),
      r <.> (a <+> b) ~ r <.> a <+> r <.> b;
  module_distrib_Radd:
    forall (r s: R)(a: M),
      (r [+] s) <.> a ~ r <.> a <+> s <.> a;
  module_distrib_Rmul:
    forall (r s: R)(a: M),
      (r [*] s) <.> a ~ r <.> (s <.> a);
  module_Rone:
    forall (a: M), Rone <.> a ~ a;
}.

Context `{module: Module_}.

Lemma module_op_l (a b: M):
  a ~ b -> forall (r: R), r <.> a ~ r <.> b.
Proof.
  intros Hab r.
  apply action_proper;
    try assumption;
    try reflexivity.
Qed.

Lemma module_op_r (r s: R):
  r & s -> forall (a: M), r <.> a ~ s <.> a.
Proof.
  intros Hrs a.
  apply action_proper;
    try assumption;
    try reflexivity.
Qed.

Theorem module_0_l (a: M):
  Rzero <.> a ~ Mzero.
Proof.
  apply (group_idemp_ident Mequiv Madd Mzero Mminus).
  transitivity ((Rzero [+] Rzero) <.> a);
    [symmetry; apply module_distrib_Radd |].
  apply module_op_r.
  apply (group_ident_r Requiv Radd Rzero Rminus).
Qed.

Theorem module_0_r (r: R):
  r <.> Mzero ~ Mzero.
Proof.
  apply (group_idemp_ident Mequiv Madd Mzero Mminus).
  transitivity (r <.> (Mzero <+> Mzero));
    [symmetry; apply module_distrib_Madd |].
  apply module_op_l.
  apply (group_ident_r Mequiv Madd Mzero Mminus).
Qed.

Theorem module_minus_l (r: R)(a: M):
  (Rminus r) <.> a ~ Mminus (r <.> a).
Proof.
  apply (group_inv_r_unique Mequiv Madd Mzero Mminus).
  transitivity ((r [+] Rminus r) <.> a);
    [symmetry; apply module_distrib_Radd |].
  transitivity (Rzero <.> a);
    [| apply module_0_l].
  apply module_op_r.
  apply (group_inv_r Requiv Radd Rzero Rminus).
Qed.

Theorem module_minus_r (r: R)(a: M):
  r <.> Mminus a ~ Mminus (r <.> a).
Proof.
  apply (group_inv_r_unique Mequiv Madd Mzero Mminus).
  transitivity (r <.> (a <+> Mminus a));
    [symmetry; apply module_distrib_Madd |].
  transitivity (r <.> Mzero);
    [| apply module_0_r].
  apply module_op_l.
  apply (group_inv_r Mequiv Madd Mzero Mminus).
Qed.

Theorem module_minus_minus (r: R)(a: M):
  Rminus r <.> Mminus a ~ r <.> a.
Proof.
  transitivity (Mminus (r <.> Mminus a));
    [apply module_minus_l |].
  transitivity (Mminus (Mminus (r <.> a)));
    [| apply (group_inv_involute Mequiv Madd Mzero Mminus)].
  apply Mminus_proper.
  apply module_minus_r.
Qed.
End Modules.
