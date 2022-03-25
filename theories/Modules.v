Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
From algebra Require Import AbelianGroups Groups CommRings.
Require Import Coq.Vectors.Vector.

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
Context (action: R -> M -> M).
Context {action_proper: Proper (Requiv ==> Mequiv ==> Mequiv) action}.

Infix "=R=" := Requiv (at level 60, no associativity).
Infix "[+]" := Radd (at level 50, left associativity).
Infix "[*]" := Rmul (at level 40, left associativity).
Infix "=M=" := Mequiv (at level 60, no associativity).
Infix "<+>" := Madd (at level 50, left associativity).
Infix "<.>" := action (at level 40, no associativity).

Class Module_ := {
  module_agroup :> AbelianGroup Mequiv Madd Mzero Mminus;
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

Definition linear_combin: forall {n: nat}, t R n -> t M n -> M :=
  fold_right2 (fun coeff vec accum => accum <+> coeff <.> vec) Mzero.

Section Submodules.
Context (P: M -> Prop).
Context {P_proper: Proper (Mequiv ==> iff) P}.

Class Submodule := {
  submodule_subgroup :> Subgroup Madd Mzero Mminus P;
  submodule_action: forall (a: M), P a -> forall (r: R), P (r <.> a);
}.

Context {submodule: Submodule}.

Let lcongru := left_congru Madd Mminus P.

Lemma quotient_action_proper:
  Proper (Requiv ==> lcongru ==> lcongru) action.
Proof.
  intros r0 r1 Hr a0 a1 Ha.
  assert (Mminus (r0 <.> a0) <+> (r1 <.> a1) =M= r1 <.> (Mminus a0 <+> a1)).
  { setoid_rewrite <- module_minus_r.
    setoid_rewrite Hr.
    symmetry.
    apply module_distrib_Madd. }
  { apply P_proper in H.
    apply H.
    apply submodule_action.
    assumption. }
Qed.

Lemma quotient_distrib_Madd (r: R)(a b: M):
  lcongru (r <.> (a <+> b)) (r <.> a <+> r <.> b).
Proof.
  assert (Mminus (r <.> (a <+> b)) <+> (r <.> a <+> r <.> b) =M= Mzero).
  { setoid_rewrite module_distrib_Madd.
    apply (group_inv_l Mequiv Madd Mzero Mminus). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident Madd Mzero Mminus P). }
Qed.

Lemma quotient_distrib_Radd (r s: R)(a: M):
  lcongru ((r [+] s) <.> a) (r <.> a <+> s <.> a).
Proof.
  assert (Mminus ((r [+] s) <.> a) <+> (r <.> a <+> s <.> a) =M= Mzero).
  { setoid_rewrite module_distrib_Radd.
    apply (group_inv_l Mequiv Madd Mzero Mminus). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident Madd Mzero Mminus P). }
Qed.

Lemma quotient_distrib_Rmul (r s: R)(a: M):
  lcongru ((r [*] s) <.> a) (r <.> (s <.> a)).
Proof.
  assert (Mminus ((r [*] s) <.> a) <+> (r <.> (s <.> a)) =M= Mzero).
  { setoid_rewrite module_distrib_Rmul.
    apply (group_inv_l Mequiv Madd Mzero Mminus). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident Madd Mzero Mminus P). }
Qed.

Lemma quotient_Rone (a: M):
  lcongru (Rone <.> a) a.
Proof.
  assert (Mminus (Rone <.> a) <+> a =M= Mzero).
  { setoid_rewrite module_Rone.
    apply (group_inv_l Mequiv Madd Mzero Mminus). }
  { apply P_proper in H.
    apply H.
    apply (subgroup_ident Madd Mzero Mminus P). }
Qed.
End Submodules.
End Modules.

Section QuotientModules.
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
Context (action: R -> M -> M).
Context {action_proper: Proper (Requiv ==> Mequiv ==> Mequiv) action}.

Infix "=R=" := Requiv (at level 60, no associativity).
Infix "[+]" := Radd (at level 50, left associativity).
Infix "[*]" := Rmul (at level 40, left associativity).
Infix "=M=" := Mequiv (at level 60, no associativity).
Infix "<+>" := Madd (at level 50, left associativity).
Infix "<.>" := action (at level 40, no associativity).

Context {module: Module_ Radd Rmul Rone Mequiv Madd Mzero Mminus action}.
Context (P: M -> Prop).
Context {P_proper: Proper (Mequiv ==> iff) P}.
Context {submodule: Submodule Madd Mzero Mminus action P}.

Let lcongru := left_congru Madd Mminus P.
#[global]
Instance quotient_module: Module_ Radd Rmul Rone lcongru Madd Mzero Mminus action := {
  module_agroup := (quotient_subagroup Mequiv Madd Mzero Mminus (module_agroup Radd Rmul Rone Mequiv Madd Mzero Mminus action) P);
  module_distrib_Madd := (quotient_distrib_Madd Radd Rmul Rone Mequiv Madd Mzero Mminus action P);
  module_distrib_Radd := (quotient_distrib_Radd Radd Rmul Rone Mequiv Madd Mzero Mminus action P);
  module_distrib_Rmul := (quotient_distrib_Rmul Radd Rmul Rone Mequiv Madd Mzero Mminus action P);
  module_Rone := (quotient_Rone Radd Rmul Rone Mequiv Madd Mzero Mminus action P); 
}.
End QuotientModules.