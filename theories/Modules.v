Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
From algebra Require Import Semigroups Monoids Groups AbelianGroups CommRings Vectors.
Require Import Coq.Vectors.Vector.
Require Import Coq.Program.Equality.

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

Lemma module_linear_combin_append:
  forall (m n: nat)(rs0: t R m)(rs1: t R n)(vs0: t M m)(vs1: t M n),
    linear_combin (append rs0 rs1) (append vs0 vs1) =M=
      linear_combin rs0 vs0 <+> linear_combin rs1 vs1.
Proof.
  intros m n rs0 rs1 vs0 vs1.
  generalize dependent vs0.
  generalize dependent rs0.
  generalize dependent m.
  apply vector_ind2;
    simpl.
  { symmetry.
    apply (monoid_ident_l Mequiv Madd Mzero). }
  { intros m rs0 vs0 IH a b.
    setoid_rewrite IH.
    setoid_rewrite (semigroup_assoc Mequiv Madd).
    apply (semigroup_op_l Mequiv Madd).
    apply (commutative Mequiv Madd). }
Qed.

Lemma module_linear_combin_0_l {n: nat}(v: t M n):
  linear_combin (const_seq Rzero n) v =M= Mzero.
Proof.
  induction v;
    simpl;
    [reflexivity |].
  setoid_rewrite IHv.
  setoid_rewrite (monoid_ident_l Mequiv Madd Mzero).
  apply module_0_l.
Qed.

Lemma module_linear_combin_zipWith_add_l {n: nat}(coeffs0 coeffs1: t R n)(vectors: t M n):
  linear_combin (zipWith Radd coeffs0 coeffs1) vectors =M=
    linear_combin coeffs0 vectors <+> linear_combin coeffs1 vectors.
Proof.
  induction vectors as [| vector n vectors].
  { dependent destruction coeffs0.
    dependent destruction coeffs1.
    simpl.
    symmetry.
    apply (monoid_ident_r Mequiv Madd Mzero). }
  { dependent destruction coeffs0.
    rename h into coeff0.
    dependent destruction coeffs1.
    rename h into coeff1.
    simpl.
    setoid_rewrite IHvectors.
    setoid_rewrite (module_distrib_Radd).
    setoid_rewrite (semigroup_assoc Mequiv Madd).
    apply (semigroup_op_l Mequiv Madd).
    setoid_rewrite <- (semigroup_assoc Mequiv Madd).
    apply (semigroup_op_r Mequiv Madd).
    apply (commutative Mequiv Madd). }
Qed.

Definition finitely_generated {n: nat}(basis: t M n) :=
  forall (vector: M),
    exists (coeffs: t R n),
      vector =M= linear_combin coeffs basis.
  
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

Context {module: Module_ Radd Rmul Rone Mequiv Madd Mzero Mminus action}.

Section QuotientModules.
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

Section IdealModule.
Context (P: R -> Prop).
Context {P_proper: Proper (Requiv ==> iff) P}.
Context {P_ideal: Ideal Radd Rzero Rminus Rmul P}.

Definition ideal_module (x: M): Prop :=
  exists (n: nat)(coeffs: t R n)(vectors: t M n),
    Forall P coeffs /\
    x =M= linear_combin Madd Mzero action coeffs vectors.

Lemma module_ideal_module_proper:
  Proper (Mequiv ==> iff) ideal_module.
Proof.
  intros x0 x1 Hx.
  unfold ideal_module.
  split;
    intros H.
  { inversion_clear H as [n [coeffs [vectors [Hcoeffs Hx0]]]].
    exists n.
    exists coeffs.
    exists vectors.
    split;
      [assumption |].
    setoid_rewrite Hx in Hx0.
    assumption. }
  { inversion_clear H as [n [coeffs [vectors [Hcoeffs Hx0]]]].
    exists n.
    exists coeffs.
    exists vectors.
    split;
      [assumption |].
    setoid_rewrite Hx.
    assumption. }
Qed.

Lemma module_ideal_module_add_closed:
  forall (u v: M),
    ideal_module u ->
    ideal_module v ->
    ideal_module (u <+> v).
Proof.
  intros u v [nu [coeffsu [vectorsu [Hcoeffsu Hu]]]].
  intros [nv [coeffsv [vectorsv [Hcoeffsv Hv]]]].
  exists (nu + nv).
  exists (append coeffsu coeffsv).
  exists (append vectorsu vectorsv).
  split.
  { apply vector_forall_append.
    split;
      assumption. }
  { setoid_rewrite Hu.
    setoid_rewrite Hv.
    symmetry.
    apply (module_linear_combin_append Radd Rmul Rone Mequiv Madd Mzero Mminus action). }
Qed.

Lemma module_linear_combin_minus_l {n: nat}(vectors: t M n)(coeffs: t R n):
  linear_combin Madd Mzero action (map (fun coeff => Rminus coeff) coeffs) vectors =M=
    Mminus (linear_combin Madd Mzero action coeffs vectors).
Proof.
  generalize dependent vectors.
  generalize dependent coeffs.
  generalize dependent n.
  apply vector_ind2;
    simpl.
  { symmetry.
    apply (group_inv_ident Mequiv Madd Mzero Mminus). }
  { intros n coeffs vectors IH a b.
    setoid_rewrite (module_minus_l Requiv Radd Rzero Rminus Rmul Rone Mequiv Madd Mzero Mminus action).
    setoid_rewrite IH.
    setoid_rewrite <- (group_inv_op Mequiv Madd Mzero Mminus).
    apply Mminus_proper.
    apply (commutative Mequiv Madd). }
Qed.

Lemma module_ideal_module_minus_closed:
  forall (u: M),
    ideal_module u ->
    ideal_module (Mminus u).
Proof.
  unfold ideal_module.
  intros u [n [coeffs [vectors [Hcoeffs Hu]]]].
  exists n.
  exists (map (fun r => Rminus r) coeffs).
  exists vectors.
  split.
  { apply vector_forall_map;
      [| assumption].
    apply (subgroup_inv_closed Radd Rzero Rminus P). }
  { setoid_rewrite module_linear_combin_minus_l.
    setoid_rewrite Hu.
    reflexivity. }
Qed.

Lemma module_ideal_module_zero:
  ideal_module Mzero.
Proof.
  exists 0.
  exists (nil R).
  exists (nil M).
  split;
    [constructor |].
  simpl.
  reflexivity.
Qed.

Lemma module_linear_combin_mul_l {n: nat}(coeffs: t R n)(vectors: t M n):
  forall (r: R),
    linear_combin Madd Mzero action (map (fun coeff => r [*] coeff) coeffs) vectors
      =M= r <.> linear_combin Madd Mzero action coeffs vectors.
Proof.
  intros r.
  generalize dependent vectors.
  generalize dependent coeffs.
  generalize dependent n.
  apply vector_ind2;
    simpl.
  { symmetry.
    apply (module_0_r Requiv Radd Rmul Rone Mequiv Madd Mzero Mminus action). }
  { intros n coeffs vectors IH a b.
    setoid_rewrite IH.
    setoid_rewrite (module_distrib_Rmul Radd Rmul Rone Mequiv Madd Mzero Mminus action).
    setoid_rewrite <- (module_distrib_Madd Radd Rmul Rone Mequiv Madd Mzero Mminus action).
    apply (module_op_l Requiv Mequiv action).
    reflexivity. }
Qed.

Lemma module_ideal_module_action:
  forall (a: M), ideal_module a ->
    forall (r: R), ideal_module (r <.> a).
Proof.
  intros a [n [coeffs [vectors [Hcoeffs Ha]]]] r.
  exists n.
  exists (map (fun coeff => r [*] coeff) coeffs).
  exists vectors.
  split.
  { apply vector_forall_map;
      [| assumption].
    intros b Hb.
    apply (ideal_mul_absorb_l Radd Rzero Rminus Rmul P).
    assumption. }
  { setoid_rewrite Ha.
    symmetry.
    apply module_linear_combin_mul_l. }
Qed.

#[global]
Instance ideal_module_subgroup: Subgroup Madd Mzero Mminus ideal_module := {
  subgroup_op_closed := module_ideal_module_add_closed;
  subgroup_inv_closed := module_ideal_module_minus_closed;
  subgroup_ident := module_ideal_module_zero;
}.

#[global]
Instance ideal_module_submodule: Submodule Madd Mzero Mminus action ideal_module := {
  submodule_subgroup := ideal_module_subgroup;
  submodule_action := module_ideal_module_action;
}.
End IdealModule.
End Modules.
