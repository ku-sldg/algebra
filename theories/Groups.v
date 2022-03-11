Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From algebra Require Import Semigroups Monoids.

Section Groups.
Context {Carrier: Type}.
Context (equiv: relation Carrier).
Context {R_equiv: Equivalence equiv}.
Context (op: Carrier -> Carrier -> Carrier).
Context {op_proper: Proper (equiv ==> equiv ==> equiv) op}.
Context (ident: Carrier).
Context (inv: Carrier -> Carrier).
Context {inv_proper: Proper (equiv ==> equiv) inv}.

Infix "~" := equiv (at level 60, no associativity).
Infix "<o>" := op (at level 40, left associativity).

Class Group := {
  group_monoid :> Monoid equiv op ident;
  group_inv_l:
    forall (a: Carrier), inv a <o> a ~ ident;
  group_inv_r:
    forall (a: Carrier), a <o> inv a ~ ident;
}.

Context {group: Group}.

Definition group_assoc :=
  semigroup_assoc equiv op.
Definition group_op_l :=
  semigroup_op_l equiv op.
Definition group_op_l_solo :=
  monoid_op_l_solo equiv op ident.
Definition group_op_r :=
  semigroup_op_r equiv op.
Definition group_op_r_solo :=
  monoid_op_r_solo equiv op ident.
Definition group_ident_l :=
  monoid_ident_l equiv op ident.
Definition group_ident_r :=
  monoid_ident_r equiv op ident.

Lemma group_cancel_l (a b c: Carrier):
  c <o> a ~ c <o> b -> a ~ b.
Proof.
  intros H.
  apply group_op_l with (c := inv c) in H.
  transitivity (ident <o> b);
    [| apply group_ident_l].
  transitivity (inv c <o> c <o> b);
    [| apply group_op_r; apply group_inv_l].
  transitivity (inv c <o> (c <o> b));
    [| symmetry; apply group_assoc].
  transitivity (ident <o> a);
    [symmetry; apply group_ident_l |].
  transitivity (inv c <o> c <o> a);
    [symmetry; apply group_op_r; apply group_inv_l |].
  transitivity (inv c <o> (c <o> a));
    [apply group_assoc |].
  assumption.
Qed.

Lemma group_cancel_r (a b c: Carrier):
  a <o> c ~ b <o> c -> a ~ b.
Proof.
  intros H.
  apply group_op_r with (c := inv c) in H.
  transitivity (b <o> ident);
    [| apply group_ident_r].
  transitivity (b <o> (c <o> inv c));
    [| apply group_op_l; apply group_inv_r].
  transitivity (b <o> c <o> inv c);
    [| apply group_assoc].
  transitivity (a <o> ident);
    [symmetry; apply group_ident_r |].
  transitivity (a <o> (c <o> inv c));
    [symmetry; apply group_op_l; apply group_inv_r |].
  transitivity (a <o> c <o> inv c);
    [symmetry; apply group_assoc |].
  assumption.
Qed.

Lemma group_move_l (a b c: Carrier):
  a <o> b ~ c -> b ~ inv a <o> c.
Proof.
  intros H.
  apply group_cancel_l with (a).
  transitivity (a <o> inv a <o> c);
    [| apply group_assoc].
  transitivity (ident <o> c);
    [| apply group_op_r; symmetry; apply group_inv_r].
  transitivity (c);
    [assumption | symmetry; apply group_ident_l].
Qed.

Lemma group_move_r (a b c: Carrier):
  a <o> b ~ c -> a ~ c <o> inv b.
Proof.
  intros H.
  apply group_cancel_r with (b).
  transitivity (c <o> (inv b <o> b));
    [| symmetry; apply group_assoc].
  transitivity (c <o> ident);
    [| symmetry; apply group_op_l; apply group_inv_l].
  transitivity c;
    [assumption | symmetry; apply group_ident_r].
Qed.

Theorem group_idemp_ident (a: Carrier):
  a <o> a ~ a ->
  a ~ ident.
Proof.
  intros H.
  apply group_cancel_r with (a).
  transitivity (a);
    [assumption |].
  symmetry.
  apply group_ident_l.
Qed.

Theorem group_inv_l_unique (a aInv: Carrier):
  aInv <o> a ~ ident ->
  aInv ~ inv a.
Proof.
  intros H.
  apply group_cancel_r with (a).
  transitivity (ident);
    [assumption |].
  symmetry.
  apply group_inv_l.
Qed.

Theorem group_inv_r_unique (a aInv: Carrier):
  a <o> aInv ~ ident ->
  aInv ~ inv a.
Proof.
  intros H.
  apply group_cancel_l with (a).
  transitivity (ident);
    [assumption |].
  symmetry.
  apply group_inv_r.
Qed.

Theorem group_inv_involute (a: Carrier):
  inv (inv a) ~ a.
Proof.
  symmetry.
  apply group_inv_r_unique.
  apply group_inv_l.
Qed.

Theorem group_inv_op (a b: Carrier):
  inv (a <o> b) ~ inv b <o> inv a.
Proof.
  symmetry.
  apply group_inv_r_unique.
  transitivity (a <o> b <o> inv b <o> inv a);
    [symmetry; apply group_assoc |].
  symmetry.
  apply group_move_r.
  transitivity (a);
    [apply group_ident_l |].
  apply group_move_r.
  reflexivity.
Qed.

Theorem group_solution_r (a b: Carrier):
  (exists (x: Carrier), x <o> a ~ b) /\
  (forall (x: Carrier),
    x <o> a ~ b -> x ~ b <o> inv a).
Proof.
  split.
  { exists (b <o> inv a).
    transitivity (b <o> (inv a <o> a));
      [apply group_assoc |].
    apply group_op_l_solo.
    apply group_inv_l. }
  { intros x.
    apply group_move_r. }
Qed.

Theorem group_solution_l (a b: Carrier):
  (exists (x: Carrier), a <o> x ~ b) /\
  (forall (x: Carrier),
    a <o> x ~ b -> x ~ inv a <o> b).
Proof.
  split.
  { exists (inv a <o> b).
    transitivity (a <o> inv a <o> b);
      [symmetry; apply group_assoc |].
    apply group_op_r_solo.
    apply group_inv_r. }
  { intros x.
    apply group_move_l. }
Qed.

Theorem group_inv_ident:
  inv ident ~ ident.
Proof.
  symmetry.
  apply group_inv_r_unique.
  apply group_ident_r.
Qed.

Section Subgroups.
Context (P: Carrier -> Prop).
Context (P_proper: Proper (equiv ==> iff) P).

Lemma subset_op_inv_closed_ident:
  (exists (x: Carrier), P x) ->
  (forall (a b: Carrier),
    P a -> P b -> P (a <o> inv b)) ->
  P ident.
Proof.
  intros [x HPx] Hop_inv.
  specialize (Hop_inv x x HPx HPx).
  assert (x <o> inv x ~ ident) by apply group_inv_r.
  apply P_proper in H.
  apply H.
  assumption.
Qed.

Lemma subset_op_inv_closed_inv_closed:
  (exists (x: Carrier), P x) ->
  (forall (a b: Carrier),
    P a -> P b -> P (a <o> inv b)) ->
  (forall (a: Carrier), P a -> P (inv a)).
Proof.
  intros Hx Hop_inv a HPa.
  assert (P ident)
    as HPident
    by apply (subset_op_inv_closed_ident Hx Hop_inv).
  specialize (Hop_inv ident a HPident HPa).
  assert (ident <o> inv a ~ inv a)
    by apply group_ident_l.
  apply P_proper in H.
  apply H.
  assumption.
Qed.

Lemma subset_op_inv_closed_op_closed:
  (exists (x: Carrier), P x) ->
  (forall (a b: Carrier),
    P a -> P b -> P (a <o> inv b)) ->
  (forall (a b: Carrier), P a -> P b -> P (a <o> b)).
Proof.
  intros Hx Hop_inv a b HPa HPb.
  assert (P (inv b))
    as HPb'
    by apply (subset_op_inv_closed_inv_closed Hx Hop_inv b HPb).
  specialize (Hop_inv a (inv b) HPa HPb').
  assert (a <o> inv (inv b) ~ a <o> b)
    by (apply group_op_l; apply group_inv_involute).
  apply P_proper in H.
  apply H.
  assumption.
Qed.

Class Subgroup := {
  subgroup_op_closed:
    forall (a b: Carrier), P a -> P b -> P (a <o> b);
  subgroup_inv_closed:
    forall (a: Carrier), P a -> P (inv a);
  subgroup_ident: P ident;
}.

Theorem subset_op_inv_closed_subgroup:
  (exists (x: Carrier), P x) ->
  (forall (a b: Carrier),
    P a -> P b -> P (a <o> inv b)) ->
  Subgroup.
Proof.
  intros Hx Hop_inv.
  constructor.
  { apply subset_op_inv_closed_op_closed;
    assumption. }
  { apply subset_op_inv_closed_inv_closed;
    assumption. }
  { apply subset_op_inv_closed_ident;
    assumption. }
Qed.

Context {subgroup: Subgroup}.

Lemma subgroup_inv_inv_closed (a: Carrier):
  P (inv a) -> P a.
Proof.
  intros HPa'.
  apply subgroup_inv_closed in HPa'.
  assert (inv (inv a) ~ a)
    by apply group_inv_involute.
  apply P_proper in H.
  apply H.
  assumption.
Qed.

Definition left_congru (a b: Carrier) :=
  P (inv a <o> b).
Definition right_congru (a b: Carrier) :=
  P (a <o> inv b).

Theorem left_congru_proper:
  Proper (equiv ==> equiv ==> iff) left_congru.
Proof.
  intros a0 a1 Ha b0 b1 Hb.
  unfold left_congru.
  split;
    intros HPa'b;
  assert (inv a0 <o> b0 ~ inv a1 <o> b1);
    try (apply op_proper;
      [apply inv_proper |];
      assumption);
  apply P_proper in H;
  apply H;
  assumption.
Qed.

Theorem right_congru_proper:
  Proper (equiv ==> equiv ==> iff) right_congru.
Proof.
  intros a0 a1 Ha b0 b1 Hb.
  unfold right_congru.
  split;
    intros Hab';
  assert (a0 <o> inv b0 ~ a1 <o> inv b1);
    try (apply op_proper;
      [| apply inv_proper];
      assumption);
  apply P_proper in H;
  apply H;
  assumption.
Qed.

Lemma left_congru_reflexive (a: Carrier):
  left_congru a a.
Proof.
  unfold left_congru.
  assert (inv a <o> a ~ ident)
    by apply group_inv_l.
  apply P_proper in H.
  apply H.
  apply subgroup_ident.
Qed.

Lemma left_congru_symmetric (a b: Carrier):
  left_congru a b -> left_congru b a.
Proof.
  unfold left_congru.
  intros HPa'b.
  apply subgroup_inv_closed in HPa'b.
  assert (inv (inv a <o> b) ~ inv b <o> a).
  { transitivity (inv b <o> inv (inv a));
      [apply group_inv_op |].
    apply group_op_l.
    apply group_inv_involute. }
  { apply P_proper in H.
    apply H.
    assumption. }
Qed.

Lemma left_congru_transitive (a b c: Carrier):
  left_congru a b ->
  left_congru b c ->
  left_congru a c.
Proof.
  unfold left_congru.
  intros HPa'b HPb'c.
  assert (inv a <o> b <o> (inv b <o> c) ~ inv a <o> c).
  { transitivity (inv a <o> b <o> inv b <o> c);
      [symmetry; apply group_assoc |].
    apply group_op_r.
    transitivity (inv a <o> (b <o> inv b));
      [apply group_assoc |].
    apply group_op_l_solo.
    apply group_inv_r. }
  { apply P_proper in H.
    apply H.
    apply subgroup_op_closed;
      assumption. }
Qed.

#[global]
Instance left_congru_equiv: Equivalence left_congru := {
  Equivalence_Reflexive := left_congru_reflexive;
  Equivalence_Symmetric := left_congru_symmetric;
  Equivalence_Transitive := left_congru_transitive;
}.

Lemma right_congru_reflexive (a: Carrier):
  right_congru a a.
Proof.
  unfold right_congru.
  assert (a <o> inv a ~ ident)
    by apply group_inv_r.
  apply P_proper in H.
  apply H.
  apply subgroup_ident.
Qed.

Lemma right_congru_symmetric (a b: Carrier):
  right_congru a b -> right_congru b a.
Proof.
  unfold right_congru.
  intros HPab'.
  apply subgroup_inv_closed in HPab'.
  assert (inv (a <o> inv b) ~ b <o> inv a).
  { transitivity (inv (inv b) <o> inv a);
      [apply group_inv_op |].
    apply group_op_r.
    apply group_inv_involute. }
  { apply P_proper in H.
    apply H.
    assumption. }
Qed.

Lemma right_congru_transitive (a b c: Carrier):
  right_congru a b ->
  right_congru b c ->
  right_congru a c.
Proof.
  unfold right_congru.
  intros HPab' HPbc'.
  assert (a <o> inv b <o> (b <o> inv c) ~ a <o> inv c).
  { transitivity (a <o> inv b <o> b <o> inv c);
      [symmetry; apply group_assoc |].
    apply group_op_r.
    transitivity (a <o> (inv b <o> b));
      [apply group_assoc |].
    apply group_op_l_solo.
    apply group_inv_l. }
  { apply P_proper in H.
    apply H.
    apply subgroup_op_closed;
      assumption. }
Qed.

#[global]
Instance right_congru_equiv: Equivalence right_congru := {
  Equivalence_Reflexive := right_congru_reflexive;
  Equivalence_Symmetric := right_congru_symmetric;
  Equivalence_Transitive := right_congru_transitive;
}.

Definition left_cosets_eq (a b: Carrier) :=
  forall (m: Carrier),
    P m ->
    exists (n: Carrier), P n /\ a <o> m ~ b <o> n.

Lemma subgroup_equiv_left_congru_cosets_eq (a b: Carrier):
  left_congru a b <-> left_cosets_eq a b.
Proof.
  unfold left_congru, left_cosets_eq.
  split;
    [intros HPa'b m HPm | intros Hcoset].
  { exists (inv b <o> (a <o> m)).
    split.
    { apply subgroup_inv_closed in HPa'b.
      assert (inv (inv a <o> b) <o> m ~ inv b <o> (a <o> m)).
      { transitivity (inv b <o> inv (inv a) <o> m);
          [apply group_op_r; apply group_inv_op |].
        transitivity (inv b <o> (inv (inv a) <o> m));
          [apply group_assoc |].
        apply group_op_l.
        apply group_op_r.
        apply group_inv_involute. }
      { apply P_proper in H.
        apply H.
        apply subgroup_op_closed;
          assumption. } }
    { symmetry.
      transitivity (b <o> inv b <o> (a <o> m));
        [symmetry; apply group_assoc |].
      apply group_op_r_solo.
      apply group_inv_r. } }
  { specialize (Hcoset ident subgroup_ident).
    inversion_clear Hcoset as [n [HPn H]].
    assert (inv n ~ inv a <o> b).
    { symmetry.
      apply group_inv_l_unique.
      apply group_cancel_l with (c := a).
      transitivity (a <o> (inv a <o> b) <o> n);
        [symmetry; apply group_assoc |].
      transitivity (a <o> inv a <o> b <o> n);
        [symmetry; apply group_op_r; apply group_assoc |].
      transitivity (ident <o> b <o> n);
        [repeat apply group_op_r; apply group_inv_r |].
      transitivity (b <o> n);
        [apply group_op_r; apply group_ident_l |].
      symmetry.
      assumption. }
    { apply P_proper in H0.
      apply H0.
      apply subgroup_inv_closed.
      assumption. } }
Qed.

Definition right_cosets_eq (a b: Carrier) :=
  forall (m: Carrier),
    P m ->
    exists (n: Carrier), P n /\ m <o> a ~ n <o> b.

Lemma subgroup_equiv_right_congru_cosets_eq (a b: Carrier):
  right_congru a b <-> right_cosets_eq a b.
Proof.
  unfold right_congru, right_cosets_eq.
  split;
    [intros HPab' m HPm | intros Hcoset].
  { exists (m <o> (a <o> inv b)).
    split;
      [apply subgroup_op_closed; assumption |].
    symmetry.
    transitivity (m <o> a <o> inv b <o> b);
      [apply group_op_r; symmetry; apply group_assoc |].
    transitivity (m <o> a <o> (inv b <o> b));
      [apply group_assoc |].
    apply group_op_l_solo.
    apply group_inv_l. }
  { specialize (Hcoset ident subgroup_ident).
    inversion_clear Hcoset as [n [HPn H]].
    assert (a <o> inv b ~ n).
    { apply group_cancel_r with (c := b).
      transitivity (a <o> (inv b <o> b));
        [apply group_assoc |].
      transitivity (a <o> ident);
        [apply group_op_l; apply group_inv_l |].
      transitivity (a);
        [apply group_ident_r |].
      transitivity (ident <o> a);
        [symmetry; apply group_ident_l | assumption]. }
    { apply P_proper in H0.
      apply H0.
      assumption. } }
Qed.

Let normal_subgroup_congru_coincide := (* 1 *)
  forall (a b: Carrier),
    left_congru a b <-> right_congru a b.
Let normal_subgroup_cosets_eq_coincide := (* 2 *)
  forall (a b: Carrier),
    left_cosets_eq a b <-> right_cosets_eq a b.
Let normal_subgroup_cosets_coincide := (* 3 *)
  forall (m: Carrier),
    P m ->
    forall (a: Carrier),
      exists (n: Carrier),
        P n /\ a <o> m ~ n <o> a.
Let normal_subgroup_conj_closed := (* 4 *)
  forall (n: Carrier),
    P n ->
    forall (a: Carrier), P (a <o> n <o> inv a).
Let normal_subgroup_conj_closed_exact := (* 5 *)
  forall (n a: Carrier),
    P n <-> P (a <o> n <o> inv a).

Theorem normal_subgroup_equiv_congru_cosets_eq:
  normal_subgroup_congru_coincide <->
  normal_subgroup_cosets_eq_coincide.
Proof.
  split;
    [intros Hcongru a b | intros Hcosets a b].
  { specialize (Hcongru a b).
    split;
      [intros Hlcoset | intros Hrcoset].
    { apply subgroup_equiv_right_congru_cosets_eq.
      apply Hcongru.
      apply subgroup_equiv_left_congru_cosets_eq.
      assumption. }
    { apply subgroup_equiv_left_congru_cosets_eq.
      apply Hcongru.
      apply subgroup_equiv_right_congru_cosets_eq.
      assumption. } }
  { specialize (Hcosets a b).
    split;
      [intros Hlcongru | intros Hrcongru].
    { apply subgroup_equiv_right_congru_cosets_eq.
      apply Hcosets.
      apply subgroup_equiv_left_congru_cosets_eq.
      assumption. }
    { apply subgroup_equiv_left_congru_cosets_eq.
      apply Hcosets.
      apply subgroup_equiv_right_congru_cosets_eq.
      assumption. } }
Qed.

Theorem normal_subgroup_equiv_cosets_conj:
  normal_subgroup_cosets_coincide <->
  normal_subgroup_conj_closed.
Proof.
  split;
    [intros Hcosets | intros Hconj].
  { intros n HPn a.
    specialize (Hcosets n HPn a).
    inversion_clear Hcosets as [m [HPm H]].
    assert (a <o> n <o> inv a ~ m).
    { symmetry.
      apply group_move_r.
      symmetry.
      assumption. }
    { apply P_proper in H0.
      apply H0.
      assumption. } }
  { intros m HPm a.
    exists (a <o> m <o> inv a).
    split.
    { apply Hconj.
      assumption. }
    { symmetry.
      transitivity (a <o> m <o> (inv a <o> a));
        [apply group_assoc |].
      transitivity (a <o> m <o> ident);
        [apply group_op_l; apply group_inv_l |].
      apply group_ident_r. } }
Qed.

Theorem normal_subgroup_equiv_conj_closed:
  normal_subgroup_conj_closed <->
  normal_subgroup_conj_closed_exact.
Proof.
  split;
    [intros H | intros Hexact].
  { intros n a.
    split;
      [intros HPn | intros Hconj_n].
    { apply H.
      assumption. }
    { apply H in Hconj_n.
      specialize (Hconj_n (inv a)).
      assert (inv a <o> (a <o> n <o> inv a) <o> inv (inv a) ~ n).
      { transitivity (inv a <o> (a <o> n) <o> inv a <o> inv (inv a));
          [ apply group_op_r; symmetry; apply group_assoc |].
        transitivity (inv a <o> a <o> n <o> inv a <o> inv (inv a));
          [ repeat apply group_op_r; symmetry; apply group_assoc |].
        transitivity (ident <o> n <o> inv a <o> inv (inv a));
          [ repeat apply group_op_r; apply group_inv_l |].
        transitivity (n <o> inv a <o> inv (inv a));
          [ repeat apply group_op_r; apply group_ident_l |].
        symmetry;
        apply group_move_r.
        reflexivity. }
      { apply P_proper in H0.
        apply H0.
        assumption. } } }
  { intros n HPn a.
    apply Hexact.
    assumption. }
Qed.

Theorem normal_subgroup_equiv_congru_conj:
  normal_subgroup_congru_coincide <->
  normal_subgroup_conj_closed.
Proof.
  split;
    [intros Hcongru | intros Hconj].
  { intros n HPn a.
    assert (a <o> n <o> inv a ~ a <o> inv (a <o> inv n)).
    { transitivity (a <o> (n <o> inv a));
        [apply group_assoc | apply group_op_l].
      symmetry.
      transitivity (inv (inv n) <o> inv a); 
        [apply group_inv_op | apply group_op_r].
      apply group_inv_involute. }
    { apply P_proper in H.
      apply H.
      apply Hcongru.
      assert (inv a <o> (a <o> inv n) ~ inv n).
      { transitivity (inv a <o> a <o> inv n);
          [symmetry; apply group_assoc |].
        apply group_op_r_solo.
        apply group_inv_l. }
      { apply P_proper in H0.
        apply H0.
        apply subgroup_inv_closed.
        assumption. } } }
  { intros a b.
    split;
      [intros Hlcongru | intros Hrcongru].
    { specialize (Hconj (inv a <o> b) Hlcongru b).
      assert (b <o> (inv a <o> b) <o> inv b ~ b <o> inv a).
      { transitivity (b <o> inv a <o> b <o> inv b);
          [apply group_op_r; symmetry; apply group_assoc |].
        transitivity (b <o> inv a <o> (b <o> inv b));
          [apply group_assoc | apply group_op_l_solo].
        apply group_inv_r. }
      { apply P_proper in H.
        symmetry.
        apply H.
        assumption. } } 
    { specialize (Hconj (a <o> inv b) Hrcongru (inv b)).
      assert (inv b <o> (a <o> inv b) <o> inv (inv b) ~ inv b <o> a).
      { transitivity (inv b <o> a <o> inv b <o> inv (inv b));
          [apply group_op_r; symmetry; apply group_assoc |].
        transitivity (inv b <o> a <o> (inv b <o> inv (inv b)));
          [apply group_assoc |].
        apply group_op_l_solo.
        apply group_inv_r. }
      { apply P_proper in H.
        symmetry.
        apply H.
        assumption. } } }
Qed.

Corollary normal_subgroup_equiv_congru_cosets:
  normal_subgroup_congru_coincide <->
  normal_subgroup_cosets_coincide.
Proof.
  split;
    [intros Hcongru | intros Hcosets].
  { apply normal_subgroup_equiv_cosets_conj.
    apply normal_subgroup_equiv_congru_conj.
    assumption. }
  { apply normal_subgroup_equiv_congru_conj.
    apply normal_subgroup_equiv_cosets_conj.
    assumption. }
Qed.

Corollary normal_subgroup_equiv_congru_conj_exact:
  normal_subgroup_congru_coincide <->
  normal_subgroup_conj_closed_exact.
Proof.
  split;
    [intros Hcongr | intros Hconj].
  { apply normal_subgroup_equiv_conj_closed.
    apply normal_subgroup_equiv_congru_conj.
    assumption. }
  { apply normal_subgroup_equiv_congru_conj.
    apply normal_subgroup_equiv_conj_closed.
    assumption. }
Qed.

Corollary normal_subgroup_equiv_cosets_eq_cosets:
  normal_subgroup_cosets_eq_coincide <->
  normal_subgroup_cosets_coincide.
Proof.
  split;
    [intros Hcoset_eq | intros Hcosets].
  { apply normal_subgroup_equiv_congru_cosets.
    apply normal_subgroup_equiv_congru_cosets_eq.
    assumption. }
  { apply normal_subgroup_equiv_congru_cosets_eq.
    apply normal_subgroup_equiv_congru_cosets.
    assumption. }
Qed.

Corollary normal_subgroup_equiv_cosets_eq_conj:
  normal_subgroup_cosets_eq_coincide <->
  normal_subgroup_conj_closed.
Proof.
  split;
    [intros Hcoset_eq | intros Hconj].
  { apply normal_subgroup_equiv_congru_conj.
    apply normal_subgroup_equiv_congru_cosets_eq.
    assumption. }
  { apply normal_subgroup_equiv_congru_cosets_eq.
    apply normal_subgroup_equiv_congru_conj.
    assumption. }
Qed.

Corollary normal_subgroup_equiv_cosets_eq_conj_exact:
  normal_subgroup_cosets_eq_coincide <->
  normal_subgroup_conj_closed_exact.
Proof.
  split;
    [intros Hcoset_eq | intros Hconj_exact].
  { apply normal_subgroup_equiv_conj_closed.
    apply normal_subgroup_equiv_cosets_eq_conj.
    assumption. }
  { apply normal_subgroup_equiv_cosets_eq_conj.
    apply normal_subgroup_equiv_conj_closed.
    assumption. }
Qed.

Corollary normal_subgroup_equiv_cosets_conj_exact:
  normal_subgroup_cosets_coincide <->
  normal_subgroup_conj_closed_exact.
Proof.
  split;
    [intros Hcosets | intros Hconj_exact].
  { apply normal_subgroup_equiv_conj_closed.
    apply normal_subgroup_equiv_cosets_conj.
    assumption. }
  { apply normal_subgroup_equiv_cosets_conj.
    apply normal_subgroup_equiv_conj_closed.
    assumption. }
Qed.

Section NormalSubgroups.
Lemma quotient_op_proper:
  normal_subgroup_congru_coincide ->
  Proper (left_congru ==> left_congru ==> left_congru) op.
Proof.
  intros congru_coincide a0 a1 Ha b0 b1 Hb.
  assert (inv (a0 <o> b0) <o> (a1 <o> b1) ~ inv b0 <o> (inv a0 <o> a1 <o> b1)).
  { transitivity (inv (a0 <o> b0) <o> a1 <o> b1);
      [symmetry; apply group_assoc |].
    transitivity (inv b0 <o> inv a0 <o> a1 <o> b1);
      [repeat apply group_op_r; apply group_inv_op |].
    transitivity (inv b0 <o> inv a0 <o> (a1 <o> b1));
      [apply group_assoc |].
    transitivity (inv b0 <o> (inv a0 <o> (a1 <o> b1)));
      [apply group_assoc |].
    apply group_op_l.
    symmetry.
    apply group_assoc. }
  { apply P_proper in H.
    apply H; clear H.
    apply congru_coincide.
    assert (b0 <o> inv (inv a0 <o> a1 <o> b1) ~ b0 <o> inv b1 <o> inv (inv a0 <o> a1)).
    { transitivity (b0 <o> (inv b1 <o> inv (inv a0 <o> a1)));
        [| symmetry; apply group_assoc].
      apply group_op_l.
      apply group_inv_op. }
    { apply P_proper in H.
      apply H; clear H.
      apply subgroup_op_closed;
        [apply congru_coincide | apply subgroup_inv_closed];
        assumption. } }
Qed.

Lemma quotient_inv_proper:
  normal_subgroup_congru_coincide ->
  Proper (left_congru ==> left_congru) inv.
Proof.
  intros congru_coincide a0 a1 Ha.
  assert (inv (inv a0) <o> inv a1 ~ a0 <o> inv a1).
  { apply group_op_r.
    apply group_inv_involute. }
  { apply P_proper in H.
    apply H.
    apply congru_coincide.
    assumption. }
Qed.

Lemma quotient_semigroup:
  normal_subgroup_congru_coincide ->
  Semigroup left_congru op.
Proof.
  intros congru_coincide.
  constructor.
  intros a b c.
  assert (inv (a <o> b <o> c) <o> (a <o> (b <o> c)) ~ ident);
    [| apply P_proper in H; apply H; apply subgroup_ident].
  symmetry.
  apply group_move_l.
  transitivity (a <o> b <o> c);
    [apply group_ident_r | apply group_assoc].
Qed.

Lemma quotient_monoid:
  normal_subgroup_congru_coincide ->
  Monoid left_congru op ident.
Proof.
  intros congru_coincide.
  constructor;
    [ apply quotient_semigroup;
      apply congru_coincide | |];
    intros a.
  { assert (inv (ident <o> a) <o> a ~ ident).
    { symmetry.
      apply group_move_l.
      transitivity (ident <o> a);
        [apply group_ident_r | apply group_ident_l]. }
    { apply P_proper in H.
      apply H.
      apply subgroup_ident. } }
  { assert (inv (a <o> ident) <o> a ~ ident).
    { symmetry.
      apply group_move_l.
      transitivity (a <o> ident);
        apply group_ident_r. }
    { apply P_proper in H.
      apply H.
      apply subgroup_ident. } }
Qed.
End NormalSubgroups.
End Subgroups.
End Groups.

Section NormalSubgroups.
Context {Carrier: Type}.
Context (equiv: relation Carrier).
Context {R_equiv: Equivalence equiv}.
Context (op: Carrier -> Carrier -> Carrier).
Context {op_proper: Proper (equiv ==> equiv ==> equiv) op}.
Context (ident: Carrier).
Context (inv: Carrier -> Carrier).
Context {inv_proper: Proper (equiv ==> equiv) inv}.
Context {group: Group equiv op ident inv}.
Context (P: Carrier -> Prop).
Context {P_proper: Proper (equiv ==> iff) P}.
Context {subgroup: Subgroup op ident inv P}.

Infix "~" := equiv (at level 60, no associativity).
Infix "<o>" := op (at level 40, left associativity).

Let normal_subgroup_congru_coincide :=
  forall (a b: Carrier),
    left_congru op inv P a b <->
    right_congru op inv P a b.

Theorem quotient_normal_subgroup_group:
  normal_subgroup_congru_coincide ->
  Group (left_congru op inv P) op ident inv.
Proof.
  intros congru_coincide.
  constructor;
    [apply (quotient_monoid equiv op ident inv P P_proper);
      apply congru_coincide | |];
    intros a.
  { assert (inv (inv a <o> a) <o> ident ~ ident).
    { symmetry.
      apply (group_move_l equiv op ident inv).
      transitivity (inv a <o> a);
        [apply (group_ident_r equiv op ident inv) |].
      apply (group_inv_l equiv op ident inv). }
    { apply P_proper in H.
      apply H.
      apply (subgroup_ident op ident inv P). } }
  { assert (inv (a <o> inv a) <o> ident ~ ident).
    { symmetry.
      apply (group_move_l equiv op ident inv).
      transitivity (a <o> inv a);
        [apply (group_ident_r equiv op ident inv) |].
      apply (group_inv_r equiv op ident inv). }
    { apply P_proper in H.
      apply H.
      apply (subgroup_ident op ident inv P). } }
Qed.
End NormalSubgroups.
