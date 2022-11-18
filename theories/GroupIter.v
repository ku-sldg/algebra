Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
Require Import Coq.PArith.PArith.
Require Import Coq.ZArith.ZArith.
From algebra Require Import Semigroups Monoids Groups.

Section OpIterations.
Context {Carrier: Type}.
Context (equiv: relation Carrier).
Context {equiv_equiv: Equivalence equiv}.
Context (op: Carrier -> Carrier -> Carrier).
Context {op_proper: Proper (equiv ==> equiv ==> equiv) op}.

Definition semigroup_iter_op (p: positive)(a: Carrier): Carrier :=
  Pos.iter_op op p a.

Theorem semigroup_iter_op_proper:
  Proper (eq ==> equiv ==> equiv) semigroup_iter_op.
Proof.
  intros m n ->.
  induction n;
    intros a0 a1 Ha;
    simpl;
    [ | | assumption].
  { apply op_proper;
      [assumption |].
    apply IHn.
    apply op_proper;
      assumption. }
  { apply IHn.
    apply op_proper;
      assumption. }
Qed.

Context {semigroup: Semigroup equiv op}.
Infix "==" := equiv (at level 60, no associativity).
Infix "<o>" := op (at level 40, left associativity).

Theorem semigroup_iter_op_succ (p: positive)(a: Carrier):
  semigroup_iter_op (Pos.succ p) a == a <o> semigroup_iter_op p a.
Proof.
  generalize dependent a.
  induction p;
    intros a;
    simpl;
    [| reflexivity | reflexivity].
  setoid_rewrite <- (semigroup_assoc equiv op).
  apply IHp.
Qed.

Theorem semigroup_iter_op_add (p q: positive)(a: Carrier):
  semigroup_iter_op (p + q) a ==
    semigroup_iter_op p a <o> semigroup_iter_op q a.
Proof.
  generalize dependent a.
  generalize dependent q.
  induction p using Pos.peano_ind;
    intros q a.
  { rewrite Pos.add_1_l.
    apply semigroup_iter_op_succ. }
  { rewrite Pos.add_succ_l.
    setoid_rewrite semigroup_iter_op_succ.
    setoid_rewrite IHp.
    symmetry.
    apply (semigroup_assoc equiv op). }
Qed.

Theorem semigroup_iter_op_mul (p q: positive)(a: Carrier):
  semigroup_iter_op (p * q) a ==
    semigroup_iter_op p (semigroup_iter_op q a).
Proof.
  generalize dependent a.
  generalize dependent q.
  induction p using Pos.peano_ind;
    intros q a;
    simpl;
    try reflexivity.
  rewrite <- Pos.add_1_r.
  rewrite Pos.mul_add_distr_r.
  rewrite Pos.mul_1_l.
  setoid_rewrite semigroup_iter_op_add.
  simpl.
  apply (semigroup_op_r equiv op).
  apply IHp.
Qed.

Lemma semigroup_iter_op_comm_single (p: positive)(a b: Carrier):
  a <o> b == b <o> a ->
  a <o> semigroup_iter_op p b ==
    semigroup_iter_op p b <o> a.
Proof.
  generalize dependent b.
  generalize dependent a.
  induction p using Pos.peano_ind;
    intros a b Hab;
    simpl;
    [assumption |].
  setoid_rewrite semigroup_iter_op_succ.
  setoid_rewrite <- (semigroup_assoc equiv op).
  setoid_rewrite Hab.
  setoid_rewrite (semigroup_assoc equiv op).
  apply (semigroup_op_l equiv op).
  apply (IHp _ _ Hab).
Qed.

Lemma semigroup_iter_op_comm (p q: positive)(a b: Carrier):
  a <o> b == b <o> a ->
  semigroup_iter_op p a <o> semigroup_iter_op q b ==
    semigroup_iter_op q b <o> semigroup_iter_op p a.
Proof.
  generalize dependent b.
  generalize dependent a.
  generalize dependent q.
  induction p using Pos.peano_ind;
    intros q a b Hab;
    simpl.
  { apply semigroup_iter_op_comm_single.
    assumption. }
  { setoid_rewrite semigroup_iter_op_succ.
    setoid_rewrite <- (semigroup_assoc equiv op).
    setoid_rewrite <- (semigroup_iter_op_comm_single _ _ _ Hab).
    setoid_rewrite (semigroup_assoc equiv op).
    apply (semigroup_op_l equiv op).
    apply (IHp _ _ _ Hab). }
Qed.

Context (ident: Carrier).
Context {monoid: Monoid equiv op ident}.

Lemma semigroup_iter_op_ident (p: positive):
  semigroup_iter_op p ident == ident.
Proof.
  induction p using Pos.peano_ind;
    simpl;
    [reflexivity |].
  setoid_rewrite semigroup_iter_op_succ.
  setoid_rewrite (monoid_ident_l equiv op ident).
  assumption.
Qed.

Context (inv: Carrier -> Carrier).
Context {inv_proper: Proper (equiv ==> equiv) inv}.
Context {group: Group equiv op ident inv}.

Definition group_iter_op (n: Z)(a: Carrier): Carrier :=
  match n with
  | Z0 => ident
  | Zpos p => semigroup_iter_op p a
  | Zneg p => semigroup_iter_op p (inv a)
  end.

Theorem group_iter_op_proper:
  Proper (eq ==> equiv ==> equiv) group_iter_op.
Proof.
  intros m n ->.
  destruct n;
    intros a0 a1 Ha;
    simpl;
    try apply semigroup_iter_op_proper;
    try reflexivity.
  { assumption. }
  { apply inv_proper.
    assumption. }
Qed.

Lemma semigroup_iter_op_inv (p: positive)(a: Carrier):
  semigroup_iter_op p (inv a) ==
    inv (semigroup_iter_op p a).
Proof.
  generalize dependent a.
  induction p using Pos.peano_ind;
    intros a;
    simpl;
    [reflexivity |].
  setoid_rewrite semigroup_iter_op_succ.
  setoid_rewrite IHp.
  setoid_rewrite <- (group_inv_op equiv op ident inv).
  apply inv_proper.
  symmetry.
  apply semigroup_iter_op_comm_single.
  reflexivity.
Qed.

Theorem group_iter_op_ident (n: Z):
  group_iter_op n ident == ident.
Proof.
  destruct n as [| p | p];
    simpl;
    [reflexivity | |].
  { apply semigroup_iter_op_ident. }
  { setoid_rewrite semigroup_iter_op_inv.
    setoid_rewrite semigroup_iter_op_ident.
    apply (group_inv_ident equiv op ident inv). }
Qed.

Lemma semigroup_iter_op_pred_double (p: positive)(a: Carrier):
  semigroup_iter_op (Pos.pred_double p) a ==
    inv a <o> semigroup_iter_op p (a <o> a).
Proof.
  generalize dependent a.
  induction p;
    intros a;
    simpl.
  { transitivity (inv a <o> (a <o> a) <o> semigroup_iter_op p (a <o> a <o> (a <o> a)));
      [| apply (semigroup_assoc equiv op)].
    transitivity (inv a <o> a <o> a <o> semigroup_iter_op p (a <o> a <o> (a <o> a)));
      [| apply (semigroup_op_r equiv op); apply (semigroup_assoc equiv op)].
    setoid_rewrite (group_inv_l equiv op ident inv).
    setoid_rewrite (monoid_ident_l equiv op ident).
    reflexivity. }
  { setoid_rewrite IHp.
    transitivity (a <o> inv (a <o> a) <o> semigroup_iter_op p (a <o> a <o> (a <o> a)));
      [symmetry; apply (semigroup_assoc equiv op) |].
    apply (semigroup_op_r equiv op).
    setoid_rewrite (group_inv_op equiv op ident inv).
    setoid_rewrite <- (semigroup_assoc equiv op).
    setoid_rewrite (group_inv_r equiv op ident inv).
    apply (monoid_ident_l equiv op ident). }
  { setoid_rewrite <- (semigroup_assoc equiv op).
    setoid_rewrite (group_inv_l equiv op ident inv).
    symmetry.
    apply (monoid_ident_l equiv op ident). }
Qed.

Lemma semigroup_iter_op_inv_op (p: positive)(a b: Carrier):
  semigroup_iter_op p (inv (a <o> b)) ==
    semigroup_iter_op p (inv b <o> inv a).
Proof.
  apply semigroup_iter_op_proper;
    [reflexivity |].
  apply (group_inv_op equiv op ident inv).
Qed.

Lemma group_iter_op_succ_double (n: Z)(a: Carrier):
  group_iter_op (Z.succ_double n) a ==
    a <o> group_iter_op n (a <o> a).
Proof.
  destruct n;
    simpl;
    [| reflexivity |].
  { symmetry.
    apply (monoid_ident_r equiv op ident). }
  { setoid_rewrite semigroup_iter_op_pred_double.
    setoid_rewrite (group_inv_involute equiv op ident inv).
    apply (semigroup_op_l equiv op).
    symmetry.
    apply semigroup_iter_op_inv_op. }
Qed.

Lemma group_iter_op_pred_double (n: Z)(a: Carrier):
  group_iter_op (Z.pred_double n) a ==
    inv a <o> group_iter_op n (a <o> a).
Proof.
  destruct n;
    simpl;
    [| apply semigroup_iter_op_pred_double |].
  { symmetry.
    apply (monoid_ident_r equiv op ident). }
  { apply (semigroup_op_l equiv op).
    symmetry.
    apply semigroup_iter_op_inv_op. }
Qed.

Lemma group_iter_op_double (n: Z)(a: Carrier):
  group_iter_op (Z.double n) a ==
    group_iter_op n (a <o> a).
Proof.
  destruct n;
    simpl;
    [reflexivity | reflexivity |].
  symmetry.
  apply semigroup_iter_op_inv_op.
Qed.

Lemma group_iter_op_pos_sub (p q: positive)(a: Carrier):
  group_iter_op (Z.pos_sub p q) a ==
    semigroup_iter_op p a <o> semigroup_iter_op q (inv a).
Proof.
  generalize dependent a.
  generalize dependent q.
  induction p;
    destruct q;
    intros a;
    simpl.
  { setoid_rewrite group_iter_op_double.
    setoid_rewrite IHp.
    setoid_rewrite <- (semigroup_assoc equiv op).
    transitivity (a <o> semigroup_iter_op p (a <o> a) <o> inv a <o>
        semigroup_iter_op q (inv (a <o> a)));
      [| apply (semigroup_op_l equiv op)].
    { apply (semigroup_op_r equiv op).
      setoid_rewrite (semigroup_assoc equiv op).
      transitivity (a <o> (inv a <o> semigroup_iter_op p (a <o> a)));
        [| apply (semigroup_op_l equiv op);
          apply semigroup_iter_op_comm_single].
      { setoid_rewrite <- (semigroup_assoc equiv op).
        setoid_rewrite (group_inv_r equiv op ident inv).
        symmetry.
        apply (monoid_ident_l equiv op ident). }
      { apply (group_move_r equiv op ident inv).
        setoid_rewrite (semigroup_assoc equiv op).
        symmetry.
        apply (group_move_l equiv op ident inv).
        symmetry.
        apply (semigroup_assoc equiv op). } }
    { apply semigroup_iter_op_inv_op. } }
  { setoid_rewrite group_iter_op_succ_double.
    setoid_rewrite IHp.
    setoid_rewrite <- (semigroup_assoc equiv op).
    apply (semigroup_op_l equiv op).
    apply semigroup_iter_op_inv_op. }
  { apply (group_move_r equiv op ident inv).
    symmetry.
    apply semigroup_iter_op_comm_single.
    symmetry.
    apply (semigroup_assoc equiv op). }
  { setoid_rewrite group_iter_op_pred_double.
    setoid_rewrite IHp.
    transitivity (semigroup_iter_op p (a <o> a) <o> inv a <o>
        semigroup_iter_op q (inv a <o> inv a));
      [| apply (semigroup_assoc equiv op)].
    transitivity (inv a <o> semigroup_iter_op p (a <o> a) <o>
        semigroup_iter_op q (inv a <o> inv a));
      [| apply (semigroup_op_r equiv op)].
    { setoid_rewrite <- (semigroup_assoc equiv op).
      apply (semigroup_op_l equiv op).
      apply semigroup_iter_op_inv_op. }
    { apply semigroup_iter_op_comm_single.
      symmetry;
      apply (group_move_l equiv op ident inv);
      symmetry.
      repeat setoid_rewrite <- (semigroup_assoc equiv op).
      apply (group_move_r equiv op ident inv).
      reflexivity. } }
  { setoid_rewrite group_iter_op_double.
    setoid_rewrite IHp.
    apply (semigroup_op_l equiv op).
    apply semigroup_iter_op_inv_op. }
  { setoid_rewrite semigroup_iter_op_pred_double.
    apply semigroup_iter_op_comm_single.
    setoid_rewrite <- (semigroup_assoc equiv op).
    setoid_rewrite (group_inv_l equiv op ident inv).
    setoid_rewrite (monoid_ident_l equiv op ident).
    apply (group_move_r equiv op ident inv).
    reflexivity. }
  { setoid_rewrite <- (semigroup_assoc equiv op).
    setoid_rewrite (group_inv_r equiv op ident inv).
    symmetry.
    apply (monoid_ident_l equiv op ident). }
  { setoid_rewrite semigroup_iter_op_pred_double.
    setoid_rewrite (group_inv_involute equiv op ident inv).
    reflexivity. }
  { symmetry.
    apply (group_inv_r equiv op ident inv). }
Qed.

Theorem group_iter_op_add (m n: Z)(a: Carrier):
  group_iter_op (m + n) a ==
    group_iter_op m a <o> group_iter_op n a.
Proof.
  generalize dependent a.
  destruct m as [| p | p],
    n as [| q | q];
    intros a;
    simpl;
    try (symmetry; apply (monoid_ident_l equiv op ident));
    try (symmetry; apply (monoid_ident_r equiv op ident));
    try apply semigroup_iter_op_add.
  { apply group_iter_op_pos_sub. }
  { setoid_rewrite group_iter_op_pos_sub.
    apply semigroup_iter_op_comm.
    setoid_rewrite (group_inv_l equiv op ident inv).
    apply (group_inv_r equiv op ident inv). }
Qed.

Theorem group_iter_op_neg (n: Z)(a: Carrier):
  group_iter_op (-n) a == group_iter_op n (inv a).
Proof.
  destruct n as [| p | p];
    simpl;
    [reflexivity | reflexivity |].
  symmetry.
  apply semigroup_iter_op_proper;
    [reflexivity |].
  apply (group_inv_involute equiv op ident inv).
Qed.

Theorem group_iter_op_inv (n: Z)(a: Carrier):
  group_iter_op n (inv a) == inv (group_iter_op n a).
Proof.
  destruct n;
    simpl.
  { symmetry;
    apply (group_inv_ident equiv op ident inv). }
  { apply semigroup_iter_op_inv. }
  { apply semigroup_iter_op_inv. }
Qed.

Theorem group_iter_op_comm (m n: Z)(a b: Carrier):
  a <o> b == b <o> a ->
  group_iter_op m a <o> group_iter_op n b ==
    group_iter_op n b <o> group_iter_op m a.
Proof.
  intros Hab.
  destruct m as [| p | p], n as [| q | q];
    simpl;
    try (setoid_rewrite (monoid_ident_r equiv op ident));
    try (setoid_rewrite (monoid_ident_l equiv op ident));
    try reflexivity.
  { apply semigroup_iter_op_comm;
      assumption. }
  { apply semigroup_iter_op_comm.
    apply (group_move_l equiv op ident inv).
    symmetry.
    setoid_rewrite <- (semigroup_assoc equiv op).
    apply (group_move_r equiv op ident inv).
    assumption. }
  { apply semigroup_iter_op_comm.
    apply (group_move_r equiv op ident inv).
    symmetry.
    setoid_rewrite (semigroup_assoc equiv op).
    apply (group_move_l equiv op ident inv).
    assumption. }
  { apply semigroup_iter_op_comm.
    setoid_rewrite <- (group_inv_op equiv op ident inv).
    apply inv_proper.
    symmetry.
    assumption. }
Qed.

Theorem group_iter_op_mul (m n: Z)(a: Carrier):
  group_iter_op (m * n) a ==
    group_iter_op m (group_iter_op n a).
Proof.
  destruct m as [| p | p].
  { rewrite Z.mul_0_l.
    simpl.
    reflexivity. }
  { destruct n as [| q | q];
      simpl.
    { symmetry;
        apply semigroup_iter_op_ident. }
    { apply semigroup_iter_op_mul. }
    { apply semigroup_iter_op_mul. } }
  { destruct n as [| q | q];
      simpl.
    { symmetry.
      setoid_rewrite semigroup_iter_op_inv.
      setoid_rewrite semigroup_iter_op_ident.
      apply (group_inv_ident equiv op ident inv). }
    { setoid_rewrite semigroup_iter_op_mul.
      apply semigroup_iter_op_proper;
        [reflexivity |].
      apply semigroup_iter_op_inv. }
    { setoid_rewrite semigroup_iter_op_mul.
      apply semigroup_iter_op_proper;
        [reflexivity |].
      symmetry.
      setoid_rewrite semigroup_iter_op_inv.
      setoid_rewrite (group_inv_involute equiv op ident inv).
      reflexivity. } }
Qed.
End OpIterations.
