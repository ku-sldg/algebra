Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Semigroups Monoids.

Module Type GroupSig.
  Include MonoidSig.

  Parameter (inv: Carrier -> Carrier).
  Parameter (inv_proper: Proper (Req ==> Req) inv).

  Axiom inv_l: forall (a: Carrier), inv a <*> a ~ e.
  Axiom inv_r: forall (a: Carrier), a <*> inv a ~ e.
End GroupSig.

Module GroupTheory (Import GS: GroupSig).
  Include MonoidTheory GS.

  Theorem cancel_l (a b c: Carrier):
    c <*> a ~ c <*> b -> a ~ b.
  Proof.
    intros Hcacb.
    apply op_l with (c := inv c) in Hcacb.
    transitivity (e <*> b);
      try apply ident_l.
    transitivity (inv c <*> c <*> b).
    { transitivity (inv c <*> (c <*> b));
        try (symmetry; apply associativity).
      transitivity (inv c <*> (c <*> a));
        try assumption.
      transitivity (inv c <*> c <*> a);
        try apply associativity.
      transitivity (e <*> a);
        try (symmetry; apply ident_l).
      apply op_r;
        try reflexivity.
      symmetry.
      apply inv_l. }
    { apply op_r;
          try reflexivity.
        apply inv_l. }
  Qed.

  Theorem cancel_r (a b c: Carrier):
    a <*> c ~ b <*> c -> a ~ b.
  Proof.
    intros Hacbc.
    apply op_r with (c := inv c) in Hacbc.
    transitivity (b <*> e);
      try apply ident_r.
    transitivity (b <*> (c <*> inv c)).
    { transitivity (b <*> c <*> inv c);
        try apply associativity.
      transitivity (a <*> c <*> inv c);
        try assumption.
      transitivity (a <*> (c <*> inv c));
        try (symmetry; apply associativity).
      symmetry.
      apply op_l_solo.
      apply inv_r. }
    { apply op_l;
        try reflexivity.
      apply inv_r. }
  Qed.

  Theorem op_l_cancel_solo (a b: Carrier):
    b <*> a ~ b -> a ~ e.
  Proof.
    intros H.
    apply cancel_l with (b).
    transitivity (b);
      try assumption.
    symmetry.
    apply ident_r.
  Qed.

  Theorem op_r_cancel_solo (a b: Carrier):
    a <*> b ~ b -> a ~ e.
  Proof.
    intros H.
    apply cancel_r with (b).
    transitivity (b);
      try assumption.
    symmetry.
    apply ident_l.
  Qed.

  Theorem op_idemp_ident (a: Carrier):
    a <*> a ~ a -> a ~ e.
  Proof.
    apply op_r_cancel_solo.
  Qed.

Theorem inv_l_unique (a aInv: Carrier):
    aInv <*> a ~ e ->
    aInv ~ inv a.
  Proof.
    intros Hl.
    apply cancel_r with a.
    transitivity e;
      try assumption.
    symmetry.
    apply inv_l.
  Qed.

  Theorem inv_r_unique (a aInv: Carrier):
    a <*> aInv ~ e ->
    aInv ~ inv a.
  Proof.
    intros Hr.
    apply cancel_l with a.
    transitivity (e);
      try assumption.
    symmetry.
    apply inv_r.
  Qed.

  Theorem inv_involute (a: Carrier):
    inv (inv a) ~ a.
  Proof.
    symmetry.
    apply inv_r_unique.
    apply inv_l.
  Qed.

  Theorem inv_ident: inv e ~ e.
  Proof.
    symmetry.
    apply inv_r_unique.
    apply ident_r.
  Qed.

  Theorem inv_op (a b: Carrier):
    inv (a <*> b) ~ inv b <*> inv a.
  Proof.
    symmetry.
    apply inv_r_unique.
    transitivity (a <*> inv a);
      try apply inv_r.
    transitivity (a <*> (b <*> (inv b <*> inv a)));
      try apply associativity.
    apply op_l.
    transitivity (b <*> inv b <*> inv a);
      try (symmetry; apply associativity).
    apply op_r_solo.
    apply inv_r.
  Qed.

  Theorem solution_l (a b: Carrier):
    (exists (x: Carrier), a <*> x ~ b) /\
    (forall (x: Carrier),
      a <*> x ~ b -> x ~ inv a <*> b).
  Proof.
    split;
      [exists (inv a <*> b) | intros x Hsoln].
    { transitivity (a <*> inv a <*> b);
        try (symmetry; apply associativity).
      apply op_r_solo.
      apply inv_r. }
    { apply cancel_l with (a).
      transitivity b;
        try assumption.
      transitivity (a <*> inv a <*> b);
        try apply associativity.
      symmetry.
      apply op_r_solo.
      apply inv_r. }
  Qed.

  Theorem solution_r (a b: Carrier):
    (exists (x: Carrier), x <*> a ~ b) /\
    (forall (x: Carrier),
      x <*> a ~ b -> x ~ b <*> inv a).
  Proof.
    split;
      [exists (b <*> inv a) | intros x Hsoln].
    { transitivity (b <*> (inv a <*> a));
        try apply associativity.
      apply op_l_solo.
      apply inv_l. }
    { apply cancel_r with (a).
      transitivity (b);
        try assumption.
      symmetry.
      transitivity (b <*> e);
        try apply ident_r.
      transitivity (b <*> (inv a <*> a));
        try apply associativity.
      apply op_l.
      apply inv_l. }
  Qed.

  Section Subgroups.
  Variable (P: Carrier -> Prop).
  Variable (P_proper: Proper (Req ==> iff) P).

  Lemma subset_op_inv_closed_ident:
    (exists (x: Carrier), P x) ->
    (forall (a b: Carrier),
      P a -> P b -> P (a <*> inv b)) ->
    P e.
  Proof.
    intros [x HPx] Hop_inv.
    specialize (Hop_inv x x HPx HPx).
    assert (x <*> inv x ~ e) by apply inv_r.
    apply (P_proper _ _ H).
    assumption.
  Qed.

  Lemma subset_op_inv_closed_inv:
    (exists (x: Carrier), P x) ->
    (forall (a b: Carrier),
      P a -> P b -> P (a <*> inv b)) ->
    forall (a: Carrier), P a -> P (inv a).
  Proof.
    intros [x HPx] Hop_inv a HPa.
    assert (P e)
      as HPe
      by apply (subset_op_inv_closed_ident (ex_intro _ _ HPx) Hop_inv).
    specialize (Hop_inv e a HPe HPa).
    assert (e <*> inv a ~ inv a) by apply ident_l.
    apply (P_proper _ _ H).
    assumption.
  Qed.

  Lemma subset_op_inv_closed_op:
    (exists (x: Carrier), P x) ->
    (forall (a b: Carrier),
      P a -> P b -> P (a <*> inv b)) ->
    forall (a b: Carrier), P a -> P b -> P (a <*> b).
  Proof.
    intros Hx Hop_inv a b HPa HPb.
    assert (P (inv b)) as HPb'
      by apply (subset_op_inv_closed_inv Hx Hop_inv b HPb).
    specialize (Hop_inv a (inv b) HPa HPb').
    assert (a <*> inv (inv b) ~ a <*> b)
      by (apply op_l; apply inv_involute).
    apply (P_proper _ _ H).
    assumption.
  Qed.

  Theorem subset_op_inv_closed:
    (exists (x: Carrier), P x) ->
    (forall (a b: Carrier),
      P a -> P b -> P (a <*> inv b)) ->
    P e /\
    (forall (a: Carrier), P a -> P (inv a)) /\
    (forall (a b: Carrier),
      P a -> P b -> P (a <*> b)).
  Proof.
    intros Hx Hop_inv.
    split; [| split].
    { apply subset_op_inv_closed_ident;
        assumption. }
    { apply subset_op_inv_closed_inv;
        assumption. }
    { apply subset_op_inv_closed_op;
        assumption. }
  Qed.

  Hypothesis subgroup_op_closed:
    forall (a b: Carrier), P a -> P b -> P (a <*> b).
  Hypothesis subgroup_inv_closed:
    forall (a: Carrier), P a -> P (inv a).
  Hypothesis subgroup_ident: P e.

  Theorem subgroup_inv_inv_closed (a: Carrier):
    P (inv a) -> P a.
  Proof.
    intros HPa'.
    assert (inv (inv a) ~ a) by apply inv_involute.
    apply P_proper in H.
    apply H.
    apply subgroup_inv_closed.
    assumption.
  Qed.

  Definition right_congru (a b: Carrier) :=
    P (a <*> (inv b)).
  Definition left_congru (a b: Carrier) :=
    P ((inv a) <*> b).

  Theorem right_congru_proper:
    Proper (Req ==> Req ==> iff) right_congru.
  Proof.
    intros a0 a1 Ha b0 b1 Hb.
    unfold right_congru.
    apply P_proper.
    apply op_proper;
      [assumption |].
    apply inv_proper.
    assumption.
  Qed.

  Theorem left_congru_proper:
    Proper (Req ==> Req ==> iff) left_congru.
  Proof.
    intros a0 a1 Ha b0 b1 Hb.
    unfold left_congru.
    apply P_proper.
    apply op_proper;
      [| assumption].
    apply inv_proper.
    assumption.
  Qed.

  Theorem right_congru_reflexive (a: Carrier):
    right_congru a a.
  Proof.
    unfold right_congru.
    apply (P_proper (a <*> (inv a)) e (inv_r a)).
    apply subgroup_ident.
  Qed.

  Theorem left_congru_reflexive (a: Carrier):
    left_congru a a.
  Proof.
    unfold left_congru.
    apply (P_proper ((inv a) <*> a) e (inv_l a)).
    apply subgroup_ident.
  Qed.

  Theorem right_congru_symmetric (a b: Carrier):
    right_congru a b -> right_congru b a.
  Proof.
    unfold right_congru;
      intros HPab.
    assert (inv (a <*> inv b) ~ b <*> inv a) as Hab'.
    { transitivity (inv (inv b) <*> inv a);
        [apply inv_op |].
      apply op_r.
      apply inv_involute. }
    { apply (P_proper (inv (a <*> inv b)) (b <*> inv a) Hab').
      apply subgroup_inv_closed.
      assumption. }
  Qed.

  Theorem left_congru_symmetric (a b: Carrier):
    left_congru a b -> left_congru b a.
  Proof.
    unfold left_congru;
      intros HPab.
    assert (inv (inv a <*> b) ~ inv b <*> a) as Ha'b.
    { transitivity (inv b <*> inv (inv a));
        [apply inv_op |].
      apply op_l.
      apply inv_involute. }
    { apply (P_proper (inv (inv a <*> b)) (inv b <*> a) Ha'b).
      apply subgroup_inv_closed.
      assumption. }
  Qed.

  Theorem right_congru_transitive (a b c: Carrier):
    right_congru a b -> right_congru b c ->
    right_congru a c.
  Proof.
    unfold right_congru.
    intros HPab HPbc.
    assert ((a <*> inv b) <*> (b <*> inv c) ~ a <*> inv c)
      as Hac'.
    { transitivity (a <*> (inv b <*> (b <*> inv c)));
        [apply associativity |].
      apply op_l.
      transitivity (inv b <*> b <*> inv c);
        [symmetry; apply associativity |].
      apply op_r_solo.
      apply inv_l. }
    { apply (P_proper _ _ Hac').
      apply subgroup_op_closed;
        assumption. }
  Qed.

  Theorem left_congru_transitive (a b c: Carrier):
    left_congru a b -> left_congru b c ->
    left_congru a c.
  Proof.
    unfold left_congru.
    intros HPab Hbc.
    assert ((inv a <*> b) <*> (inv b <*> c) ~ inv a <*> c)
      as Hb'c.
    { transitivity (inv a <*> (b <*> (inv b <*> c)));
        [apply associativity |].
      apply op_l.
      transitivity (b <*> inv b <*> c);
        [symmetry; apply associativity |].
      apply op_r_solo.
      apply inv_r. }
    { apply (P_proper _ _ Hb'c).
      apply subgroup_op_closed;
        assumption. }
  Qed.

  #[local]
  Instance right_congru_equiv: Equivalence right_congru := {
    Equivalence_Reflexive := right_congru_reflexive;
    Equivalence_Symmetric := right_congru_symmetric;
    Equivalence_Transitive := right_congru_transitive;
  }.

  #[local]
  Instance left_congru_equiv: Equivalence left_congru := {
    Equivalence_Reflexive := left_congru_reflexive;
    Equivalence_Symmetric := left_congru_symmetric;
    Equivalence_Transitive := left_congru_transitive;
  }.

  Definition right_cosets_eq (a b: Carrier) :=
    forall (m: Carrier),
      P m ->
      exists (n: Carrier), P n /\ m <*> a ~ n <*> b.
  Theorem right_cosets_eq_congru (a b: Carrier):
    right_cosets_eq a b <->
    right_congru a b.
  Proof.
    unfold right_cosets_eq, right_congru.
    split;
      [intros Hcosets | intros Hcongru].
    { specialize (Hcosets e subgroup_ident).
      inversion_clear Hcosets as [n [HPn Hrcoset]].
      assert (a <*> inv b ~ n) as H;
        [| apply (P_proper _ _ H); assumption].
      apply cancel_r with (c := b).
      transitivity (a <*> (inv b <*> b));
        [apply associativity |].
      transitivity (a <*> e);
        [apply op_l; apply inv_l |].
      transitivity a;
        [apply ident_r |].
      transitivity (e <*> a);
        [symmetry; apply ident_l | assumption]. }
    { intros m HPm.
      exists (m <*> (a <*> inv b)).
      split;
        [apply subgroup_op_closed; assumption |].
      transitivity (m <*> a <*> inv b <*> b);
        [| apply op_r; apply associativity].
      symmetry.
      transitivity (m <*> a <*> (inv b <*> b));
        [apply associativity |].
      apply op_l_solo.
      apply inv_l. }
  Qed.

  Definition left_cosets_eq (a b: Carrier) :=
    forall (m: Carrier),
      P m ->
      exists (n: Carrier), P n /\ a <*> m ~ b <*> n.
  Theorem left_cosets_eq_congru (a b: Carrier):
    left_cosets_eq a b <->
    left_congru a b.
  Proof.
    unfold left_cosets_eq, left_congru.
    split;
      [intros H | intros HPa'b].
    { specialize (H e subgroup_ident).
      inversion_clear H as [n [HPn Hlcoset]].
      assert (inv a <*> b ~ inv n);
        [| apply (P_proper _ _ H);
            apply subgroup_inv_closed;
            assumption].
      apply cancel_r with (c := n).
      transitivity e;
        [| symmetry; apply inv_l].
      apply cancel_l with (c := a).
      transitivity (a <*> (inv a <*> b) <*> n);
        [symmetry; apply associativity |].
      transitivity (a <*> inv a <*> b <*> n);
        [symmetry; apply op_r; apply associativity |].
      transitivity (e <*> b <*> n);
        [apply op_r; apply op_r; apply inv_r |].
      transitivity (b <*> n);
        [apply op_r; apply ident_l |].
      symmetry.
      assumption. }
    { intros m HPm.
      exists (inv b <*> a <*> m).
      split.
      { apply subgroup_op_closed;
          [| assumption].
        apply subgroup_inv_closed in HPa'b.
        assert (inv (inv a <*> b) ~ inv b <*> a).
        { transitivity (inv b <*> inv (inv a));
            [apply inv_op |].
          apply op_l.
          apply inv_involute. }
        { apply P_proper in H.
          apply H.
          assumption. } }
      { transitivity (b <*> (inv b <*> a) <*> m);
          [| apply associativity].
        apply op_r.
        transitivity (b <*> inv b <*> a);
          [| apply associativity].
        symmetry.
        apply op_r_solo.
        apply inv_r. } }
  Qed.

  Let normal_subgroup_congru_coincide: Prop := (* 1 *)
    forall (a b: Carrier), left_congru a b <-> right_congru a b.
  Let normal_subgroup_coset_eq_coincide: Prop := (* 2 *)
    forall (a b: Carrier), left_cosets_eq a b <-> right_cosets_eq a b.
  Let normal_subgroup_cosets_coincide: Prop :=
    forall (m: Carrier), (* 3 *)
      P m ->
      (forall (a: Carrier), exists (n: Carrier), P n /\ a <*> m ~ n <*> a).
  Let normal_subgroup_conj_closed: Prop := (* 4 *)
    forall (n: Carrier), P n -> forall (a: Carrier), P (a <*> n <*> inv a).
  Let normal_subgroup_conj_closed_exact: Prop := (* 5 *)
    forall (n: Carrier), P n <-> forall (a: Carrier), P (a <*> n <*> inv a).

  (* equiv 1 & 2 *)
  Theorem normal_subgroup_equiv_congru_coset_eq:
    normal_subgroup_congru_coincide <->
    normal_subgroup_coset_eq_coincide.
  Proof.
    unfold normal_subgroup_congru_coincide,
      normal_subgroup_coset_eq_coincide.
    split;
      [intros Hcongru | intros Hcoset].
    { intros a b.
      split;
        [intros Hlcoset | intros Hrcoset].
      { apply right_cosets_eq_congru.
        apply Hcongru.
        apply left_cosets_eq_congru.
        assumption. }
      { apply left_cosets_eq_congru.
        apply Hcongru.
        apply right_cosets_eq_congru.
        assumption. } }
    { intros a b.
      split;
        [intros Hlcongru | intros Hrcongru].
      { apply right_cosets_eq_congru.
        apply Hcoset.
        apply left_cosets_eq_congru.
        assumption. }
      { apply left_cosets_eq_congru.
        apply Hcoset.
        apply right_cosets_eq_congru.
        assumption. } }
  Qed.

  (* equiv 3 & 4 *)
  Theorem normal_subgroup_equiv_cosets_conj:
    normal_subgroup_cosets_coincide <->
    normal_subgroup_conj_closed.
  Proof.
    unfold normal_subgroup_conj_closed_exact,
      normal_subgroup_cosets_coincide.
    split;
      [intros Hcosets | intros Hconj].
    { intros n.
      intros HPn a.
      specialize (Hcosets n HPn a).
      inversion_clear Hcosets as [m [HPm H]].
      assert (a <*> n <*> inv a ~ m).
      { apply cancel_r with (c := a).
        transitivity (a <*> n <*> (inv a <*> a));
          [apply associativity |].
        transitivity (a <*> n <*> e);
          [ apply op_l; apply inv_l |].
        transitivity (a <*> n);
          [ apply ident_r | assumption]. }
      apply (P_proper _ _ H0).
      assumption. }
    { intros m HPm a.
      exists (a <*> m <*> inv a).
      split;
        [apply (Hconj m); assumption |].
      transitivity (a <*> m <*> (inv a <*> a));
        [| symmetry; apply associativity].
      symmetry.
      apply op_l_solo.
      apply inv_l. }
  Qed.

  (* equiv 4 & 5 *)
  Theorem normal_subgroup_equiv_conj_closed:
    normal_subgroup_conj_closed <->
    normal_subgroup_conj_closed_exact.
  Proof.
    unfold normal_subgroup_conj_closed,
      normal_subgroup_conj_closed_exact.
    split;
      [intros Himpl n | intros H n HPn; apply H; assumption].
    split;
      [apply Himpl | intros Hconj].
    specialize (Hconj e).
    apply (P_proper n (e <*> n <*> inv e));
      [| assumption].
    transitivity (e <*> n <*> e);
      [| apply op_l; symmetry; apply inv_ident].
    transitivity (e <*> n);
      symmetry;
      [apply ident_l | apply ident_r ].
  Qed.

  (* equiv 1 & 4 *)
  Theorem normal_subgroup_equiv_congru_conj:
    normal_subgroup_congru_coincide <->
    normal_subgroup_conj_closed.
  Proof.
    unfold normal_subgroup_congru_coincide, left_congru,
      right_congru, normal_subgroup_cosets_coincide.
    split;
      [intros Hcongru | intros Hcosets].
    { unfold normal_subgroup_conj_closed.
      intros n HPn a.
      assert (a <*> n <*> inv a ~ a <*> inv (a <*> inv n)).
      { transitivity (a <*> (n <*> inv a));
          [apply associativity |].
        apply op_l.
        symmetry.
        transitivity (inv (inv n) <*> inv a);
          [apply inv_op |].
        apply op_r.
        apply inv_involute. }
      { apply (P_proper _ _ H); clear H.
        apply Hcongru.
        assert (inv a <*> (a <*> inv n) ~ inv n).
        { transitivity (inv a <*> a <*> inv n);
            [symmetry; apply associativity |].
          apply op_r_solo.
          apply inv_l. }
        { apply (P_proper _ _ H); clear H.
          apply subgroup_inv_closed.
          assumption. } } }
    { intros a b.
      unfold normal_subgroup_conj_closed in Hcosets.
      split;
        [intros Ha'b | intros Hab'].
      { assert (P (inv a <*> b) -> (forall (c: Carrier), P (c <*> (inv a <*> b) <*> inv c)))
          by apply Hcosets.
        specialize (H Ha'b); clear Ha'b.
        specialize (H b).
        assert (b <*> (inv a <*> b) <*> inv b ~ inv (a <*> inv b)).
        { transitivity (b <*> inv a <*> b <*> inv b);
            [apply op_r; symmetry; apply associativity |].
          transitivity (b <*> inv a <*> (b <*> inv b));
            [apply associativity |].
          transitivity (b <*> inv a <*> e);
            [apply op_l; apply inv_r |].
          transitivity (b <*> inv a);
            [apply ident_r |].
          symmetry.
          transitivity (inv (inv b) <*> inv a);
            [apply inv_op |].
          apply op_r.
          apply inv_involute. }
        { apply subgroup_inv_inv_closed.
          apply (P_proper _ _ H0).
          assumption. } }
      { specialize (Hcosets (a <*> inv b)).
        specialize (Hcosets Hab' (inv b)).
        assert (inv b <*> (a <*> inv b) <*> inv (inv b) ~ inv (inv a <*> b)).
        { transitivity (inv b <*> a <*> inv b <*> inv (inv b));
            [symmetry; apply op_r; apply associativity |].
          transitivity (inv b <*> a <*> (inv b <*> inv (inv b)));
            [apply associativity |].
          transitivity (inv b <*> inv (inv a));
            [| symmetry; apply inv_op].
          transitivity (inv b <*> a);
            [| apply op_l; symmetry; apply inv_involute].
          apply op_l_solo.
          apply inv_r. }
        { apply subgroup_inv_inv_closed.
          apply (P_proper _ _ H).
          assumption. } } }
  Qed.

  (* equiv 1 & 3 *)
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

  (* equiv 1 & 5 *)
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

  (* equiv 2 & 3 *)
  Corollary normal_subgroup_equiv_coset_eq_cosets:
    normal_subgroup_coset_eq_coincide <->
    normal_subgroup_cosets_coincide.
  Proof.
    split;
      [intros Hcoset_eq | intros Hcosets].
    { apply normal_subgroup_equiv_congru_cosets.
      apply normal_subgroup_equiv_congru_coset_eq.
      assumption. }
    { apply normal_subgroup_equiv_congru_coset_eq.
      apply normal_subgroup_equiv_congru_cosets.
      assumption. }
  Qed.

  (* equiv 2 & 4 *)
  Corollary normal_subgroup_equiv_coset_eq_conj:
    normal_subgroup_coset_eq_coincide <->
    normal_subgroup_conj_closed.
  Proof.
    split;
      [intros Hcoset_eq | intros Hconj].
    { apply normal_subgroup_equiv_congru_conj.
      apply normal_subgroup_equiv_congru_coset_eq.
      assumption. }
    { apply normal_subgroup_equiv_congru_coset_eq.
      apply normal_subgroup_equiv_congru_conj.
      assumption. }
  Qed.

  (* equiv 2 & 5 *)
  Corollary normal_subgroup_equiv_coset_eq_conj_exact:
    normal_subgroup_coset_eq_coincide <->
    normal_subgroup_conj_closed_exact.
  Proof.
    split;
      [intros Hcoset_eq | intros Hconj_exact].
    { apply normal_subgroup_equiv_conj_closed.
      apply normal_subgroup_equiv_coset_eq_conj.
      assumption. }
    { apply normal_subgroup_equiv_coset_eq_conj.
      apply normal_subgroup_equiv_conj_closed.
      assumption. }
  Qed.

  (* equiv 3 & 5 *)
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
  End Subgroups.
End GroupTheory.
