Require Import Coq.Vectors.Vector.
Require Import Coq.Program.Equality.

Theorem vector_forall_append {A: Type}(P: A -> Prop):
  forall (m n: nat)(u: t A m)(v: t A n),
    Forall P (append u v) <->
    Forall P u /\ Forall P v.
Proof.
  intros m n u.
  generalize dependent n.
  induction u as [| x m u];
    simpl;
    intros n v;
    split.
  { intros Hv;
      split;
      [constructor | assumption]. }
  { intros [Hnil Hv];
      assumption. }
  { intros Happ.
    inversion Happ.
    inversion_sigma.
    subst.
    split.
    { constructor;
        [assumption |].
      let H := match goal with H : m + n = m + n |- _ => H end in
        pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
      simpl in H5.
      subst.
      apply IHu in H3.
      inversion_clear H3 as [Hu Hv].
      assumption. }
    { let H := match goal with H : m + n = m + n |- _ => H end in
        pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
      simpl in H5.
      subst.
      apply IHu in H3.
      inversion_clear H3 as [Hu Hv].
      assumption. } }
  { intros [Hxu Hv].
    inversion Hxu;
      subst.
    inversion_sigma.
    let H := match goal with H : m = m |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
    simpl in H4.
    subst.
    constructor;
      [assumption |].
    apply IHu.
    split;
      assumption. }
Qed.

Definition vector_ind2 {A B: Type}(P: forall {n}, t A n -> t B n -> Prop)
    (base: P (nil A) (nil B))(ind: forall {n v1 v2}, P v1 v2 -> forall a b, P (cons A a _ v1) (cons B b _ v2)) :=
  fix vector_ind2_fix {n} (v1: t A n): forall (v2: t B n), P v1 v2 :=
    match v1 with
    | nil _ => fun v2 => case0 _ base v2
    | @cons _ hd1 n' tl1 =>
      fun v2 =>
        caseS' v2 (fun v2' => P (cons A hd1 _ tl1) v2')
          (fun hd2 tl2 => ind (vector_ind2_fix tl1 tl2) hd1 hd2)
    end.

Theorem vector_fold_right2_append {A B C: Type}(g: A -> B -> C -> C)(c: C):
  forall {n: nat}(u2: t A n)(v2: t B n){m: nat}(u1: t A m)(v1: t B m),
    fold_right2 g c _ (append u1 u2) (append v1 v2) =
      fold_right2 g (fold_right2 g c _ u2 v2) _ u1 v1.
Proof.
  intros n u2 v2.
  apply vector_ind2;
    simpl;
    [reflexivity |].
  intros m u1 v1 IH.
  intros a b.
  rewrite IH.
  reflexivity.
Qed.

Lemma vector_forall_map {A: Type}(P: A -> Prop)(f: A -> A):
  (forall (a: A), P a -> P (f a)) ->
  forall {n: nat}(v: t A n),
    Forall P v ->
    Forall P (map f v).
Proof.
  intros Hclosed n.
  induction v;
    simpl.
  { constructor. }
  { intros Hcons.
    inversion Hcons.
    subst.
    inversion_sigma.
    let H := match goal with H: n = n |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
    simpl in H4.
    subst.
    constructor.
    { apply Hclosed.
      assumption. }
    { apply IHv.
      assumption. } }
Qed.

Lemma vector_forall_map_spec {A B: Type}(P: B -> Prop)(f: A -> B):
  (forall (a: A), P (f a)) ->
  forall {n: nat}(v: t A n),
    Forall P (map f v).
Proof.
  intros Hspec.
  intros n.
  induction v as [| a n v];
    simpl;
    constructor.
  { apply Hspec. }  
  { assumption. }
Qed.

Fixpoint const_seq {A: Type}(a: A)(n: nat): t A n :=
  match n with
  | 0 => nil A
  | S n' => cons _ a _ (const_seq a n')
  end.

Lemma vector_forall_const_seq {A: Type}(a: A){n: nat}(P: A -> Prop):
  Forall P (const_seq a n) <-> n = 0 \/ P a.
Proof.
  split;
    [intros Hforall |].
  { destruct n as [| n'].
    { left; reflexivity. }
    { right.
      simpl in Hforall.
      inversion_clear Hforall.
      assumption. } }
  { induction n as [| n'].
    { left; reflexivity. }
    { simpl.
      intros [Hcontra | Ha];
        [inversion Hcontra |].
      constructor;
        [assumption |].
      apply IHn'.
      right.
      assumption. } }
Qed.

Definition zipWith {A B C: Type}(f: A -> B -> C){n: nat}(u: t A n)(v: t B n): t C n :=
  rect2 (fun n _ _ => t C n) (nil C)
    (fun n _ _ accum a b => cons C (f a b) n accum) u v.

Theorem vector_forall_zipwith_binary_op {A: Type}(f: A -> A -> A)(P: A -> Prop):
  (forall (a0 a1: A), P a0 -> P a1 -> P (f a0 a1)) ->
  forall {n: nat}(v0: t A n)(v1: t A n),
    Forall P v0 -> Forall P v1 ->
    Forall P (zipWith f v0 v1).
Proof.
  intros Hclosed n v0 v1.
  induction v0 as [| a0 n v0].
  { dependent destruction v1.
    intros _ _.
    simpl.
    constructor. }
  { dependent destruction v1.
    rename h into a1.
    intros Hv0 Hv1.
    simpl.
    inversion Hv0.
    subst.
    inversion_sigma.
    let H := match goal with H: n = n |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
    simpl in H4.
    subst v.
    inversion Hv1.
    subst.
    inversion_sigma.
    let H := match goal with H: n = n |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
    simpl in H6.
    subst v.
    constructor.
    { apply Hclosed;
        assumption. }
    { apply IHv0;
        assumption. } }
Qed.

Theorem vector_map_composed {A B C: Type}(f: A -> B)(g: B -> C):
  forall {n: nat}(v: t A n),
    map (fun x => g (f x)) v =
      map g (map f v).
Proof.
  intros n.
  induction v;
    simpl;
    [| rewrite IHv];
    reflexivity.
Qed.
