Require Import Coq.Relations.Relations.
From Coq.Classes Require Import RelationClasses Morphisms.
From algebra Require Import Semigroups Monoids Groups AbelianGroups CommRings Modules Vectors.
Require Import Coq.Vectors.Vector.
Require Import Coq.Program.Equality.

Section NakayamaLemma.
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
Context (P: R -> Prop).
Context {P_proper: Proper (Requiv ==> iff) P}.
Context {P_ideal: Ideal Radd Rzero Rminus Rmul P}.
Context {P_maxideal: maximal_ideal Requiv Radd Rzero Rminus Rmul P}.
Context {R_local: local_ring Requiv Radd Rzero Rminus Rmul}.

Let ideal_module_pred := ideal_module Mequiv Madd Mzero action P.

Lemma module_fin_gen_ideal_module:
  forall {n: nat}(basis: t M n),
    finitely_generated Mequiv Madd Mzero action basis ->
    forall {m: nat}(coeffs: t R m)(vectors: t M m),
      Forall P coeffs ->
      exists (coeffs': t R n),
        linear_combin Madd Mzero action coeffs vectors =M=
          linear_combin Madd Mzero action coeffs' basis /\
        Forall P coeffs'.
Proof.
  intros n basis M_fingen m coeffs vectors.
  induction vectors as [| vector m vectors].
  { dependent destruction coeffs.
    simpl.
    intros Hcoeffs.
    exists (const_seq Rzero n).
    setoid_rewrite (module_linear_combin_0_l Requiv Radd Rzero Rminus Rmul Rone Mequiv Madd Mzero Mminus action).
    split;
      [reflexivity |].
    apply vector_forall_const_seq.
    right.
    apply (subgroup_ident Radd Rzero Rminus P). }
  { dependent destruction coeffs.
    rename h into coeff.
    intros Hcoeffs.
    inversion Hcoeffs.
    subst.
    inversion_sigma.
    let H := match goal with H: m = m |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
    simpl in H4.
    subst.
    specialize (IHvectors coeffs H3).
    inversion_clear IHvectors as [coeffs' [Hlincomb Hcoeffs']].
    pose proof (M_fingen vector) as H4.
    inversion_clear H4 as [coeffs'' Hvector].
    exists (zipWith Radd coeffs' (map (Rmul coeff) coeffs'')).
    (* coeffs . vectors = coeffs' . basis
     * coeff * vector + coeffs . vectors
     *   = coeff * (coeffs'' . basis) + coeffs' . basis
     *   = (coeff * coeffs'' + coeffs') . basis
     *)
    split.
    { simpl.
      setoid_rewrite (module_linear_combin_zipWith_add_l Radd Rmul Rone Mequiv Madd Mzero Mminus action).
      setoid_rewrite Hlincomb.
      apply (semigroup_op_l Mequiv Madd).
      setoid_rewrite (module_linear_combin_mul_l Requiv Radd Rmul Rone Mequiv Madd Mzero Mminus action).
      setoid_rewrite Hvector.
      reflexivity. }
    { apply vector_forall_zipwith_binary_op.
      { apply (subgroup_op_closed Radd Rzero Rminus P). }
      { assumption. }
      { apply vector_forall_map_spec.
        apply (ideal_mul_absorb_r Requiv Radd Rzero Rminus Rmul Rone P).
        assumption. } } }
Qed.

Theorem nakayama:
  forall {n: nat}(basis: t M n),
    finitely_generated Mequiv Madd Mzero action basis ->
  (forall a: M, ideal_module_pred a) ->
  forall a: M, a =M= Mzero.
Proof.
  intros n.
  induction basis as [| u1 n basis'];
    intros M_fingen Hideal_mod.
  { intros a.
    specialize (M_fingen a).
    inversion_clear M_fingen as [coeffs Ha].
    dependent destruction coeffs.
    simpl in Ha.
    assumption. }
  { apply IHbasis';
      [| assumption].
    intros u.
    specialize (Hideal_mod u1).
    inversion_clear Hideal_mod as [m [coeffs_u [vectors_u [Hcoeffs_u Hu]]]].
    pose proof (module_fin_gen_ideal_module (cons M u1 n basis') M_fingen coeffs_u vectors_u Hcoeffs_u).

(* 
  induction basis as [| u1 n basis'];
    intros Hideal_mod.
  { intros a.
    specialize (M_fingen a).
    inversion_clear M_fingen as [coeffs H].
    dependent destruction coeffs.
    simpl in H.
    assumption. }
  { specialize (IHbasis' basis').
    pose proof (Hideal_mod u1) as Hu1.
    inversion_clear Hu1 as [m [coeffs_u1 [vectors_u1 [Hcoeffs_u1 _]]]].
    pose proof (module_fin_gen_ideal_module coeffs_u1 vectors_u1 Hcoeffs_u1).
    dependent destruction coeffs.
    rename h into x1, coeffs into coeffs'.
    simpl in Hu1'.
    assert ((Rone [+] Rminus x1) <.> u1 =M= linear_combin Madd Mzero action coeffs' t).
 *)
Admitted.
End NakayamaLemma.
