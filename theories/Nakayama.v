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

(* For finitely generated module \(M\) with generating set
  \(generatingSet\) and an ideal \(P\), any element of
  \(P M\) can be written as a linear combination of
  the generatingSet and coefficients from \(P\).
 *)
Lemma module_fin_gen_ideal_module:
  forall {n: nat}(generatingSet: t M n),
    finitely_generated Mequiv Madd Mzero action generatingSet ->
    forall {m: nat}(coeffs: t R m)(elts: t M m),
      Forall P coeffs ->
      exists (coeffs': t R n),
        linear_combin Madd Mzero action coeffs elts =M=
          linear_combin Madd Mzero action coeffs' generatingSet /\
        Forall P coeffs'.
Proof.
  intros n generatingSet M_fingen m coeffs elts.
  induction elts as [| elt m elts].
  { (* elts := nil *)
    dependent destruction coeffs.
    (* so coeffs = nil *)
    simpl.
    intros Hcoeffs.
    (* coeffs' is a list of \(n\) zeros *)
    exists (const_seq Rzero n).
    setoid_rewrite
      (module_linear_combin_0_l Requiv Radd Rzero Rminus Rmul Rone
        Mequiv Madd Mzero Mminus action).
    split;
      [reflexivity |].
    (* Forall P (const_seq Rzero n) -> P RZero -> True *)
    apply vector_forall_const_seq.
    right.
    apply (subgroup_ident Radd Rzero Rminus P). }
  { (* elts := cons elt elts *)
    (* `coeffs: t R (S m)` breaks up into `cons coeff coeffs` *)
    dependent destruction coeffs.
    rename h into coeff.
    intros Hcoeffs.
    (* induction hypothesis applies to `coeffs . elts` 
       so `coeffs . elts = coeffs' . generatingSet` *)
    inversion Hcoeffs.
    subst.
    inversion_sigma.
    let H := match goal with H: m = m |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H;
      simpl in *; subst.
    specialize (IHelts coeffs H3).
    inversion_clear IHelts as [coeffs' [Hlincomb Hcoeffs']].
    (* elt = linear_combin coeffs'' generatingSet *)
    pose proof (M_fingen elt) as H4.
    inversion_clear H4 as [coeffs'' Helt].
    exists (zipWith Radd coeffs' (map (Rmul coeff) coeffs'')).
    (* coeff * elt + coeffs . elts
     *   = coeff * (coeffs'' . generatingSet) + coeffs' . generatingSet
     *   = (coeff * coeffs'' + coeffs') . generatingSet
     *)
    split.
    { simpl.
      setoid_rewrite (module_linear_combin_zipWith_add_l Radd Rmul Rone
        Mequiv Madd Mzero Mminus action).
      setoid_rewrite Hlincomb.
      apply (semigroup_op_l Mequiv Madd).
      setoid_rewrite (module_linear_combin_mul_l Requiv Radd Rmul Rone
        Mequiv Madd Mzero Mminus action).
      setoid_rewrite Helt.
      reflexivity. }
    (* proving the coefficients belong to the ideal *)
    { apply vector_forall_zipwith_binary_op.
      { apply (subgroup_op_closed Radd Rzero Rminus P). }
      { assumption. }
      { apply vector_forall_map_spec.
        apply (ideal_mul_absorb_r Requiv Radd Rzero Rminus Rmul Rone P).
        assumption. } } }
Qed.

Theorem nakayama:
  forall {n: nat}(generatingSet: t M n),
    finitely_generated Mequiv Madd Mzero action generatingSet ->
  (forall a: M, ideal_module_pred a) ->
  forall a: M, a =M= Mzero.
Proof.
  intros n.
  induction generatingSet as [| u1 n generatingSet'];
    intros M_fingen Hideal_mod.
  { (* Base case: generatingSet is empty, module is zero *)
    intros a.
    specialize (M_fingen a).
    inversion_clear M_fingen as [coeffs Ha].
    dependent destruction coeffs.
    simpl in Ha.
    assumption. }
  { (* Ind case: generatingSet = u1::generatingSet' *)
    apply IHgeneratingSet'; (* apply induction hypothesis *)
      [| assumption].
    (* u1 = x1 u1 + coeffs' . generatingSet' *)
    specialize (Hideal_mod u1).
    inversion_clear Hideal_mod as [m [coeffs_u [elts_u [Hcoeffs_u Hu1]]]].
    pose proof
      (module_fin_gen_ideal_module
        (cons M u1 n generatingSet')
        M_fingen
        coeffs_u
        elts_u
        Hcoeffs_u).
    inversion_clear H as [coeffs' [Hu1_genSet Hcoeffs']].
    setoid_rewrite Hu1_genSet in Hu1.
    dependent destruction coeffs'.
    rename h into x1.
    simpl in Hu1.
    (* (1 - x1) u1 = coeffs' . generatingSet' *)
    assert ((Rone [+] Rminus x1) <.> u1 =M=
      linear_combin Madd Mzero action coeffs' generatingSet').
    { setoid_rewrite (module_distrib_Radd Radd Rmul Rone
        Mequiv Madd Mzero Mminus action).
      setoid_rewrite (module_Rone Radd Rmul Rone
        Mequiv Madd Mzero Mminus action).
      setoid_rewrite (module_minus_l Requiv Radd Rzero Rminus Rmul Rone
        Mequiv Madd Mzero Mminus action).
      symmetry.
      apply (group_move_r Mequiv Madd Mzero Mminus).
      symmetry.
      assumption. }
    (* x1 is in the maximal ideal *)    
    inversion Hcoeffs';
      subst.
    inversion_sigma.
    let H := match goal with H: n = n |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H;
      simpl in *; subst v.
    (* x1 cannot be a unit *)
    pose proof
      (comm_ring_maximal_ideal_nonunits Requiv Radd Rzero Rminus Rmul Rone
        P P_maxideal x1 H3) as Hx1_nonunit.
    (* 1 - x1 must be a unit with y as its inverse *)
    pose proof
      (local_comm_ring_sub_1_nonunit Requiv Radd Rzero Rminus Rmul Rone R_local
        x1 Hx1_nonunit) as H1mx1_unit.
    (* u1 = (y coeffs') . generatingSet *)
    inversion_clear H1mx1_unit as [y Hy].
    setoid_rewrite (commutative Requiv Rmul) in Hy.
    apply (module_op_l Requiv Mequiv action) with (r:=y) in H.
    setoid_rewrite <- (module_distrib_Rmul Radd Rmul Rone
      Mequiv Madd Mzero Mminus action) in H.
    setoid_rewrite Hy in H.
    setoid_rewrite (module_Rone Radd Rmul Rone
      Mequiv Madd Mzero Mminus action) in H.
    setoid_rewrite <- (module_linear_combin_mul_l Requiv Radd Rmul Rone
      Mequiv Madd Mzero Mminus action) in H.
    (* v = v1 u1 + coeffs_v . generatingSet'
     *   = v1 (y coeffs' . generatingSet') + coeffs_v . generatingSet'
     *   = (v1 y coeffs' + coeffs_v) . generatingSet'
     *)
    intros v.
    pose proof (M_fingen v) as Hv.
    inversion_clear Hv as [coeffs_v Hcoeffs_v].
    dependent destruction coeffs_v.
    rename h into v1.
    simpl in Hcoeffs_v.
    setoid_rewrite H in Hcoeffs_v.
    setoid_rewrite <- (module_linear_combin_mul_l Requiv Radd Rmul Rone
      Mequiv Madd Mzero Mminus action) in Hcoeffs_v.
    rewrite <- vector_map_composed in Hcoeffs_v.
    setoid_rewrite <- (module_linear_combin_zipWith_add_l Radd Rmul Rone
      Mequiv Madd Mzero Mminus action) in Hcoeffs_v.
    exists (zipWith Radd coeffs_v
      (map (fun x : R => v1 [*] (y [*] x)) coeffs')).
    assumption. }
Qed.
End NakayamaLemma.
(* Print Assumptions nakayama. *)
