Require Import Algebra.AbelianGroup.
Require Import Algebra.CommRing.

Section Modules.
Context {R: Set}(plusR: R -> R -> R)(zeroR: R)(minusR: R -> R).
Context (multR: R -> R -> R)(oneR: R).
Context `{Rcring: CommRing R plusR zeroR minusR multR oneR}.
Context {A: Set}(plusA: A -> A -> A)(zeroA: A)(minusA: A -> A).
Context `{Aagroup: AbelianGroup A plusA zeroA minusA}.
Context (action: R -> A -> A).

Class Module_ := {
  module_distrib_plusA: forall (r: R)(a b: A), action r (plusA a b) = plusA (action r a) (action r b);
  module_distrib_plusR: forall (r s: R)(a: A), action (plusR r s) a = plusA (action r a) (action s a);
  module_distrib_multR: forall (r s: R)(a: A), action (multR r s) a = action r (action s a);
  module_oneR: forall (a: A), action oneR a = a;
}.

Context `{ARmodule: Module_}.

Theorem module_zeroR (a: A):
  action zeroR a = zeroA.
Proof.
  cut (plusA (action zeroR a) (action zeroR a) = action zeroR a).
  { intros H.
    apply (agroup_idemp_zero plusA zeroA minusA).
    assumption. }
  { rewrite <- module_distrib_plusR.
    rewrite (cring_plus_ident plusR zeroR minusR multR oneR).
    reflexivity. }
Qed.

Theorem module_zeroA (r: R):
  action r zeroA = zeroA.
Proof.
  cut (plusA (action r zeroA) (action r zeroA) = action r zeroA).
  { intros H.
    apply (agroup_idemp_zero plusA zeroA minusA).
    assumption. }
  { rewrite <- module_distrib_plusA.
    rewrite (agroup_ident plusA zeroA minusA).
    reflexivity. }
Qed.
End Modules.
