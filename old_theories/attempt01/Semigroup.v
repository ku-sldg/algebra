Section Semigroups.
Context {G: Set}(mult: G -> G -> G).

Class Semigroup := {
  semigroup_assoc: forall (a b c: G), mult (mult a b) c = mult a (mult b c);
}.

Context `{Gsemigroup: Semigroup}.

Lemma semigroup_left_mult (a b: G):
  a = b -> forall (c: G), mult c a = mult c b.
Proof.
  intros <-;
    reflexivity.
Qed.

Lemma semigroup_right_mult (a b: G):
  a = b -> forall (c: G), mult a c = mult b c.
Proof.
  intros <-;
    reflexivity.
Qed.

Class Commutative := {
    commutative: forall (a b: G), mult a b = mult b a;
}.
End Semigroups.
