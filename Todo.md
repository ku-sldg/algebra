1. Zorn's lemma for ideals yielding a maximal ideal.
   * Family of ideals `\(\left(I_{\alpha}\right)_{\alpha}\)`:
     `I: Index -> Carrier -> Prop`.
   * every chain (`forall (P: Index -> Prop)(i0 i1: Index), P i0 -> P i1 -> I i0 ~<~ I i1 \/ I i1 ~<~ I i0`)
     has an upper bound (`exists (iup: Index), forall (i: Index), P i -> I i ~<~ I iup`).
   * then there is a maximal ideal.
1. `\(x\)` in a maximal ideal implies `\(1 - x\)` is a unit.
