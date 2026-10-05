/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricFiniteExtraction
import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedRestrictionCut
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizationPower

set_option autoImplicit false

/-!
# `sym₃` of the `alphatilde`-typed `112` cut meets the committed symmetric ambient power

Layer 4 (`AlgebraicComplexity/Examples/`).  This is the tensor-level meeting point of the two halves
of the `T_{1,1,2}` value argument: the leaf's typed cut on one side, and the object the committed
value certificate is attached to on the other.

## The paper step

`[duan2023faster]`, `second_power_appendix.tex:26-45`, proof of `lem:non-rot-values` (d):

> *Let `\T` be the tensor obtained from `T_{1,1,2}^{⊗m}` by zeroing out all blocks inconsistent
> with the marginal distributions of `α^{(1,1,2)}`.  `\T` is a subtensor of
> `T_{1,1,2}^{⊗m}[\tilde α_Z^{(1,1,2)}]`; it can be obtained by zeroing out X and Y-blocks from
> `T_{1,1,2}^{⊗m}[\tilde α_Z^{(1,1,2)}]`.  Then, we take the 3-symmetrization of `\T`, denoted by
> `sym₃(\T) = \T ⊗ \T^{rot} ⊗ \T^{rot rot}` ... Next, symmetric hashing method is applied on
> `sym₃(\T)`.*

`T_{1,1,2}^{⊗m}[\tilde α_Z^{(1,1,2)}]` is the leaf's cut: the `Z`-marginal split condition alone,
which for the level-two fine leaf is `dwz63AlphaTilde 6` --- the `b`-split
`(b, 1-2b, b)` of `global_value.tex:341-348`, at the table's `b = 0.00021015`, i.e. the committed
`42030 / 199915940 / 42030` at mass `2·10⁸`.  `\T` is the further zeroing by the X and Y
marginals, which is the committed `cw112SymmetricKeepMarginal`.  The theorem below is the sentence
"*`\T` ... can be obtained by zeroing out X and Y-blocks from `T_{1,1,2}^{⊗m}[\tilde α_Z]`*"
together with "*we take the 3-symmetrization of `\T`*", read in the direction the value argument
uses it: the marginal-cut object sits inside `sym₃` of the `Z`-typed cut, so a value proved for
the former is a value for the latter.

The X/Y-marginal implication itself --- that `KeepsMarginal` on all three legs forces each of the
three factors' `Z` letter type to be `alphatilde`-proportional --- is the one hypothesis left open
here; it is the paper's "*inconsistent with the marginal distributions*" bookkeeping and is the next
increment.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power_appendix.tex:26-45` (proof of `lem:non-rot-values` (d)),
`second_power.tex:142-158` (`lem:non-rot-values`, `eq:tilde_A`), `second_power.tex:235`
(`note:T112`), `global_value.tex:341-348` (the `b`-parametrisation of `tilde α_{1,1,2}`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- **`sym₃` of the leaf's `alphatilde`-typed `112` cut restricts onto the committed symmetric
ambient power.**

The hypothesis `himp` is the paper's marginal bookkeeping: every block the value certificate keeps
(the three-marginal condition `cw112SymmetricKeepMarginal`) is a block of `sym₃` of the `Z`-typed
cut.  Given it, a `tau`-weight for the certificate's object descends to `sym₃` of the leaf's cut,
which composes with image 127 and image 104 to the fine leaf's orbit-region entry.

Proof sketch: `isomorphic_symThreePartition_positivePower_select` rewrites `sym₃` of the cut as a
cut of the positive power of the three-orientation partition --- which is definitionally the
certificate's `cw112SymmetricPartitionedTensor` --- and `Restricts.select_of_imp` then compares the
two cuts of that one parent. -/
theorem cw112_symThree_typedCut_restricts_symmetricAmbient
    (K : Type u) [CommRing K] (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    [Fact p.Prime] (hp : 27 ≤ p) {M : ℕ} (t₀ : Fin M) (j : ℕ)
    (himp : ∀ c w, cw112SymmetricKeepMarginal K q L G k hq hL hG c w →
      PartitionedTensor.symThreeKeep
        ((SegmentedSplitRestriction.ofLeg (A := CW112Block) Leg.Z
          (cw112PushedOrbitProfile t₀ j)).Keeps
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
            (fun _ ↦ t₀)) c
        ((PartitionedTensor.symThreeWordEquiv
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
          c).symm w)) :
    Restricts
      (symThree K (cw112TypedCut K q t₀
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
        j).realize)
      (cw112SymmetricAmbientPartitionedPower K q L G k p hq hL hG hp).realize :=
  (PartitionedTensor.isomorphic_symThreePartition_positivePower_select
      (cw112PartitionedTensor K q) _ _).restricts.trans
    (Restricts.select_of_imp _ _ _ himp)

end AlgebraicComplexity.Examples
