/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitRowSixWeight
import AlgebraicComplexity.MatrixMultiplication.TauValueConstantDirectSum

set_option autoImplicit false

/-!
# The `tau`-weight of the symmetric ambient power

Layer 4 (`AlgebraicComplexity/Examples/`).  Image 148 left one binder open: a `HasTauWeight` for
`cw112SymmetricAmbientPartitionedPower`
(`Examples/CoppersmithWinograd112SymmetricFiniteExtraction.lean:61`).  This module supplies it from
the committed finite extraction (`:159`) and the numerical adapter of
`MatrixMultiplication/TauValueConstantDirectSum.lean`.

## The paper

This is the value bound for the `(1,1,2)` component.  `[duan2023faster]` arXiv:2210.10173,
`second_power_appendix.tex:26-45` (proof of `lem:non-rot-values` (d)) states the route in one
sentence: *"symmetric hashing method is applied on `sym₃(\T)` to obtain
`binom(m, m/2)² binom(m, 2a'm, b'm, b'm) · 2^{-o(m)}` disjoint triples.  Each triple is isomorphic
to `⟨q^{(4a'+2b')m}, q^{(4a'+2b')m}, q^{(4a'+2b')m}⟩`.  This leads to the lower bound
`V^{(3)}_τ(T_{1,1,2}, α̃_Z) ≥ (binom(m,m/2)² binom(m, 2a'm, b'm, b'm))^{1/(3m)} ·
q^{(4a'+2b')τ}`"* ---
and attributes the optimisation `b' = 1/(2+q^{3τ})` to Coppersmith and Winograd, *Matrix
multiplication via arithmetic progressions*, J. Symbolic Computation 9 (1990), pp. 270--272 (the
value of `T_{1,1,2}`, cited there as `\cite{coppersmith1987matrix}`).  The level-two instance with
the free `b` is `global_value.tex:341-348`.

The paper's shape is therefore: *count the surviving triples, each of the same volume*.  That is
literally the content of `HasTauWeight.ofConstantIndexedDirectSum`: the extraction produces a
degeneration onto a constant family indexed by the survivors, and the weight is the volume power
sum of that family.

## Deviation from the paper's route, flagged

The paper takes the `1/(3m)`-th root and passes to the limit, so its `V^{(3)}_τ` is an asymptotic
quantity.  The repository does not: `HasTauWeight` keeps the finite volume power sum, and the
asymptotics live separately in the growth module, which certifies the *same* numeric fields
(`Examples/CoppersmithWinograd112SymmetricGrowth.lean:265-330`, all `rfl`).  The theorem below is
therefore the finite half of the paper's sentence, stated at the exact survivor count; the
asymptotic half is `exists_eventually_cw112SymmetricLimitLowerTerm_le_certificate` and is not
restated here.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power_appendix.tex:26-45` (`lem:non-rot-values` (d)),
`global_value.tex:341-348`; Don Coppersmith and Shmuel Winograd, *Matrix multiplication via
arithmetic progressions*, J. Symbolic Computation 9 (1990), pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [Field K]

/-- **The symmetric ambient power carries the `tau`-weight of its surviving triples.**

The value is bounded by the volume power sum of the constant survivor family --- the paper's
"number of disjoint triples times one triple's volume to the `tau`"
(`second_power_appendix.tex:26-45`).

Proof: the committed finite extraction degenerates the ambient onto that constant family, and
`HasTauWeight.ofConstantIndexedDirectSum` reads the degeneration as a weight. -/
theorem cw112SymmetricAmbientHasTauWeight
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (hk : 0 < k)
    [Fact p.Prime] (hp : 27 ≤ p)
    (B : Finset (ZMod p)) (hB : ThreeAPFree (B : Set (ZMod p)))
    (seed : ProgressionHash.Seed (ZMod p)
      (Fin ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1)))
    (τ : ℝ) {value : ℝ}
    (hvalue : value ≤ matrixMultiplicationVolumePowerSum
      (fun _ : Fin (Fintype.card
        ((cw112SymmetricPartitionHashEncoding K q p hp).markedLegwiseIsolatedPowerAddresses
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).ambientWords k)
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).markedWords k)
          B seed)) ↦
        (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .X ^ k)
      (fun _ ↦ (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct
        .Y ^ k)
      (fun _ ↦ (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct
        .Z ^ k)
      τ) :
    HasTauWeight K
      (cw112SymmetricAmbientPartitionedPower K q L G k p hq hL hG hp).realize τ value :=
  HasTauWeight.ofConstantIndexedDirectSum τ _ _ _ _
    (pow_pos ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct_pos
      Leg.X) k)
    (pow_pos ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct_pos
      Leg.Y) k)
    (pow_pos ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct_pos
      Leg.Z) k)
    (cw112SymmetricFiniteExtraction K q L G k p hq hL hG hk hp B hB seed) hvalue

/-! ## Remaining: the canonical instantiation

`exists_eventually_cw112SymmetricAmbientHasTauWeight` --- the eventual form at the canonical hash
modulus, buckets and a surviving seed, with the value bounded below by
`exp (dwz112LogValue - 10^(-22)) ^ (3 · dwz112Mass · k)` --- is NOT proved here.  It is the
theorem above instantiated at the canonical data of
`Examples/CoppersmithWinograd112SymmetricGrowth.lean`, plus the identification of this module's
volume power sum with the canonical certificate's (its `copies`, `xSize`, `ySize`, `zSize` are the
same constants, all `rfl`, `:277-330`) and then the last twenty lines of
`exists_eventually_dwz112LeafHasTauWeight` verbatim.  Two obstacles were met and are recorded on
the board: the canonical-seed statement's own elaboration hits an `isDefEq` heartbeat timeout, and
the `hroot` step it needs (`certificate.term ^ (3 · power) = volume power sum`) is currently inline
in that committed proof rather than exported. -/

end AlgebraicComplexity.Examples
