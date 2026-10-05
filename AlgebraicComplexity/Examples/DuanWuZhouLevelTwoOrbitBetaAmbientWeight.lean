/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitRowSixCanonical
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeightBeta

set_option autoImplicit false

/-!
# The symmetric ambient power at the free-`beta` split

Layer 4 (`AlgebraicComplexity/Examples/`).  Rows `7` and `10` of the fine leaf's orbit premise ---
the components `(1,2,1)` and `(2,1,1)` --- are weighed by the free-`beta` chain rather than the
`b`-split chain of row `6`, at `(L, G) = (dwz121L, dwz121G) = (69022217, 2430977783)`, period
`dwz121Mass = 1.25·10^29` and reserve `10^(-29)`.

This module supplies the ambient `tau`-weight those rows need.  It is image 152's canonical
instantiation at the beta constants: the same certificate constructor
(`cw112SymmetricCanonicalDegenerationValueCertificate` at `(dwz121L, dwz121G)`), the same
`CyclicExtractionCertificate.rpow_three_mul_power_le_volumePowerSum`, the same volume power sum.

## Why an ambient weight is needed here too

The committed beta bridge `exists_eventually_dwz121LeafHasTauWeight`
(`Examples/DuanWuZhouLevelTwoLeafTauWeightBeta.lean:282`) carries its weight for
`Tensor.power (symThree K (cw112PartitionedTensor K 6).realize) (dwz121Mass · k)` --- the **uncut**
power --- exactly like `exists_eventually_dwz112LeafHasTauWeight` does at the `b`-split.  Since
`cw112SymmetricPower_restricts_ambientPartitionedPower` carries a weight from the ambient UP to
the power, that theorem is downstream of the premise a cut leaf needs, not upstream of it.  So the
ambient weight is built here the same way as in images 150 and 152, rather than worked around.

## The paper

The value carried is `[duan2023faster]` arXiv:2210.10173 `lem:non-rot-values` (d)
(`second_power.tex:145-156`, proved at `second_power_appendix.tex:26-45`): `T_{1,1,2}` is the one
level-two component that is not a matrix multiplication tensor, so only its *symmetrized* value
`V^{(3)}_τ` is available (`second_power.tex:235`, footnote `note:T112`), and the rotations
`T_{1,2,1}`, `T_{2,1,1}` share it --- which is why the paper requires
`α(1,1,2) = α(1,2,1) = α(2,1,1)`.  At level two the split used for these two rows is the
symmetric degree-one one (`global_value.tex:347`: *"For all other components, we use the symmetric
Z-marginal split distributions ... So the values of all other components (including
`(2,2,0)`, `(1,2,1)`, `(2,1,1)`) do not change"*), and the free parameter `beta` enters through the
three-symmetrization rather than through `α̃`; the `b`-parametrised sibling is
`global_value.tex:341-348`.

## Deviation, flagged (unchanged from images 150 and 152)

The paper's `V^{(3)}_τ` is the limit of the `1/(3m)`-th root; the repository keeps the finite
volume power sum in `HasTauWeight` and puts the asymptotics in the growth module.
the committed `CyclicExtractionCertificate.rpow_three_mul_power_le_volumePowerSum`
(`MatrixMultiplication/CyclicValueNormalization.lean:59`) is where the two meet.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power.tex:142-158` (`lem:non-rot-values`), `:235`
(`note:T112`), `second_power_appendix.tex:26-45`, `global_value.tex:341-348`; Don Coppersmith and
Shmuel Winograd, *Matrix multiplication via arithmetic progressions*, J. Symbolic Computation 9
(1990), pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [Field K]

/-- **Eventually, the symmetric ambient power carries the free-`beta` orbit value.**

Image 152's canonical ambient weight at the beta constants: the value is the volume power sum of
the canonical survivors, and it dominates `exp (dwz121LogValue - 10^(-29))` raised to the leaf's
total index length `3 · dwz121Mass · k`.

`hq` is a named hypothesis rather than an inline tactic proof, because an inline proof in this
dependent argument position makes the statement time out at `isDefEq`. -/
theorem exists_eventually_cw112SymmetricAmbientHasTauWeightBeta (hq : 0 < 6) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∃ (_hkpos : 0 < k)
        (seed : CW112SymmetricCanonicalSeed K 6 dwz121L dwz121G k hq dwz121L_pos dwz121G_pos)
        (_hne : Nonempty (CW112SymmetricCanonicalSurvivor K 6 dwz121L dwz121G k hq
          dwz121L_pos dwz121G_pos seed))
        (value : ℝ),
        HasTauWeight K
          (cw112SymmetricAmbientPartitionedPower K 6 dwz121L dwz121G k
            (cw112SymmetricHashModulus K 6 dwz121L dwz121G k hq dwz121L_pos dwz121G_pos)
            hq dwz121L_pos dwz121G_pos
            (cw112SymmetricHashModulus_ge_twentySeven K 6 dwz121L dwz121G k hq
              dwz121L_pos dwz121G_pos)).realize dwz63Tau value ∧
        Real.exp (dwz121LogValue - 1 / 10 ^ 29) ^ (3 * (dwz121Mass * k)) ≤ value := by
  obtain ⟨N, hN⟩ := exists_eventually_cw112SymmetricLimitLowerTerm_le_certificate
    K dwz63Tau 6 dwz121L dwz121G hq dwz121L_pos dwz121G_pos
    (dwz121InnerCopyBase_pos K) (dwz121InnerCopyBase_lt K)
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨hkpos, seed, hnonempty, hterm⟩ := hN k hk
  refine ⟨hkpos, seed, hnonempty, _,
    cw112SymmetricAmbientHasTauWeight K 6 dwz121L dwz121G k _ hq dwz121L_pos dwz121G_pos hkpos
      (cw112SymmetricHashModulus_ge_twentySeven K 6 dwz121L dwz121G k hq
        dwz121L_pos dwz121G_pos)
      (cw112SymmetricBuckets K 6 dwz121L dwz121G k hq dwz121L_pos dwz121G_pos)
      (cw112SymmetricBuckets_threeAPFree K 6 dwz121L dwz121G k hq dwz121L_pos dwz121G_pos)
      seed dwz63Tau le_rfl, ?_⟩
  have hpower : (cw112SymmetricCanonicalDegenerationValueCertificate
      K dwz63Tau 6 dwz121L dwz121G k hq dwz121L_pos dwz121G_pos hkpos seed hnonempty).power =
      dwz121Mass * k := by
    have h := RationalTypedLeaf.proportionalDepth_add_one
      (cw112SymmetricLeaf K 6 dwz121L dwz121G hq dwz121L_pos dwz121G_pos) hkpos
    rw [cw112SymmetricLeaf_profile_mass] at h
    show (cw112SymmetricLeaf K 6 dwz121L dwz121G hq dwz121L_pos dwz121G_pos).proportionalDepth k
      + 1 = _
    rw [h]
  have hbound := (cw112SymmetricCanonicalDegenerationValueCertificate
      K dwz63Tau 6 dwz121L dwz121G k hq dwz121L_pos dwz121G_pos hkpos
      seed hnonempty).rpow_three_mul_power_le_volumePowerSum K (Real.exp_nonneg _)
    (le_trans (dwz121_exp_le_leafTerm K) hterm)
  rw [Real.rpow_natCast, hpower] at hbound
  exact hbound

end AlgebraicComplexity.Examples
