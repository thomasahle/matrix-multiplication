/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitBetaWeight

set_option autoImplicit false

/-!
# Rows 7 and 10 of the fine leaf's orbit premise, hypothesis-free

Layer 4 (`AlgebraicComplexity/Examples/`).  Image 155 made the symmetric ambient power a
`HasTauWeight` at the free-`beta` value; this module instantiates that at the canonical hash
modulus, Behrend buckets and a surviving seed, and thereby discharges the binder the previous
module left open.  Rows `7` and `10` of image 135's `R3` premise --- the components `(1,2,1)` and
`(2,1,1)` --- are then hypothesis-free at `eps = dwz63LeafMargin`.

## The paper

`[duan2023faster]` arXiv:2210.10173, `second_power.tex:142-158` (`lem:non-rot-values`) and `:235`
(`note:T112`): only the three-symmetrized value `V^{(3)}_τ` of `T_{1,1,2}` is available, and the
paper reads the same value on the two rotations `T_{1,2,1}` and `T_{2,1,1}`, which is why it
requires `α(1,1,2) = α(1,2,1) = α(2,1,1)`.  The split carried here is the symmetric
degree-one one of `global_value.tex:347`; the proof of `lem:non-rot-values` (d) is
`second_power_appendix.tex:26-45`, and the optimisation is Coppersmith and Winograd, *Matrix
multiplication via arithmetic progressions*, J. Symbolic Computation 9 (1990), pp. 270--272.

## Deviation, flagged (unchanged from images 150, 152 and 155)

The paper's `V^{(3)}_τ` is the limit of the `1/(3m)`-th root; the repository keeps the finite
volume power sum in `HasTauWeight` and puts the asymptotics in the growth module.  The two meet in
`CyclicExtractionCertificate.rpow_three_mul_power_le_volumePowerSum`
(`MatrixMultiplication/CyclicValueNormalization.lean:59`), used by image 155.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power_appendix.tex:26-45`, `global_value.tex:341-348`
(`:347`); Don Coppersmith and Shmuel Winograd, *Matrix multiplication via arithmetic progressions*,
J. Symbolic Computation 9 (1990), pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [Field K]

/-- **Rows `7` and `10` of image 135's `R3` premise, hypothesis-free.**

For every sufficiently large repetition on the assembly's own `121` lattice
`3125·10^17 ∣ s`, the `(1,2,1)` and `(2,1,1)` orbit regions of the fine leaf carry the published
value backed off by `dwz63LeafMargin`, in exactly the binder shape
`DuanWuZhouLevelTwoAssemblyRowSix.lean` asks for at `o ≠ 0`.

Proof: the canonical free-`beta` ambient weight of image 155, fed through
`dwz63_orbitRowsSevenTen_R3_of_ambient` (which chains the rotation, the rotated typed cut and the
free-`beta` marginal identity, and drops the deficit from `10^(-29)` to `dwz63LeafMargin`), with
the index length identified by `dwz63_sideRegion_depth`. -/
theorem dwz63_orbitRowsSevenTen_R3 (hq : 0 < 6) (hqQ : 0 < dwz63Q) :
    ∃ N : ℕ, ∀ s : ℕ, 312500000000000000000 ∣ s →
      N ≤ 10367229 * (s / 312500000000000000000) →
      0 < 10367229 * (s / 312500000000000000000) →
      ∀ (o : Fin 3), o ≠ 0 → ∀ m : ℕ,
        m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s) →
        HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
          (dwz63Alpha (dwz63OrbitRow o) * s)).realize) dwz63Tau
          (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s : ℕ) : ℝ)
            * (dwz63OrbitLogVal o - dwz63LeafMargin)) ^ 3) := by
  obtain ⟨N, hN⟩ := exists_eventually_cw112SymmetricAmbientHasTauWeightBeta K hq
  refine ⟨N, fun s hs hk hkpos o ho m hm ↦ ?_⟩
  obtain ⟨_hkpos, seed, _hne, value, hvalue, hlower⟩ := hN _ hk
  exact dwz63_orbitRowsSevenTen_R3_of_ambient K hqQ
    (cw112SymmetricHashModulus K 6 dwz121L dwz121G
      (10367229 * (s / 312500000000000000000)) hq dwz121L_pos dwz121G_pos)
    (cw112SymmetricHashModulus_ge_twentySeven K 6 dwz121L dwz121G
      (10367229 * (s / 312500000000000000000)) hq dwz121L_pos dwz121G_pos)
    o ho s hs hvalue hlower m
    (dwz63_sideRegion_depth K hqQ o ho s hs hkpos m hm)

end AlgebraicComplexity.Examples
