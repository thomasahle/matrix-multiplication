/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareSymmetry
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeightBeta
import AlgebraicComplexity.MatrixMultiplication.SymThreeCycleInvariance

/-!
# The exceptional orbit's `tau`-weights, read on all three coarse addresses

`Examples/DuanWuZhouLevelTwoLeafTauWeight.lean` and
`Examples/DuanWuZhouLevelTwoLeafTauWeightBeta.lean` produce `[DuanWuZhou2022]` section 6.3's two
`tau`-weights for the exceptional orbit `{(1,1,2), (1,2,1), (2,1,1)}`, at the two splits

* `b = 21015 / 10 ^ 8`, mass `D_b = 8 * 10 ^ 21`, value `27.0947543121752429`, and
* `beta = 69022217 / 5000000000`, mass `D_beta = 1.25 * 10 ^ 29`, value `27.3288311864040788`.

Both are stated on `sym_3` of the `(1,1,2)` constituent, because that is the only orbit member the
committed `(112)` value chain is phrased in.  This module removes that asymmetry: with
`MatrixMultiplication/SymThreeCycleInvariance.lean`'s unconditional
`Isomorphic.symThree_permute_cycle` / `Isomorphic.symThree_permute_cycleSymm`, each weight is
restated verbatim on `sym_3` of the `(1,2,1)` and `(2,1,1)` constituents.

The two committed orbit isomorphisms

* `cwSquareConstituent_211_isomorphic_cycle`   --- `T_{2,1,1} ≅ T_{1,1,2}^rot`
* `cwSquareConstituent_121_isomorphic_cycleSymm` --- `T_{1,2,1} ≅ T_{1,1,2}^{rot⁻¹}`

turn each rotated constituent into a rotation of the `(1,1,2)` one, and cyclic invariance of
`sym_3` then absorbs the rotation.  `HasTauWeight` transports along the resulting restriction.

## Why this matters for the six-orientation partition

A letter of `symSixPartition` carries the full `S_3`-orbit of its coarse address, so which of the
six weights below a letter spends is decided by the letter's coarse *address* --- `(1,1,2)`,
`(1,2,1)` or `(2,1,1)` --- and by which split section 6.3 assigns to it, not by the letter's
tensor.  Having all six named avoids a rotation argument at every use site.

## Position in the library

Layer 4 (a client).  It adds no arithmetic: every value, mass and reserve is inherited unchanged
from the two split modules, and the only new ingredient is the cyclic invariance of `sym_3`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power.tex` `lem:non-rot-values` (d) and `global_value.tex`
section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

variable (K : Type u) [Field K]

/-! ## Restricting the rotated constituents onto the `(1,1,2)` one -/

/-- `sym_3(T_{1,2,1})` restricts onto `sym_3(T_{1,1,2})`: the committed orbit isomorphism makes it
a `rot⁻¹` rotation, and `sym_3` is invariant under rotation. -/
theorem restricts_symThree_cwSquare121 (q : ℕ) :
    Restricts (symThree K ((cwSquarePartitionedTensor K q).constituent cwSquare121))
      (symThree K ((cwSquarePartitionedTensor K q).constituent cwSquare112)) :=
  ((Isomorphic.symThree_congr
      (cwSquareConstituent_121_isomorphic_cycleSymm K q)).trans
    (Isomorphic.symThree_permute_cycleSymm
      ((cwSquarePartitionedTensor K q).constituent cwSquare112))).restricts

/-- `sym_3(T_{2,1,1})` restricts onto `sym_3(T_{1,1,2})`, by the `rot` rotation. -/
theorem restricts_symThree_cwSquare211 (q : ℕ) :
    Restricts (symThree K ((cwSquarePartitionedTensor K q).constituent cwSquare211))
      (symThree K ((cwSquarePartitionedTensor K q).constituent cwSquare112)) :=
  ((Isomorphic.symThree_congr
      (cwSquareConstituent_211_isomorphic_cycle K q)).trans
    (Isomorphic.symThree_permute_cycle
      ((cwSquarePartitionedTensor K q).constituent cwSquare112))).restricts

/-! ## The `b`-split weight on the two rotated letters -/

/-- The `(1,1,2)`-split weight, read on the `(1,2,1)` constituent. -/
theorem exists_eventually_dwz112Orbit121HasTauWeight :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare121))
          (dwz112Mass * k))
        dwz63Tau (dwz112LeafTerm K ^ (3 * (dwz112Mass * k))) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz112ConstituentHasTauWeight K
  exact ⟨N, fun k hk ↦ (hN k hk).of_restricts
    (Tensor.Restricts.power (restricts_symThree_cwSquare121 K dwz63Q) _)⟩

/-- The `(1,1,2)`-split weight, read on the `(2,1,1)` constituent. -/
theorem exists_eventually_dwz112Orbit211HasTauWeight :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare211))
          (dwz112Mass * k))
        dwz63Tau (dwz112LeafTerm K ^ (3 * (dwz112Mass * k))) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz112ConstituentHasTauWeight K
  exact ⟨N, fun k hk ↦ (hN k hk).of_restricts
    (Tensor.Restricts.power (restricts_symThree_cwSquare211 K dwz63Q) _)⟩

/-! ## The free-`beta` weight on the two rotated letters

These are the two `[DuanWuZhou2022]` section 6.3 actually spends on `(1,2,1)` and `(2,1,1)`. -/

/-- **The free-`beta` weight, read on the `(1,2,1)` constituent.** -/
theorem exists_eventually_dwz121Orbit121HasTauWeight :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare121))
          (dwz121Mass * k))
        dwz63Tau (dwz121LeafTerm K ^ (3 * (dwz121Mass * k))) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz121ConstituentHasTauWeight K
  exact ⟨N, fun k hk ↦ (hN k hk).of_restricts
    (Tensor.Restricts.power (restricts_symThree_cwSquare121 K dwz63Q) _)⟩

/-- **The free-`beta` weight, read on the `(2,1,1)` constituent.** -/
theorem exists_eventually_dwz121Orbit211HasTauWeight :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare211))
          (dwz121Mass * k))
        dwz63Tau (dwz121LeafTerm K ^ (3 * (dwz121Mass * k))) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz121ConstituentHasTauWeight K
  exact ⟨N, fun k hk ↦ (hN k hk).of_restricts
    (Tensor.Restricts.power (restricts_symThree_cwSquare211 K dwz63Q) _)⟩

/-! ## Exponential (`hvalue`) forms -/

/-- The free-`beta` weight on `(1,2,1)`, in the `hvalue` shape. -/
theorem exists_eventually_dwz121Orbit121HasTauWeight_exp :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∃ value : ℝ, 0 < value ∧
      HasTauWeight K
        (Tensor.power
          (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare121))
          (dwz121Mass * k))
        dwz63Tau value ∧
      Real.exp (dwz121LogValue - 1 / 10 ^ 29) ^ (3 * (dwz121Mass * k)) ≤ value := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz121Orbit121HasTauWeight K
  refine ⟨N, fun k hk ↦ ⟨dwz121LeafTerm K ^ (3 * (dwz121Mass * k)),
    pow_pos (dwz121LeafTerm_pos K) _, hN k hk, ?_⟩⟩
  exact pow_le_pow_left₀ (Real.exp_nonneg _) (dwz121_exp_le_leafTerm K) _

/-- The free-`beta` weight on `(2,1,1)`, in the `hvalue` shape. -/
theorem exists_eventually_dwz121Orbit211HasTauWeight_exp :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∃ value : ℝ, 0 < value ∧
      HasTauWeight K
        (Tensor.power
          (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare211))
          (dwz121Mass * k))
        dwz63Tau value ∧
      Real.exp (dwz121LogValue - 1 / 10 ^ 29) ^ (3 * (dwz121Mass * k)) ≤ value := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz121Orbit211HasTauWeight K
  refine ⟨N, fun k hk ↦ ⟨dwz121LeafTerm K ^ (3 * (dwz121Mass * k)),
    pow_pos (dwz121LeafTerm_pos K) _, hN k hk, ?_⟩⟩
  exact pow_le_pow_left₀ (Real.exp_nonneg _) (dwz121_exp_le_leafTerm K) _

end

end AlgebraicComplexity.Examples
