/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LaserRate
import AlgebraicComplexity.MatrixMultiplication.CyclicProductPowerCoherence

/-!
# The cyclic laser extraction rate

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module is the lightweight semantic
core of cyclic laser extraction.  It defines the logarithmic rate obtained from polynomial
degenerations of powers of the three-orientation product and proves the normalization bridge from
an ordinary laser rate on that product.

Subexponential copy/volume sequences live in `CyclicLaserVolume.lean`; border-rank and value
soundness live in `CyclicLaserRateSoundness.lean`.  Keeping those clients out of this file lets
value and certificate modules depend on the rate relation without importing the entire
subexponential-growth cone.

## Main declarations

* `HasCyclicLaserExtractionRate`: the normalized cyclic logarithmic extraction relation; and
* `HasLaserExtractionRate.toCyclic`: division by three from the ordinary three-orientation rate.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

section Semiring

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- A tensor achieves a cyclic logarithmic laser rate if powers of its three-orientation product
degenerate to matrix-multiplication direct sums of the corresponding asymptotic-sum value.

The factor `3 * k` is essential: the source contains three differently oriented copies of
`T^k`.  Thus `value` is the logarithmic rate per original copy of `T`, equivalently one third of
the logarithmic rate of the cyclic product. -/
def HasCyclicLaserExtractionRate (T : Tensor3 K V) (value : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (k L : ℕ) (m n p : Fin L → ℕ),
      0 < k ∧
        (∀ i, 0 < m i) ∧ (∀ i, 0 < n i) ∧ (∀ i, 0 < p i) ∧
        PolynomialDegenerates (cyclicPowerProduct K T k)
          (matrixMultiplicationDirectSum K m n p) ∧
        0 < asymptoticSum K m n p ∧
        ((3 * k : ℕ) : ℝ) * (value - ε) ≤
          Real.log (asymptoticSum K m n p)

/-- An ordinary laser rate for the three-orientation product gives one third of that rate per
original tensor.

This is the semantic normalization bridge between the ordinary and cyclic laser interfaces.  Its
source is the single tensor `T ⊗ cycle(T) ⊗ cycle⁻¹(T)`; the cyclic interface instead writes its
`k`th power as the product of the three oriented copies of `T^k` and counts `3 * k` original
tensors.

Proof sketch: ask the ordinary rate theorem for loss `3 * ε`.  For its positive power `k = j+1`,
`Tensor.Isomorphic.cyclicPowerProduct_positive` identifies the ordinary source power with the
cyclic source.  Transport the degeneration across that isomorphism, and observe that
`k * (value - 3ε) = (3k) * (value / 3 - ε)`. -/
theorem HasLaserExtractionRate.toCyclic
    {T : Tensor3 K V} {value : ℝ}
    (h : HasLaserExtractionRate K
      (Tensor.external
        (Tensor.external T (Tensor.permute cycle T))
        (Tensor.permute cycle.symm T)) value) :
    HasCyclicLaserExtractionRate K T (value / 3) := by
  intro ε hε
  obtain ⟨k, L, m, n, p, hk, hm, hn, hp, hdeg, hsum, hrate⟩ :=
    h (3 * ε) (mul_pos (by norm_num) hε)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  refine ⟨j + 1, L, m, n, p, hk, hm, hn, hp, ?_, hsum, ?_⟩
  · exact
      (PolynomialDegenerates.of_restricts
        (Tensor.Isomorphic.cyclicPowerProduct_positive T j).restricts).trans hdeg
  · calc
      (((3 * (j + 1) : ℕ) : ℝ) * (value / 3 - ε)) =
          (((j + 1 : ℕ) : ℝ) * (value - 3 * ε)) := by
            push_cast
            ring
      _ ≤ Real.log (asymptoticSum K m n p) := hrate

end Semiring

end AlgebraicComplexity
