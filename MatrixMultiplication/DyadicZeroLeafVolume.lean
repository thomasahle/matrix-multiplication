/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.IntegralProfileEntropyDefs
import MatrixMultiplication.DyadicEntropyDefs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

/-!
# Dyadic semantics of a zero-coordinate leaf

A zero-coordinate leaf has two independent logarithmic contributions.  A normalized dyadic
profile contributes the entropy of its exact type class, while an additive statistic on the
profile contributes the logarithm of a local matrix dimension.  This module identifies the
evaluator's homogeneous dyadic expression with that finite typed-leaf expression.

For a profile `a` of total mass `2^bits`, a statistic `s`, and a local dimension base `q`, the
value is

```text
Σᵢ -pᵢ log₂ pᵢ + (2⁻ᵇᵢᵗˢ Σᵢ aᵢ sᵢ) log₂ q.
```

The main theorem proves that multiplying every profile count by a positive natural `k` turns the
finite typed-leaf exponent into `(2^bits * k)` times this value.  No tensor, generated table,
optimizer, or asymptotic estimate occurs here.  A CW-specific adapter only has to identify its
complete-split profile and middle-digit statistic with these parameters.
-/

open scoped BigOperators

namespace MatrixMultiplication.DyadicZeroLeafVolume

open AlgebraicComplexity.WordType
open MatrixMultiplication.DyadicEntropy

noncomputable section

universe u

variable {I : Type u} [Fintype I]

/-- Homogeneous dyadic entropy plus the local-dimension contribution of an additive statistic. -/
def value (q bits : ℕ) (profile statistic : I → ℕ) : ℝ :=
  (∑ i, entropyTerm bits (profile i)) +
    mass bits (∑ i, profile i * statistic i) * Real.logb 2 (q : ℝ)

/-- For a normalized dyadic profile, the sum of coordinatewise Shannon terms is exactly the
profile entropy in bits.

Proof sketch: the existing homogeneous-entropy theorem gives the same sum after subtracting the
entropy of the total mass.  At total numerator `2^bits`, that mass is one and its entropy is zero.
-/
theorem entropySum_eq_profileEntropyBits
    (bits : ℕ) (profile : I → ℕ)
    (hnormalized : profileMass profile = 2 ^ bits) :
    (∑ i, entropyTerm bits (profile i)) = profileEntropyBits profile := by
  unfold entropyTerm mass profileEntropyBits profileEntropyNats
  rw [← Finset.sum_div, hnormalized]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- A normalized dyadic zero-leaf value is profile entropy plus its additive local-dimension
rate. -/
theorem value_eq_profileEntropyBits_add
    (q bits : ℕ) (profile statistic : I → ℕ)
    (hnormalized : profileMass profile = 2 ^ bits) :
    value q bits profile statistic =
      profileEntropyBits profile +
        mass bits (∑ i, profile i * statistic i) * Real.logb 2 (q : ℝ) := by
  unfold value
  rw [entropySum_eq_profileEntropyBits bits profile hnormalized]

/-- Positive proportional repetition does not change normalized profile entropy in bits. -/
theorem profileEntropyBits_proportionalCounts
    (profile : I → ℕ) (k : ℕ) (hk : 0 < k) :
    profileEntropyBits (proportionalCounts profile k) = profileEntropyBits profile := by
  have hscaledMass :
      profileMass (proportionalCounts profile k) = profileMass profile * k := by
    unfold profileMass proportionalCounts
    rw [Finset.sum_mul]
  unfold profileEntropyBits profileEntropyNats
  rw [hscaledMass]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  have hratio :
      ((proportionalCounts profile k i : ℕ) : ℝ) /
          ((profileMass profile * k : ℕ) : ℝ) =
        (profile i : ℝ) / (profileMass profile : ℝ) := by
    unfold proportionalCounts
    rw [Nat.cast_mul, Nat.cast_mul]
    exact mul_div_mul_right (profile i : ℝ) (profileMass profile : ℝ)
      (Nat.cast_ne_zero.mpr hk.ne')
  rw [hratio]

/-- An additive profile statistic scales linearly under proportional repetition. -/
theorem statisticSum_proportionalCounts
    (profile statistic : I → ℕ) (k : ℕ) :
    (∑ i, proportionalCounts profile k i * statistic i) =
      (∑ i, profile i * statistic i) * k := by
  calc
    (∑ i, proportionalCounts profile k i * statistic i) =
        ∑ i, (profile i * statistic i) * k := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold proportionalCounts
      ac_rfl
    _ = (∑ i, profile i * statistic i) * k := by
      rw [Finset.sum_mul]

/-- The entropy-plus-dimension exponent of a proportionally repeated normalized profile is its
sample count times the dyadic zero-leaf value.

Proof sketch: profile entropy is invariant under repetition, the additive statistic is multiplied
by `k`, and the factor `2^bits` cancels the dyadic denominator in the statistic's mass. -/
theorem scaledProfileBits_eq_mass_mul_value
    (q bits : ℕ) (profile statistic : I → ℕ)
    (hnormalized : profileMass profile = 2 ^ bits)
    (k : ℕ) (hk : 0 < k) :
    ((((2 ^ bits) * k : ℕ) : ℝ) *
          profileEntropyBits (proportionalCounts profile k)) +
        Real.logb 2 (q : ℝ) *
          (((∑ i, proportionalCounts profile k i * statistic i : ℕ)) : ℝ) =
      ((((2 ^ bits) * k : ℕ) : ℝ) * value q bits profile statistic) := by
  rw [profileEntropyBits_proportionalCounts profile k hk,
    statisticSum_proportionalCounts profile statistic k,
    value_eq_profileEntropyBits_add q bits profile statistic hnormalized]
  unfold mass
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

end

end MatrixMultiplication.DyadicZeroLeafVolume
