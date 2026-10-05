/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.IntegralProfileCore
import MatrixMultiplication.CompatibilityRows
import MatrixMultiplication.DyadicHomogeneousEntropy

set_option autoImplicit false

/-!
# Integral-profile semantics of dyadic entropy rows

The recursive evaluators store an integral probability profile at a common dyadic scale, whereas
finite type-counting theorems use normalized integral-profile entropy.  This lightweight module
proves the exact conversion, including zero-mass profiles and canonical finite serialization.

Compatibility requirements, certificate rows, generated data, and asymptotic estimates are
deliberately absent.  The compatibility-rate specialization is in
`MatrixMultiplication.DyadicIntegralProfileEntropy`.
-/

namespace MatrixMultiplication.DyadicIntegralProfileEntropy

open AlgebraicComplexity.WordType
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.DyadicHomogeneousEntropy
open MatrixMultiplication.HomogeneousEntropyDual
open MatrixMultiplication.SimplifiedExponentRootRecurrence

noncomputable section

universe u

/-- A dyadic homogeneous entropy is dyadic mass times the normalized integral-profile entropy in
bits.  The statement is valid for zero profiles as well as positive-mass profiles. -/
theorem weightedEntropy_eq_mass_mul_profileEntropyBits
    {I : Type u} [Fintype I] (bits : ℕ) (profile : I → ℕ) :
    weightedEntropy bits profile =
      mass bits (profileMass profile) *
        (profileEntropyNats profile / Real.log 2) := by
  classical
  rcases Nat.eq_zero_or_pos (profileMass profile) with hzero | hpositive
  · have hpoint : ∀ i, profile i = 0 := by
      intro i
      have hle : profile i ≤ profileMass profile :=
        Finset.single_le_sum (f := profile) (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ i)
      exact Nat.eq_zero_of_le_zero (by simpa [hzero] using hle)
    have hprofile : profile = fun _ ↦ 0 := funext hpoint
    rw [hprofile]
    simp [weightedEntropy, totalNumerator, profileMass, entropyTerm_zero, mass]
  · let p : I → ℝ := fun i ↦ mass bits (profile i)
    have htotal : totalMass p = mass bits (profileMass profile) := by
      simpa only [p, totalNumerator, profileMass] using
        (totalMass_dyadic bits profile)
    have htotalPositive : 0 < totalMass p := by
      rw [htotal]
      unfold mass
      positivity
    have hnormalize : MatrixMultiplication.HomogeneousEntropyDual.normalize p =
        fun i ↦ (profile i : ℝ) / (profileMass profile : ℝ) := by
      funext i
      unfold MatrixMultiplication.HomogeneousEntropyDual.normalize
      rw [htotal]
      dsimp only [p]
      unfold mass
      have hpow : (2 : ℝ) ^ bits ≠ 0 := by positivity
      have hmass : (profileMass profile : ℝ) ≠ 0 := by
        exact_mod_cast hpositive.ne'
      field_simp [hpow, hmass]
    calc
      weightedEntropy bits profile = homogeneousEntropyBits p := by
        exact weightedEntropy_dyadic_eq_homogeneousEntropyBits bits profile
      _ = totalMass p *
          MatrixMultiplication.EntropyDual.entropyBits
            (MatrixMultiplication.HomogeneousEntropyDual.normalize p) :=
        homogeneousEntropyBits_eq_mass_mul_entropyBits_normalize p htotalPositive
      _ = mass bits (profileMass profile) *
          (profileEntropyNats profile / Real.log 2) := by
        rw [htotal, hnormalize]
        rfl

/-- The preceding conversion with the common dyadic and base-two denominators collected into one
factor.  This is the convenient form for sums of conditional rows. -/
theorem weightedEntropy_eq_profileEntropyMass_div
    {I : Type u} [Fintype I] (bits : ℕ) (profile : I → ℕ) :
    weightedEntropy bits profile =
      ((profileMass profile : ℝ) * profileEntropyNats profile) /
        ((2 : ℝ) ^ bits * Real.log 2) := by
  rw [weightedEntropy_eq_mass_mul_profileEntropyBits]
  unfold mass
  simp only [div_eq_mul_inv]
  ring

/-- Canonical finite serialization preserves dyadic homogeneous entropy. -/
theorem weightedEntropyList_numeratorList
    {I : Type u} [Fintype I] [DecidableEq I]
    (bits : ℕ) (profile : I → ℕ) :
    weightedEntropyList bits (numeratorList profile) =
      weightedEntropy bits profile := by
  unfold numeratorList weightedEntropyList entropyList weightedEntropy totalNumerator
  simp only [List.map_map, Finset.sum_map_toList, Function.comp_apply]

end

end MatrixMultiplication.DyadicIntegralProfileEntropy
