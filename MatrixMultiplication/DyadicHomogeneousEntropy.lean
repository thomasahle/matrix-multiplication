/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicEntropy
import MatrixMultiplication.HomogeneousEntropyDual
import Mathlib.Tactic.Ring

/-!
# Lightweight bridge from dyadic rows to homogeneous entropy

This module connects the exact dyadic numerator semantics to the generic homogeneous-entropy API.
It intentionally omits integer dual forms, exponential-family certificates, and generated data.
-/

open scoped BigOperators

namespace MatrixMultiplication.DyadicHomogeneousEntropy

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.HomogeneousEntropyDual

noncomputable section

/-- The mass of a dyadic numerator row is its total numerator at the same denominator. -/
theorem totalMass_dyadic {A : Type*} [Fintype A]
    (bits : ℕ) (numerator : A → ℕ) :
    totalMass (fun state ↦ mass bits (numerator state)) =
      mass bits (totalNumerator numerator) := by
  unfold totalMass totalNumerator mass
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  push_cast
  rfl

/-- Dyadic homogeneous entropy agrees with the generic homogeneous entropy of the represented
real mass row. -/
theorem weightedEntropy_dyadic_eq_homogeneousEntropyBits
    {A : Type*} [Fintype A] (bits : ℕ) (numerator : A → ℕ) :
    weightedEntropy bits numerator =
      homogeneousEntropyBits (fun state ↦ mass bits (numerator state)) := by
  unfold weightedEntropy homogeneousEntropyBits homogeneousEntropy
    MatrixMultiplication.EntropyDual.entropy entropyTerm
  rw [totalMass_dyadic]
  rw [← Finset.sum_div]
  simp only [DyadicEntropy.totalNumerator, totalNumerator]
  ring

end

end MatrixMultiplication.DyadicHomogeneousEntropy
