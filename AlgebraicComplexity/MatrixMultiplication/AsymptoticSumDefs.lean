/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExponentDefs
import AlgebraicComplexity.MatrixMultiplication.Volume

/-!
# The numerical asymptotic-sum expression

This lightweight layer defines the numerical left-hand side of Schönhage's asymptotic sum
inequality at exponent `omega / 3`.  The proof of the inequality itself remains in
`MatrixMultiplication/AsymptoticSum.lean` and imports the substantially heavier tensor-compression
machinery.

Separating the expression from its soundness theorem lets finite extraction and value interfaces
state their semantic output without paying the elaboration and memory cost of the full
Schönhage proof.
-/

namespace AlgebraicComplexity

universe u w

variable (K : Type u) [CommSemiring K]
variable {ι : Type w} [Fintype ι]

/-- The left-hand side of Schönhage's asymptotic sum inequality, specialized to exponent
`omega / 3`. -/
noncomputable def asymptoticSum (m n p : ι → ℕ) : ℝ :=
  matrixMultiplicationVolumePowerSum m n p (omega K / 3)

/-- A constant family contributes its cardinality times the common volume to the power
`omega / 3`. -/
@[simp] theorem asymptoticSum_const (a b c : ℕ) :
    asymptoticSum K (fun _ : ι ↦ a) (fun _ ↦ b) (fun _ ↦ c) =
      Fintype.card ι * ((a * b * c : ℕ) : ℝ) ^ (omega K / 3) := by
  simp [asymptoticSum, matrixMultiplicationVolumePowerSum,
    matrixMultiplicationVolume]

end AlgebraicComplexity
