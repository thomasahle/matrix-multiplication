/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CoordinateCertificate
import AlgebraicComplexity.MatrixMultiplication.Exponent

/-!
# Strassen's rank-seven decomposition

This file is a small regression client for the tensor library, and the smallest illustration of
the house certificate pattern: the seven pure tensors of Strassen's `2 × 2` algorithm are given
as one integer table, its coefficient table is checked once over `ℤ` by the kernel, and the
one-shot `MMCertificate.rankLE_of_intCoefficient` of
`MatrixMultiplication/CoordinateCertificate.lean` turns that single finite check into a
constructive tensor-rank certificate over every commutative ring.

Primary source: V. Strassen, *Gaussian elimination is not optimal*, Numer. Math. **13** (1969),
354--356.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

private def matrixUnit (i j : Fin 2) : Fin 2 × Fin 2 → ℤ :=
  Pi.single (i, j) 1

/-- The seven integer triples of linear forms in Strassen's decomposition.

The `Z` coordinate is ordered `(output column, output row)`, matching
`matrixMultiplication K 2 2 2`.
-/
def strassenIntTerms : List (∀ c, MMSpace ℤ 2 2 2 c) :=
  let e₀₀ := matrixUnit 0 0
  let e₀₁ := matrixUnit 0 1
  let e₁₀ := matrixUnit 1 0
  let e₁₁ := matrixUnit 1 1
  [ ofLegs (e₀₀ + e₁₁) (e₀₀ + e₁₁) (e₀₀ + e₁₁),
    ofLegs (e₁₀ + e₁₁) e₀₀ (e₀₁ - e₁₁),
    ofLegs e₀₀ (e₀₁ - e₁₁) (e₁₀ + e₁₁),
    ofLegs e₁₁ (e₁₀ - e₀₀) (e₀₀ + e₀₁),
    ofLegs (e₀₀ + e₀₁) e₁₁ (e₁₀ - e₀₀),
    ofLegs (e₁₀ - e₀₀) (e₀₀ + e₀₁) e₁₁,
    ofLegs (e₀₁ - e₁₁) (e₁₀ + e₁₁) e₀₀ ]

/-- The finite integer coefficient table underlying Strassen's identity.  Checking the table over
`Int` separates finite computation from the generic-ring theorem. -/
theorem strassenCoefficient_int (a : ∀ c, MMIndex 2 2 2 c) :
    MMCertificate.coefficient ℤ strassenIntTerms a = if MMCompatible a then 1 else 0 := by
  decide +revert

section

variable (K : Type u) [CommRing K]

/-- The seven triples of linear forms in Strassen's decomposition over `K`. -/
def strassenTerms : List (∀ c, MMSpace K 2 2 2 c) :=
  MMCertificate.castTerms K strassenIntTerms

@[simp] theorem strassenTerms_length : (strassenTerms K).length = 7 := by
  simp [strassenTerms, strassenIntTerms]

/-- The seven displayed pure tensors sum to the `2 × 2` matrix-multiplication tensor. -/
theorem strassen_decomposition :
    matrixMultiplication (K := K) 2 2 2 =
      ((strassenTerms K).map (pure (K := K))).sum :=
  MMCertificate.decomposition_of_intCoefficient strassenIntTerms strassenCoefficient_int

/-- Strassen's constructive tensor-rank upper bound `R(⟨2,2,2⟩) ≤ 7`. -/
theorem strassen_rankLE :
    RankLE 7 (matrixMultiplication (K := K) 2 2 2) :=
  MMCertificate.rankLE_of_intCoefficient strassenIntTerms (by simp [strassenIntTerms])
    strassenCoefficient_int

/-- Tensor powers of Strassen's decomposition give rank `7^k` for multiplication of
`2^k × 2^k` matrices. -/
theorem strassen_rankLE_pow (k : ℕ) :
    RankLE (7 ^ k)
      (matrixMultiplication (K := K) (2 ^ k) (2 ^ k) (2 ^ k)) :=
  (strassen_rankLE K).matrixMultiplication_pow k

/-- Strassen's exact algorithm gives the classical exponent bound `ω ≤ log₂(7)`. -/
theorem strassen_omega_le_log :
    omega K ≤ Real.log 7 / Real.log 2 := by
  exact omega_le_log_of_rankLE K (by norm_num) (by norm_num) (strassen_rankLE K)

end

end AlgebraicComplexity.Examples
