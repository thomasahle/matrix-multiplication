/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.Exponent
import OpenAIBridge.ArithmeticPrograms
import OpenAIBridge.NineQuarters

/-!
# The vendored exponents are this repository's exponent

The vendored development has two exponents of square matrix multiplication: the exact-rank
exponent `exactRankExponent K = inf_{n ≥ 2} log_n R_K(⟨n,n,n⟩)` and the arithmetic exponent
`Arithmetic.omega K` of its program model.  `OpenAIBridge/NineQuarters.lean` and
`OpenAIBridge/ArithmeticPrograms.lean` compare each with this repository's `omega` in the
direction needed to import upper bounds.  This file closes the comparison:

```text
exactRankExponent K = omega K                     over every field,
Arithmetic.omega K  ≤ omega K                     over every field,
Arithmetic.omega K  = omega K                     over every infinite field.
```

So the three definitions describe one number, and statements move in both directions: an upper
bound proved upstream is an upper bound here, and a lower bound or a barrier proved here applies
to the vendored model.  Over a finite field only the inequality is available, for a reason that
is not an artefact: a vendored `MatrixAlgorithm` is required to be correct only on matrices with
entries in the field, which over a finite field does not determine a polynomial identity.

## Main results

* `rankAtMost_of_rankLE_matrixMultiplication`: a `RankLE` certificate of
  `matrixMultiplication n n n` is an exact decomposition of the vendored coordinate tensor (the
  converse of `rankLE_matrixMultiplication_of_rankAtMost`).
* `exactMatrixRank_eq_squareMatrixRankSequence`: the two ranks of `⟨n,n,n⟩` are the same number.
* `exactRankExponent_eq_omega`, `arithmeticOmega_le_omega`, `arithmeticOmega_eq_omega`.
-/

namespace AlgebraicComplexity.OpenAIBridge

open Tensor
open OAI.MatrixMultiplication

universe u

variable {K : Type u} [Field K]

/-- A rank certificate of this repository's `matrixMultiplication n n n` is an exact
decomposition of the `OAI` coordinate tensor `⟨n,n,n⟩` with the same number of terms. -/
theorem rankAtMost_of_rankLE_matrixMultiplication {n R : ℕ}
    (h : RankLE R (matrixMultiplication (K := K) n n n)) :
    Foundation.Tensor.RankAtMost
      (AuxiliarySeparation.matrixMultiplicationTensor (K := K) n n n) R := by
  obtain ⟨A, hA⟩ := (matrixMultiplication_rankLE_iff_exists_algorithm (K := K) n n n R).mp h
  rw [matrixProductMap_eq_bilinearMapOfCoeff, BilinearAlgorithm.computes_iff_coeff] at hA
  refine ⟨A.f, A.g, A.w, ?_⟩
  funext x y z
  have h := hA x y z
  simp only [mmCoeff] at h
  simp only [AuxiliarySeparation.matrixMultiplicationTensor, Foundation.Tensor.rankOne]
  rw [h]
  exact Finset.sum_congr rfl fun t _ ↦ by ring

/-- The exact rank of `⟨n,n,n⟩` in the vendored development is the rank of
`matrixMultiplication n n n` in this repository. -/
theorem exactMatrixRank_eq_squareMatrixRankSequence (K : Type u) [Field K] (n : ℕ) :
    AuxiliarySeparation.exactMatrixRank K n = squareMatrixRankSequence K n := by
  refine le_antisymm ?_ ?_
  · exact AuxiliarySeparation.exactRank_le
      (rankAtMost_of_rankLE_matrixMultiplication (rank_spec _))
  · exact rank_le_iff.mpr (rankLE_matrixMultiplication_of_rankAtMost
      (AuxiliarySeparation.exactMatrixRank_spec (K := K) n))

/-- The vendored exact-rank exponent is at most this repository's exponent. -/
theorem exactRankExponent_le_omega (K : Type u) [Field K] :
    AuxiliarySeparation.exactRankExponent K ≤ omega K := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨-, C, hC, hb⟩ :=
    matrixExponentLE_of_omega_lt K (lt_add_of_pos_right (omega K) (half_pos hε))
  obtain ⟨n, hn2, hnC⟩ : ∃ n : ℕ, 2 ≤ n ∧ C ≤ (n : ℝ) ^ (ε / 2) := by
    have htend := (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop C)
    exact ⟨max N 2, le_max_right _ _, hN _ (le_max_left _ _)⟩
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hnR
  have hpos : (0 : ℝ) < AuxiliarySeparation.exactMatrixRank K n := by
    exact_mod_cast AuxiliarySeparation.exactMatrixRank_pos (K := K) (by omega : 0 < n)
  have h2 : (AuxiliarySeparation.exactMatrixRank K n : ℝ) ≤ (n : ℝ) ^ (omega K + ε) := by
    rw [exactMatrixRank_eq_squareMatrixRankSequence]
    calc (squareMatrixRankSequence K n : ℝ) ≤ C * (n : ℝ) ^ (omega K + ε / 2) := hb n (by omega)
      _ ≤ (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (omega K + ε / 2) :=
        mul_le_mul_of_nonneg_right hnC (Real.rpow_nonneg hn0.le _)
      _ = (n : ℝ) ^ (omega K + ε) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
  calc AuxiliarySeparation.exactRankExponent K
      ≤ Real.logb n (AuxiliarySeparation.exactMatrixRank K n) :=
        AuxiliarySeparation.exactRankExponent_le_logb hn2
    _ ≤ Real.logb n ((n : ℝ) ^ (omega K + ε)) := Real.logb_le_logb_of_le hnR hpos h2
    _ = omega K + ε := Real.logb_rpow hn0 hnR.ne'

/-- **The vendored exact-rank exponent is this repository's exponent**, over every field. -/
theorem exactRankExponent_eq_omega (K : Type u) [Field K] :
    AuxiliarySeparation.exactRankExponent K = omega K :=
  le_antisymm (exactRankExponent_le_omega K) (omega_le_exactRankExponent K)

/-- The vendored arithmetic exponent is at most this repository's exponent, over every field:
rank certificates compile to programs. -/
theorem arithmeticOmega_le_omega (K : Type u) [Field K] : Arithmetic.omega K ≤ omega K :=
  AuxiliarySeparation.omega_le_exactRankExponent.trans (exactRankExponent_le_omega K)

/-- **The vendored arithmetic exponent is this repository's exponent**, over every infinite
field. -/
theorem arithmeticOmega_eq_omega (K : Type u) [Field K] [Infinite K] :
    Arithmetic.omega K = omega K :=
  le_antisymm (arithmeticOmega_le_omega K) (omega_le_arithmeticOmega K)

end AlgebraicComplexity.OpenAIBridge
