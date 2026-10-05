/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
import Mathlib.Tactic.IntervalCases

/-!
# Schönhage's ten-term direct-sum degeneration

This regression client formalizes the approximate decomposition displayed after the asymptotic
sum inequality in the classical exposition: the direct sum
`⟨3,1,3⟩ ⊕ ⟨1,4,1⟩` has constructive border rank at most ten.  Applying the reusable
asymptotic sum inequality gives

`9^(omega/3) + 4^(omega/3) ≤ 10`

and an exact rational comparison then yields the historical strict bound `omega < 2.6`.

Sources: Schönhage, *Partial and Total Matrix Multiplication*, SIAM Journal on Computing 10(3),
[doi:10.1137/0210032](https://doi.org/10.1137/0210032), Section 7; and the concise presentation in
[He and Williams's CS 6810 notes](https://www.cs.cornell.edu/courses/cs6810/2023fa/Matrix.pdf),
Section 3.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open Tensor.PolynomialVector

universe u

def schonhageM : Bool → ℕ
  | false => 3
  | true => 1

def schonhageN : Bool → ℕ
  | false => 1
  | true => 4

def schonhageP : Bool → ℕ
  | false => 3
  | true => 1

abbrev SchonhageSpace (K : Type u) [CommSemiring K] :=
  MMDirectSumSpace K schonhageM schonhageN schonhageP

section

variable (K : Type u) [CommRing K]

private noncomputable def includeFirst : ∀ c,
    MMSpace K 3 1 3 c →ₗ[K] SchonhageSpace K c :=
  Tensor.indexedInclude (K := K)
    (V := fun b ↦ MMSpace K (schonhageM b) (schonhageN b) (schonhageP b)) false

private noncomputable def includeSecond : ∀ c,
    MMSpace K 1 4 1 c →ₗ[K] SchonhageSpace K c :=
  Tensor.indexedInclude (K := K)
    (V := fun b ↦ MMSpace K (schonhageM b) (schonhageN b) (schonhageP b)) true

noncomputable def schonA (i : Fin 3) : SchonhageSpace K .X :=
  includeFirst K .X (Pi.single (i, 0) 1)

noncomputable def schonB (j : Fin 3) : SchonhageSpace K .Y :=
  includeFirst K .Y (Pi.single (0, j) 1)

noncomputable def schonC (i j : Fin 3) : SchonhageSpace K .Z :=
  includeFirst K .Z (Pi.single (j, i) 1)

noncomputable def schonU (l : Fin 4) : SchonhageSpace K .X :=
  includeSecond K .X (Pi.single (0, l) 1)

noncomputable def schonV (l : Fin 4) : SchonhageSpace K .Y :=
  includeSecond K .Y (Pi.single (l, 0) 1)

noncomputable def schonW : SchonhageSpace K .Z :=
  includeSecond K .Z (Pi.single (0, 0) 1)

private abbrev PolyVec (c : Leg) := PolynomialVector (SchonhageSpace K c)

noncomputable def schonCurve00 : ∀ c, PolyVec K c :=
  ofLegs
    (constant (schonA K 0) + monomial 1 (schonU K 0))
    (constant (schonB K 0) + monomial 1 (schonV K 0))
    (constant (schonW K) + monomial 2 (schonC K 0 0))

noncomputable def schonCurve01 : ∀ c, PolyVec K c :=
  ofLegs
    (constant (schonA K 0) + monomial 1 (schonU K 1))
    (constant (schonB K 1) + monomial 1 (schonV K 1))
    (constant (schonW K) + monomial 2 (schonC K 0 1))

noncomputable def schonCurve10 : ∀ c, PolyVec K c :=
  ofLegs
    (constant (schonA K 1) + monomial 1 (schonU K 2))
    (constant (schonB K 0) + monomial 1 (schonV K 2))
    (constant (schonW K) + monomial 2 (schonC K 1 0))

noncomputable def schonCurve11 : ∀ c, PolyVec K c :=
  ofLegs
    (constant (schonA K 1) + monomial 1 (schonU K 3))
    (constant (schonB K 1) + monomial 1 (schonV K 3))
    (constant (schonW K) + monomial 2 (schonC K 1 1))

noncomputable def schonCurve20 : ∀ c, PolyVec K c :=
  ofLegs
    (constant (schonA K 2) + monomial 1 (-schonU K 0 - schonU K 2))
    (constant (schonB K 0))
    (constant (schonW K) + monomial 2 (schonC K 2 0))

noncomputable def schonCurve21 : ∀ c, PolyVec K c :=
  ofLegs
    (constant (schonA K 2) + monomial 1 (-schonU K 1 - schonU K 3))
    (constant (schonB K 1))
    (constant (schonW K) + monomial 2 (schonC K 2 1))

noncomputable def schonCurve02 : ∀ c, PolyVec K c :=
  ofLegs
    (constant (schonA K 0))
    (constant (schonB K 2) + monomial 1 (-schonV K 0 - schonV K 1))
    (constant (schonW K) + monomial 2 (schonC K 0 2))

noncomputable def schonCurve12 : ∀ c, PolyVec K c :=
  ofLegs
    (constant (schonA K 1))
    (constant (schonB K 2) + monomial 1 (-schonV K 2 - schonV K 3))
    (constant (schonW K) + monomial 2 (schonC K 1 2))

noncomputable def schonCurve22 : ∀ c, PolyVec K c :=
  ofLegs
    (constant (schonA K 2))
    (constant (schonB K 2))
    (constant (schonW K) + monomial 2 (schonC K 2 2))

noncomputable def schonCancellationCurve : ∀ c, PolyVec K c :=
  ofLegs
    (constant (-(schonA K 0 + schonA K 1 + schonA K 2)))
    (constant (schonB K 0 + schonB K 1 + schonB K 2))
    (constant (schonW K))

noncomputable def schonBorderTerms : List (∀ c, PolyVec K c) :=
  [schonCurve00 K, schonCurve01 K, schonCurve10 K, schonCurve11 K,
    schonCurve20 K, schonCurve21 K, schonCurve02 K, schonCurve12 K,
    schonCurve22 K, schonCancellationCurve K]

@[simp] theorem schonBorderTerms_length : (schonBorderTerms K).length = 10 := by
  simp [schonBorderTerms]

noncomputable def schonBorderPath : PolynomialTensor K (SchonhageSpace K) :=
  (schonBorderTerms K).map (polynomialPure (K := K)) |>.sum

theorem schonBorderPath_coeff_zero : schonBorderPath K 0 = 0 := by
  simp [schonBorderPath, schonBorderTerms, schonCurve00, schonCurve01,
    schonCurve10, schonCurve11, schonCurve20, schonCurve21, schonCurve02,
    schonCurve12, schonCurve22, schonCancellationCurve, constant]
  abel

theorem schonBorderPath_coeff_one : schonBorderPath K 1 = 0 := by
  simp [schonBorderPath, schonBorderTerms, schonCurve00, schonCurve01,
    schonCurve10, schonCurve11, schonCurve20, schonCurve21, schonCurve02,
    schonCurve12, schonCurve22, schonCancellationCurve, constant]
  simp only [sub_eq_add_neg]
  rw [pure_ofLegs_add_X, pure_ofLegs_add_X,
    pure_ofLegs_add_Y, pure_ofLegs_add_Y]
  simp
  abel

noncomputable def schonhageTensor : Tensor3 K (SchonhageSpace K) :=
  matrixMultiplicationDirectSum K schonhageM schonhageN schonhageP

private theorem map_first_matrixMultiplication :
    map (includeFirst K) (matrixMultiplication (K := K) 3 1 3) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        pure (K := K) (ofLegs (schonA K i) (schonB K j) (schonC K i j)) := by
  unfold matrixMultiplication
  rw [map_sum]
  simp_rw [Tensor.map_pure]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext c
  cases c <;> rfl

private theorem map_second_matrixMultiplication :
    map (includeSecond K) (matrixMultiplication (K := K) 1 4 1) =
      ∑ l : Fin 4,
        pure (K := K) (ofLegs (schonU K l) (schonV K l) (schonW K)) := by
  unfold matrixMultiplication
  rw [map_sum]
  simp_rw [Tensor.map_pure]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  simp_rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  funext c
  cases c <;> rfl

theorem schonhageTensor_expansion : schonhageTensor K =
    (∑ i : Fin 3, ∑ j : Fin 3,
      pure (K := K) (ofLegs (schonA K i) (schonB K j) (schonC K i j))) +
      ∑ l : Fin 4,
        pure (K := K) (ofLegs (schonU K l) (schonV K l) (schonW K)) := by
  unfold schonhageTensor matrixMultiplicationDirectSum Tensor.indexedDirectSum
  rw [Fintype.sum_bool]
  change map (includeSecond K) (matrixMultiplication (K := K) 1 4 1) +
      map (includeFirst K) (matrixMultiplication (K := K) 3 1 3) = _
  rw [map_first_matrixMultiplication, map_second_matrixMultiplication]
  abel

theorem schonBorderPath_coeff_two : schonBorderPath K 2 = schonhageTensor K := by
  rw [schonhageTensor_expansion]
  simp [schonBorderPath, schonBorderTerms, schonCurve00, schonCurve01,
    schonCurve10, schonCurve11, schonCurve20, schonCurve21, schonCurve02,
    schonCurve12, schonCurve22, schonCancellationCurve, constant]
  simp [Fin.sum_univ_succ]
  abel

theorem schonhage_borderRankLE : BorderRankLE 10 (schonhageTensor K) := by
  refine ⟨2, schonBorderTerms K, ?_, ?_⟩
  · simp
  · constructor
    · exact schonBorderPath_coeff_two K
    · intro d hd
      interval_cases d
      · exact schonBorderPath_coeff_zero K
      · exact schonBorderPath_coeff_one K

end


section Field

variable (K : Type u) [Field K]

theorem schonhage_asymptoticSum_bound :
    (9 : ℝ) ^ (omega K / 3) + (4 : ℝ) ^ (omega K / 3) ≤ 10 := by
  have h := asymptoticSum_le_of_borderRankLE (ι := Bool)
    K schonhageM schonhageN schonhageP (schonhage_borderRankLE K)
    (by intro i; cases i <;> norm_num [schonhageM])
    (by intro i; cases i <;> norm_num [schonhageN])
    (by intro i; cases i <;> norm_num [schonhageP])
    (PolynomialDegenerates.refl (schonhageTensor K))
  simp [asymptoticSum, matrixMultiplicationVolumePowerSum,
    matrixMultiplicationVolume, schonhageM, schonhageN, schonhageP] at h
  norm_num at h ⊢
  linarith

private theorem nine_rpow_thirteen_fifteenths_gt :
    (67 / 10 : ℝ) < (9 : ℝ) ^ (13 / 15 : ℝ) := by
  have h : (67 / 10 : ℝ) < (((9 : ℝ) ^ 13) ^ ((15 : ℝ)⁻¹)) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
    norm_num
  convert h using 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9)]
  congr 2

private theorem four_rpow_thirteen_fifteenths_gt :
    (83 / 25 : ℝ) < (4 : ℝ) ^ (13 / 15 : ℝ) := by
  have h : (83 / 25 : ℝ) < (((4 : ℝ) ^ 13) ^ ((15 : ℝ)⁻¹)) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
    norm_num
  convert h using 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 2

/-- Schönhage's ten-term approximate decomposition of
`⟨3,1,3⟩ ⊕ ⟨1,4,1⟩`, combined with the asymptotic sum inequality, gives the
classical strict bound `omega < 2.6`. -/
theorem schonhage_omega_lt_two_point_six : omega K < 13 / 5 := by
  by_contra hnot
  have hexponent : (13 / 15 : ℝ) ≤ omega K / 3 := by
    have : (13 / 5 : ℝ) ≤ omega K := le_of_not_gt hnot
    linarith
  have h9 : (9 : ℝ) ^ (13 / 15 : ℝ) ≤ (9 : ℝ) ^ (omega K / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have h4 : (4 : ℝ) ^ (13 / 15 : ℝ) ≤ (4 : ℝ) ^ (omega K / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hbound := schonhage_asymptoticSum_bound K
  linarith [nine_rpow_thirteen_fifteenths_gt, four_rpow_thirteen_fifteenths_gt]

end Field

end AlgebraicComplexity.Examples
