import MatrixMultiplication.CurrentProofObligations
import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpoint

/-!
# Exact endpoint for the sorted-pair volume certificate

This candidate-specific adapter records only the exact rational floors consumed by the generic
Coppersmith--Winograd volume theorem.  Tensor extraction and numerical reconstruction remain
separate interfaces, so stronger certificates can reuse the same endpoint machinery.
-/

namespace MatrixMultiplication.SortedPairVolumeEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CurrentProofObligations

universe u

/-- Directed retained-exponent floor from the 20/12-bit sorted-pair certificate. -/
noncomputable def retainedFloor : ℝ := 825847 / 100000

/-- Directed rectangular-volume floor from the same certificate. -/
noncomputable def volumeFloor : ℝ := 60091 / 10000

/-- Exact rational endpoint represented by the decimal `2.363145`. -/
noncomputable def omegaTarget : ℝ := 472629 / 200000

/-- The earlier, slightly weaker endpoint retained for downstream compatibility. -/
noncomputable def legacyOmegaTarget : ℝ := 47263 / 20000

theorem volumeFloor_pos : 0 < volumeFloor := by
  norm_num [volumeFloor]

theorem omegaTarget_nonneg : 0 ≤ omegaTarget := by
  norm_num [omegaTarget]

/-- The exact final margin is `131075979 / 25000000000000 > 0`. -/
theorem certified_endpoint_slack :
    MatrixMultiplication.LogBounds.rankBudgetUpper <
      retainedFloor + omegaTarget * volumeFloor := by
  norm_num [MatrixMultiplication.LogBounds.rankBudgetUpper,
    retainedFloor, omegaTarget, volumeFloor]

/-- Semantic numerical reconstruction boundary for this endpoint. -/
def Reconstruction (retained volume : ℝ) : Prop :=
  retainedFloor ≤ retained ∧ volumeFloor ≤ volume

/-- Once the quotient extraction sequence and the two directed floors are established, the
generic rectangular-volume endpoint gives `ω < 2.363145`. -/
theorem omega_lt_2363145_of_subexponentialVolumeSequence
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : Reconstruction retained volume) :
    omega K < omegaTarget := by
  rcases hreconstruct with ⟨hretained, hvolume⟩
  apply omega_lt_of_cwPower_volumeSequence_lowerBounds K 5 8
    volumeFloor_pos hretained hvolume omegaTarget_nonneg hextractions
  calc
    (8 : ℝ) * Real.log ((5 : ℕ) + 2) / Real.log 2 = sourceRankBudget := by
      norm_num [sourceRankBudget]
      ring
    _ < retainedFloor + omegaTarget * volumeFloor :=
      sourceRankBudget_lt_upper.trans certified_endpoint_slack

/-- Compatibility corollary at the previously advertised rounded endpoint. -/
theorem omega_lt_236315_of_subexponentialVolumeSequence
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : Reconstruction retained volume) :
    omega K < legacyOmegaTarget := by
  have hstrong := omega_lt_2363145_of_subexponentialVolumeSequence
    K hextractions hreconstruct
  exact hstrong.trans_le (by norm_num [omegaTarget, legacyOmegaTarget])

theorem omegaTarget_eq_decimal : omegaTarget = 2.363145 := by
  norm_num [omegaTarget]

theorem legacyOmegaTarget_eq_decimal : legacyOmegaTarget = 2.36315 := by
  norm_num [legacyOmegaTarget]

end MatrixMultiplication.SortedPairVolumeEndpoint
