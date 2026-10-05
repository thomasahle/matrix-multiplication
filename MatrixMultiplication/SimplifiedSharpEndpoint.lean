import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpointValue
import MatrixMultiplication.CurrentProofObligations
import MatrixMultiplication.Generated.SimplifiedExponentScalarData

/-!
# Sharper uncorrected endpoint for the simplified certificate

This endpoint uses the aggregate retained-exponent witness rather than separately rounding each
recursive family.  The exact rational floors

* `E ≥ 10394985048348986652456243334017428410201561 /
    1267650600228229401496703205376000000000000`, and
* `Mvol > 6016717904289 / 1000000000000 = 6.016717904289`

already imply `ω < 2.369837225`.  Parent consistency and correlated two-letter extraction are not
used here.  The sole paper-specific input is a semantic extraction sequence whose retained rate
dominates the generated aggregate witness.

## How the endpoint reaches `omega`

Exactly as in `MatrixMultiplication/SimplifiedCoarseEndpoint.lean`: one application of the value
API's client idiom `Examples.omega_lt_of_cwPower_borderRankBudget`, hence of the regularization
bridge `AlgebraicComplexity/MatrixMultiplication/LaserVolumeRegularization.lean`.  Neither the
laser *rate* interface nor the feasibility-to-strict step
`FeasibilitySlack.strict_of_feasibility_with_slack` occurs in this module any more, and the
endpoint no longer needs positivity of the volume — only `0 ≤ omegaTarget`.
-/

namespace MatrixMultiplication.SimplifiedSharpEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CurrentProofObligations

universe u

/-- Certified aggregate retained-exponent floor. -/
noncomputable def retainedFloor : ℝ :=
  10394985048348986652456243334017428410201561 /
    1267650600228229401496703205376000000000000

/-- Certified rectangular-volume floor. -/
noncomputable def volumeFloor : ℝ := 6016717904289 / 1000000000000

/-- Exact rational endpoint represented by the decimal `2.369837225`. -/
noncomputable def omegaTarget : ℝ := 2369837225 / 1000000000

theorem retainedFloor_le_witness :
    retainedFloor ≤
      MatrixMultiplication.Generated.SimplifiedExponentScalar.retainedExponentLowerWitness := by
  apply le_trans (b :=
    MatrixMultiplication.Generated.SimplifiedExponentScalar.retainedExponentRationalFloor)
  · norm_num [retainedFloor,
      MatrixMultiplication.Generated.SimplifiedExponentScalar.retainedExponentRationalFloor,
      MatrixMultiplication.Generated.SimplifiedExponentScalar.positiveFloorSum,
      MatrixMultiplication.Generated.SimplifiedExponentScalar.negativeCeilingSum,
      MatrixMultiplication.Generated.SimplifiedExponentScalar.bits,
      MatrixMultiplication.Generated.SimplifiedExponentScalar.constantNumerator,
      MatrixMultiplication.Generated.SimplifiedExponentScalar.inverseLogFloor,
      MatrixMultiplication.Generated.SimplifiedExponentScalar.Positive0.floor,
      MatrixMultiplication.Generated.SimplifiedExponentScalar.Negative0.ceiling,
      MatrixMultiplication.DyadicEntropy.mass]
  · exact MatrixMultiplication.Generated.SimplifiedExponentScalar.retainedExponentRationalFloor_le

theorem volumeFloor_pos : 0 < volumeFloor := by
  norm_num [volumeFloor]

theorem omegaTarget_pos : 0 < omegaTarget := by
  norm_num [omegaTarget]

/-- The exact positive arithmetic margin is approximately `4.4668e-10`. -/
theorem certified_endpoint_slack :
    MatrixMultiplication.LogBounds.rankBudgetUpper <
      retainedFloor + omegaTarget * volumeFloor := by
  norm_num [MatrixMultiplication.LogBounds.rankBudgetUpper,
    retainedFloor, omegaTarget, volumeFloor]

/-- Semantic reconstruction interface for the sharp uncorrected endpoint. -/
def Reconstruction (retained volume : ℝ) : Prop :=
  MatrixMultiplication.Generated.SimplifiedExponentScalar.retainedExponentLowerWitness ≤
      retained ∧
    volumeFloor ≤ volume

/-- The simplified certificate, without either new correction, proves `ω < 2.369837225` once
its generated recurrence is connected to the finite extraction sequence.

The tensor content is one application of `Examples.omega_lt_of_cwPower_borderRankBudget` at
`q = 5`, `power = 8`; the rest is the rational chain from the aggregate retained witness through
`certified_endpoint_slack` to the source budget `sourceRankBudget = 8·log₂ 7`. -/
theorem omega_lt_2369837225_of_subexponentialVolumeSequence
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : Reconstruction retained volume) :
    omega K < omegaTarget := by
  obtain ⟨hwitness, hvolume⟩ := hreconstruct
  have hretained : retainedFloor ≤ retained := retainedFloor_le_witness.trans hwitness
  refine omega_lt_of_cwPower_borderRankBudget K 5 8 omegaTarget_pos.le hextractions ?_
  have hbudget :
      ((8 : ℕ) : ℝ) * Real.log (((5 : ℕ) : ℝ) + 2) / Real.log 2 = sourceRankBudget := by
    rw [sourceRankBudget, show (((5 : ℕ) : ℝ) + 2) = 7 by norm_num]
    push_cast
    ring
  have hnumericLower :
      retainedFloor + omegaTarget * volumeFloor ≤
        retained + omegaTarget * volume := by
    have hvolumeTerm := mul_le_mul_of_nonneg_left hvolume omegaTarget_pos.le
    linarith
  exact hbudget.trans_lt
    ((sourceRankBudget_lt_upper.trans certified_endpoint_slack).trans_le hnumericLower)

end MatrixMultiplication.SimplifiedSharpEndpoint
