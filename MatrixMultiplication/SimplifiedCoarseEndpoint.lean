import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpointValue
import MatrixMultiplication.CurrentProofObligations
import MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors

/-!
# Strong coarse endpoint from the reconstructed family floors

The first formal milestone used the deliberately rounded inequalities `E ≥ 8.2` and
`Mvol ≥ 6.0165`.  The exact coarse reconstruction artifacts already retain more margin:

* `E ≥ 8.200174`, from the four separately rounded exponent families;
* `Mvol > 6.0167`, from the exact three-coordinate volume recurrence.

These values suffice for the stronger rational endpoint `ω < 2.36985`.  This module contains
only the generic endpoint arithmetic; the generated semantic reconstruction and finite extraction
sequence remain explicit hypotheses.

## How the endpoint reaches `omega`

Through the value API, in one step.  The extraction sequence is handed to
`Examples.omega_lt_of_cwPower_borderRankBudget`, the client idiom of the regularization bridge
`AlgebraicComplexity/MatrixMultiplication/LaserVolumeRegularization.lean`: every repetition of the
sequence *is* a CW90 `TauValueCertificate` of `CW₅⁸`, the certified value
`2 ^ (retained + ω·volume)` is bounded by the source's border rank `7⁸`, and the `τ = target/3`
normalization and the strict value-to-exponent step are performed once inside the bridge.

Nothing here solves for `omega` by hand: the module owes only the rational margin
`certified_endpoint_slack` and the two floor comparisons.  In particular neither the rate
interface (`HasLaserExtractionRate`, `CurrentProofObligations.CurrentLaserExtraction`) nor the
feasibility-to-strict step (`FeasibilitySlack.strict_of_feasibility_with_slack`) is used any more,
and positivity of the *volume* is no longer needed — only `0 ≤ omegaTarget`.
-/

namespace MatrixMultiplication.SimplifiedCoarseEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CurrentProofObligations

universe u

/-- Exact assembled retained-exponent floor from the four coarse family certificates. -/
noncomputable abbrev retainedFloor : ℝ :=
  MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors.coarseFourFamilyFloor

/-- Exact rational volume floor supplied by the generated volume recurrence. -/
noncomputable def volumeFloor : ℝ := 60167 / 10000

/-- Strongest five-decimal endpoint supported by the two coarse floors. -/
noncomputable def omegaTarget : ℝ := 236985 / 100000

theorem retainedFloor_eq : retainedFloor = (8200174 / 1000000 : ℝ) :=
  MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors.coarseFourFamilyFloor_eq

theorem volumeFloor_pos : 0 < volumeFloor := by
  norm_num [volumeFloor]

theorem omegaTarget_pos : 0 < omegaTarget := by
  norm_num [omegaTarget]

/-- Exact scalar margin for `2.36985`; its value over the directed source-cost upper bound is
`277963479 / 25000000000000`. -/
theorem certified_endpoint_slack :
    MatrixMultiplication.LogBounds.rankBudgetUpper <
      retainedFloor + omegaTarget * volumeFloor := by
  rw [retainedFloor_eq]
  norm_num [MatrixMultiplication.LogBounds.rankBudgetUpper, omegaTarget, volumeFloor]

/-- The semantic lower-bound interface consumed by the coarse endpoint. -/
def Reconstruction (retained volume : ℝ) : Prop :=
  retainedFloor ≤ retained ∧ volumeFloor ≤ volume

/-- A fully semantic extraction sequence meeting the exact coarse floors implies
`omega < 2.36985`.

The whole tensor-side argument is `Examples.omega_lt_of_cwPower_borderRankBudget` at `q = 5`,
`power = 8`; what remains is rational: raise the two floors to the hypothesized exponents and read
the source budget `sourceRankBudget = 8·log₂ 7` in the bit coordinates the bridge expects. -/
theorem omega_lt_236985_of_subexponentialVolumeSequence
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : Reconstruction retained volume) :
    omega K < omegaTarget := by
  obtain ⟨hretained, hvolume⟩ := hreconstruct
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

end MatrixMultiplication.SimplifiedCoarseEndpoint
