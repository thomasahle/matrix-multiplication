/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpointValue
import AlgebraicComplexity.MatrixMultiplication.LaserVolumeMonotone
import MatrixMultiplication.CurrentProofObligations

set_option autoImplicit false

/-!
# The `C′` acceptance floors for the volume-only `2.36999` endpoint

This module fixes the three exact rational floors — and the stride — at which the volume-only
total-weight candidate (`CW₅⁸`, depth 4, certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`) is *accepted*, and proves the
endpoint theorem they support.

## The floor triple

The numeric preparation pass recorded in `better_bound/total_weight_stage_floor_prep.md` fixed the
split labelled `C′` there:

| quantity | value | margin against the certified per-stage floors |
| --- | --- | --- |
| `outerRetainedFloor` | `811/125 = 6.488` | `1.114e-02` |
| `innerRetainedFloor` | `433/250 = 1.732` | `1.083e-02` |
| `retainedFloor` | `411/50 = 8.22` (their sum) | — |
| `volumeFloor` | `15021/2500 = 6.0084` | `7.03e-04` |
| endpoint slack | `25213488479/25000000000000 ≈ 1.008e-03` | — |

The certified per-stage floors that dominate the two retained numbers are proved in
`Generated/TotalQuotientExponentStageFloors.lean`.

## Why the stride is `38`

`SubexponentialLaserVolumeSequence.volume_growth` demands
`2 ^ (3 * stride * volumeFloor * r) ≤ xSize r * ySize r * zSize r` for **every** `r > 0`, and for
`CW_q` a leaf's side-length product is `q ^ m` where `m` counts the one-type letters of the stride
block.  For `q = 5` and a stride block of `8 * stride` letters this is the grid condition

`m * log₂ 5 ≥ 3 * stride * volumeFloor`,  `m ∈ ℤ`,  `m ≤ 8 * stride`,

whose achievable mean volumes are `m * log₂ 5 / (3 * stride)`.  At `stride = 2` the entire interval
`(5.80482, 6.19181)` is unreachable, so the frequently quoted stride `2` is *impossible* for any
choice of the three floors.  The smallest admissible stride is the least `s` with
`⌊s * 7.76393878⌋ * log₂ 5 ≥ 3 * s * volumeFloor`; at `volumeFloor = 15021/2500` that is `38`
(the ceiling reachable at stride `38` is `6.00849814`, comfortably above `6.0084`).  `C′` is
precisely the largest volume floor whose minimum stride is still `38`; the previously hard-coded
floor `3755689/625000` would have required stride `3067`.

The integrality analysis lives in §5 of the preparation document; this module records only its
conclusion, since the endpoint theorem takes the extraction sequence as a hypothesis and therefore
does not itself need to exhibit the leaf profile.

## How the endpoint reaches `omega`

Through the value API, in one step.  The extraction sequence is handed to
`Examples.omega_lt_of_cwPower_borderRankBudget`, the client idiom of the regularization bridge
`AlgebraicComplexity/MatrixMultiplication/LaserVolumeRegularization.lean`: every repetition of the
sequence *is* a CW90 `TauValueCertificate` of `CW₅⁸`, the certified value
`2 ^ (retainedFloor + ω·volumeFloor)` is bounded by the source's border rank `7⁸`, and the
`τ = target/3` normalization and the strict value-to-exponent step happen once inside the bridge.

## Local restatements

Nothing is restated here.  The border-rank budget (`LogBounds.rankBudgetUpper`,
`CurrentProofObligations.sourceRankBudget`), Schönhage's inequality, and the regularization bridge
are all imported from committed modules.  The feasibility-to-strict-bound step
`FeasibilitySlack.strict_of_feasibility_with_slack` and the laser *rate* interface
(`CurrentProofObligations.CurrentLaserExtraction`) are no longer used by this module at all.

Deliberately **not** imported: `MatrixMultiplication/TotalWeightVolumeEndpoint.lean`, whose
constants this module supersedes.
-/

namespace MatrixMultiplication.TotalWeightAcceptanceFloors

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor

universe u

/-! ## The exact rational constants -/

/-- Exact rational target represented by the decimal `2.36999`. -/
noncomputable def acceptanceTarget : ℝ := 236999 / 100000

/-- Outer (root + level-4 + level-3) retained floor of the `C′` split: `6.488`. -/
noncomputable def outerRetainedFloor : ℝ := 811 / 125

/-- Inner (level-2) retained floor of the `C′` split: `1.732`. -/
noncomputable def innerRetainedFloor : ℝ := 433 / 250

/-- Total retained floor of the `C′` split: `8.22`. -/
noncomputable def retainedFloor : ℝ := 411 / 50

/-- Mean rectangular-volume floor of the `C′` split: `6.0084`.

This is the largest volume floor whose minimal admissible stride is `38`; see the module
documentation for the integrality derivation. -/
noncomputable def volumeFloor : ℝ := 15021 / 2500

/-- The stride at which the `C′` floors are realizable.

Fixed by the leaf-dimension integrality condition `⌊s * 7.76393878⌋ * log₂ 5 ≥ 3 * s * volumeFloor`
of `better_bound/total_weight_stage_floor_prep.md` §5; stride `2` is provably impossible. -/
def strideValue : ℕ := 38

/-! ## Elementary arithmetic facts -/

/-- The `C′` split is exact: `811/125 + 433/250 = 2055/250 = 411/50`. -/
theorem retainedFloor_eq_outer_add_inner :
    retainedFloor = outerRetainedFloor + innerRetainedFloor := by
  norm_num [retainedFloor, outerRetainedFloor, innerRetainedFloor]

theorem acceptanceTarget_pos : 0 < acceptanceTarget := by norm_num [acceptanceTarget]

theorem outerRetainedFloor_pos : 0 < outerRetainedFloor := by norm_num [outerRetainedFloor]

theorem innerRetainedFloor_pos : 0 < innerRetainedFloor := by norm_num [innerRetainedFloor]

theorem retainedFloor_pos : 0 < retainedFloor := by norm_num [retainedFloor]

theorem volumeFloor_pos : 0 < volumeFloor := by norm_num [volumeFloor]

theorem strideValue_pos : 0 < strideValue := by norm_num [strideValue]

/-- The stride, viewed as a real number. -/
theorem strideValue_cast : ((strideValue : ℕ) : ℝ) = (38 : ℝ) := by
  norm_num [strideValue]

/-! ## The endpoint slack -/

/-- Pure rational arithmetic for the `C′` acceptance endpoint.  The exact gap over the printed
rank-budget upper endpoint is `25213488479 / 25000000000000 ≈ 1.008e-03`. -/
theorem certified_acceptance_slack :
    LogBounds.rankBudgetUpper < retainedFloor + acceptanceTarget * volumeFloor := by
  norm_num [LogBounds.rankBudgetUpper, retainedFloor, acceptanceTarget, volumeFloor]

/-- Chained with the proved logarithm enclosure `sourceRankBudget < rankBudgetUpper`: the exact
border-rank budget of `CW₅⁸` lies strictly below the `C′` acceptance value. -/
theorem sourceRankBudget_lt_acceptance_endpoint :
    CurrentProofObligations.sourceRankBudget <
      retainedFloor + acceptanceTarget * volumeFloor :=
  CurrentProofObligations.sourceRankBudget_lt_upper.trans certified_acceptance_slack

/-! ## The acceptance endpoint -/

/-- **Acceptance endpoint.**  A stride-`38` subexponential volume extraction sequence for `CW₅⁸`
that realizes the `C′` copy base `2 ^ (38 * 8.22)` and the `C′` volume base `2 ^ (3 * 38 * 6.0084)`
gives `omega K < 2.36999`.

Only the extraction sequence is hypothetical: the border-rank budget, Schönhage's asymptotic sum
inequality, the logarithm enclosure, and the rational slack are all proved.

The only step that is not the bridge itself is putting the sequence into the bridge's
stride coordinates, where the literal `38` of the statement becomes `((strideValue : ℕ) : ℝ)`. -/
theorem omega_lt_236999_of_subexponentialVolumeSequence_acceptance
    (K : Type u) [Field K]
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) strideValue
      ((2 : ℝ) ^ ((38 : ℝ) * retainedFloor))
      ((2 : ℝ) ^ (3 * (38 : ℝ) * volumeFloor))) :
    omega K < acceptanceTarget := by
  have hseq : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) strideValue
      ((2 : ℝ) ^ (((strideValue : ℕ) : ℝ) * retainedFloor))
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volumeFloor)) := by
    rw [strideValue_cast]
    exact hextractions
  refine omega_lt_of_cwPower_borderRankBudget K 5 8 acceptanceTarget_pos.le hseq ?_
  have hbudget :
      ((8 : ℕ) : ℝ) * Real.log (((5 : ℕ) : ℝ) + 2) / Real.log 2 =
        CurrentProofObligations.sourceRankBudget := by
    rw [CurrentProofObligations.sourceRankBudget, show (((5 : ℕ) : ℝ) + 2) = 7 by norm_num]
    push_cast
    ring
  exact hbudget.trans_lt sourceRankBudget_lt_acceptance_endpoint

/-- Split form of the acceptance endpoint, taking the outer and inner retained floors separately.

This is the shape the two-stage (outer constituent / inner level-2) constructions naturally emit:
the copy base is the product `2 ^ (38 * outer) * 2 ^ (38 * inner)` written additively in the
exponent.  Since `38 * 6.488 + 38 * 1.732 = 38 * 8.22` exactly, no inequality is lost. -/
theorem omega_lt_236999_of_subexponentialVolumeSequence_acceptance_split
    (K : Type u) [Field K]
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) strideValue
      ((2 : ℝ) ^ ((38 : ℝ) * outerRetainedFloor + (38 : ℝ) * innerRetainedFloor))
      ((2 : ℝ) ^ (3 * (38 : ℝ) * volumeFloor))) :
    omega K < acceptanceTarget := by
  have hsplit :
      (38 : ℝ) * outerRetainedFloor + (38 : ℝ) * innerRetainedFloor
        = (38 : ℝ) * retainedFloor := by
    norm_num [outerRetainedFloor, innerRetainedFloor, retainedFloor]
  rw [hsplit] at hextractions
  exact omega_lt_236999_of_subexponentialVolumeSequence_acceptance K hextractions

/-- Monotone form of the acceptance endpoint.

A concrete construction rarely realizes the certificate bases on the nose: it emits a natural
number or a quotient of certificate counts that merely *dominates* them.  This form consumes any
such sequence and weakens it with
`SubexponentialLaserVolumeSequence.mono_copyBase`/`mono_volumeBase`. -/
theorem omega_lt_236999_of_subexponentialVolumeSequence_acceptance_of_le
    (K : Type u) [Field K] {copyBase volumeBase : ℝ}
    (hcopy : (2 : ℝ) ^ ((38 : ℝ) * retainedFloor) ≤ copyBase)
    (hvolume : (2 : ℝ) ^ (3 * (38 : ℝ) * volumeFloor) ≤ volumeBase)
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) strideValue copyBase volumeBase) :
    omega K < acceptanceTarget :=
  omega_lt_236999_of_subexponentialVolumeSequence_acceptance K
    (hextractions.mono (by positivity) hcopy (by positivity) hvolume)

end MatrixMultiplication.TotalWeightAcceptanceFloors
