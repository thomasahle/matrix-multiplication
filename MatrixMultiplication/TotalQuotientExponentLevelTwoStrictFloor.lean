/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.RetainedExponentAggregationStrict
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoData
import MatrixMultiplication.TotalQuotientExponentLevelTwoRecurrence

/-!
# The level-two floor is *strictly* below every exact branch rate

`MatrixMultiplication/TotalQuotientExponentLevelTwoRecurrence.lean` isolates the inner obligation
`BranchFloorCertified`: the certified rational floor `1.742834` is below all three exact level-two
branch rates.  This module proves the same statement with `<` in place of `≤`, from the *same*
committed rational data and with no new certificate.

## Why the strict form is worth a module

The strictness is what a copy-growth client spends to absorb a subexponential loss: see
`AlgebraicComplexity/Analysis/RetainedExponentAggregationStrict.lean` for the exact shape of the
gap, and `MatrixMultiplication/TotalQuotientExponentStrictFloorBridge.lean` for the four-family
endpoint this feeds.  Level two is the only one of the four recursive stages that has a Lean
recurrence for this candidate, so it is where the strict margin has to come from; the other three
stages keep their `≤` transfers untouched.

## The margin is already in the committed bytes

`Generated/TotalQuotientExponentLevelTwoData.lean` proves `commonFloor ≤ Form.eval …` for the three
exported branch targets by composing an exact rational comparison `commonFloor ≤ Branchᵢ.branchFloor`
with the generated directed bound `Branchᵢ.branchFloor ≤ Form.eval …`.  The first step is a
comparison of two integer-literal rationals, and in the committed data it is **never an equality**:

| branch | `Branchᵢ.branchFloor` (exact) | `branchFloor − commonFloor` |
| --- | --- | --- |
| 0 | `7487650201869119857943 / 4294967296000000000000` | `2235169512255857943 / 4294967296000000000000 ≈ 5.204159562e-04` |
| 1 | `3743223290984282204577 / 2147483648000000000000` | `515774805850204577 / 2147483648000000000000 ≈ 2.401763601e-04` |
| 2 | `7485416377575264141681 / 4294967296000000000000` | `1345218400141681 / 4294967296000000000000 ≈ 3.132080660e-07` |

(`Branchᵢ.branchFloor = constantNumeratorᵢ / 2 ^ 56 − ceilingᵢ`, all four integers committed;
`commonFloor = 871417 / 500000`.)  Branch `2` is the bottleneck, so **the exact strict margin this
module contributes is `1345218400141681 / 4294967296000000000000 ≈ 3.132e-07`**, and the three
`norm_num` calls below are the same literal arithmetic the committed non-strict proofs already run.

Nothing here re-elaborates a finite reduction: the compact normalizations and the semantic
provenance stay in `MatrixMultiplication/TotalQuotientExponentLevelTwoGroupedCertificate.lean` and
are consumed, unchanged, one module downstream in
`MatrixMultiplication/TotalQuotientExponentStrictFloorBridge.lean`.  This module is deliberately
certificate-agnostic — it fixes neither the table pair nor the exported targets — so the strict
obligation can be discharged by the compact grouped checker without the ungrouped edge cone.
-/

namespace MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor

open AlgebraicComplexity
open AlgebraicComplexity.RetainedExponentAggregation
open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence

noncomputable section

/-! ## The three strict branch comparisons

Exact strict analogues of `Generated.TotalQuotientExponentLevelTwo.commonFloor_le_branchᵢ`, with
the same two-step proof and the same simp set: an integer-literal comparison against the directed
floor, then the generated directed bound.  Only the first step changes, from `≤` to `<`. -/

/-- The emitted common floor is *strictly* below exported branch `0`; rational margin
`2235169512255857943 / 4294967296000000000000 ≈ 5.204e-04`. -/
theorem commonFloor_lt_branch0 :
    commonFloor < Form.eval Branch0.bits Branch0.expectedForm := by
  apply lt_of_lt_of_le (b := Branch0.branchFloor)
  · norm_num [commonFloor, Branch0.branchFloor, Branch0.constantNumerator,
      Branch0.bits, Branch0.ceiling]
  · exact Branch0.branchFloor_le_expectedForm_eval

/-- The emitted common floor is *strictly* below exported branch `1`; rational margin
`515774805850204577 / 2147483648000000000000 ≈ 2.402e-04`. -/
theorem commonFloor_lt_branch1 :
    commonFloor < Form.eval Branch1.bits Branch1.expectedForm := by
  apply lt_of_lt_of_le (b := Branch1.branchFloor)
  · norm_num [commonFloor, Branch1.branchFloor, Branch1.constantNumerator,
      Branch1.bits, Branch1.ceiling]
  · exact Branch1.branchFloor_le_expectedForm_eval

/-- The emitted common floor is *strictly* below exported branch `2`.  This is the bottleneck of
the level-two stage: rational margin `1345218400141681 / 4294967296000000000000 ≈ 3.132e-07`, and
therefore the exact strictness the four-family bridge runs on. -/
theorem commonFloor_lt_branch2 :
    commonFloor < Form.eval Branch2.bits Branch2.expectedForm := by
  apply lt_of_lt_of_le (b := Branch2.branchFloor)
  · norm_num [commonFloor, Branch2.branchFloor, Branch2.constantNumerator,
      Branch2.bits, Branch2.ceiling]
  · exact Branch2.branchFloor_le_expectedForm_eval

/-! ## The strict obligation and its reduction -/

variable (data : SimplifiedVolumeReconstruction.PrimaryTables) (massThree : Array ℕ)

/-- The strict analogue of `TotalQuotientExponentLevelTwoRecurrence.BranchFloorCertified`: the
certified rational floor `1.742834` is **strictly** below all three exact branch rates. -/
def BranchFloorCertifiedStrict : Prop :=
  ∀ coordinate : Fin 3,
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor () <
      TotalQuotientExponentLevelTwoRecurrence.branchRate data massThree coordinate

/-- The strict certificate is at least as strong as the committed one, so a client never needs
both.  -/
theorem branchFloorCertified_of_strict
    (certificate : BranchFloorCertifiedStrict data massThree) :
    TotalQuotientExponentLevelTwoRecurrence.BranchFloorCertified data massThree :=
  fun coordinate ↦ (certificate coordinate).le

/-- Reduction of the strict obligation to generated data, verbatim the committed
`branchFloorCertified_of_normalizedForms` with its floor hypothesis strengthened to `<`: the same
three decidable integer form normalizations, and a *strict* directed logarithm bound on each
target. -/
theorem branchFloorCertifiedStrict_of_normalizedForms
    (target : Fin 3 → Form)
    (hnormalize : ∀ coordinate,
      Form.normalize
          (TotalQuotientExponentLevelTwoRecurrence.branchForm data massThree coordinate) =
        target coordinate)
    (hfloor : ∀ coordinate,
      Generated.TotalQuotientExponentStageFloors.levelTwoFloor () <
        Form.eval levelTwoFormBits (target coordinate)) :
    BranchFloorCertifiedStrict data massThree := by
  intro coordinate
  rw [← TotalQuotientExponentLevelTwoRecurrence.branchForm_eval data massThree coordinate,
    ← Form.eval_normalize, hnormalize coordinate]
  exact hfloor coordinate

/-! ## The strict level-two family transfer -/

/-- **Strict level-two floor transfer.**  The certified per-stage floor is a *strict* lower bound
for the level-two family exponent.

The level-two family of a depth-four recursive certificate is the single group `Unit`, which is the
`Nonempty` instance `familyFloor_lt_familyExponent` needs; over an empty family no strict transfer
could exist. -/
theorem levelTwoFamilyFloor_lt_familyExponent
    (certificate : BranchFloorCertifiedStrict data massThree) :
    familyFloor Generated.TotalQuotientExponentStageFloors.levelTwoFloor <
      familyExponent (TotalQuotientExponentLevelTwoRecurrence.familyRate data massThree) :=
  familyFloor_lt_familyExponent
    (TotalQuotientExponentLevelTwoRecurrence.familyRate data massThree)
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor
    fun _ branch ↦ certificate branch

/-- The same transfer against the concrete level-two bottleneck. -/
theorem levelTwoFloor_lt_retainedExponent
    (certificate : BranchFloorCertifiedStrict data massThree) :
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor () <
      TotalQuotientExponentLevelTwoRecurrence.retainedExponent data massThree :=
  lt_threeWayMin certificate

end

end MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor
