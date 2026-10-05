/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedCertificate
import MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor

/-!
# The strict floor-domination bridge of the total-weight track

`MatrixMultiplication/TotalQuotientExponentStageAggregation.lean` ends at

```text
coarseFourFamilyFloor ≤ fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate
```

and this module upgrades that `≤` to `<`.

## Why the non-strict endpoint is not enough

`MatrixMultiplication/SimplifiedSequencePackaging.lean` asks a counting client for

```text
RetainedCountValid retainedFloor cutoff count :
  … ∀ r, cutoff ≤ r → 0 < r → (2 ^ (38 · retainedFloor)) ^ r ≤ count r
```

with `retainedFloor = coarseFourFamilyFloor` — a *loss-free* eventual count.  What a recursive
construction produces instead is a growth statement through an ambient subexponential loss,
`base ^ r ≤ loss r * count r`, and the only theorem that removes the loss is
`Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul`, which needs
`lowerBase < base` **strictly**: its proof spends the gap by absorbing `loss r ≤ (base/lowerBase) ^ r`.
With `base = 2 ^ (38 · fourFamilyExponent …)` and `lowerBase = 2 ^ (38 · coarseFourFamilyFloor)`
the non-strict aggregation endpoint permits `base = lowerBase`, where no cutoff exists at all.
The gap therefore has to be produced at the floor-domination level, and that is exactly what is
proved here.

## Where the strictness comes from, and how much of it there is

Only the level-two stage of the four is backed by a Lean recurrence for this candidate, so it
carries the whole gap; the root, level-four and level-three transfers keep their `≤` hypotheses
unchanged.  `MatrixMultiplication/TotalQuotientExponentLevelTwoStrictFloor.lean` sharpens the
committed rational comparison `commonFloor ≤ Branchᵢ.branchFloor` to `<` on all three branches, and
`AlgebraicComplexity/Analysis/RetainedExponentAggregationStrict.lean` turns one strict summand into
a strict four-family sum.  The bottleneck is branch `2`:

```text
  Branch2.branchFloor − commonFloor
    = 785076174686654464 / 2 ^ 56 − 286008945377 / 31250000000 − 871417 / 500000
    = 1345218400141681 / 4294967296000000000000
    ≈ 3.132080660e-07  >  0
```

**so the exact rational slack witnessing the guaranteed strict gap of `coarseFourFamilyFloor_lt_fourFamilyExponent` is
`1345218400141681 / 4294967296000000000000`**, and the copy-base ratio a client is guaranteed at least (the true gap may be larger) on the
ambient loss is `2 ^ (38 · 3.132080660e-07) ≈ 1.00000825`.  Every other inequality in the chain is
reused verbatim from committed modules; no constant moves, no numerical datum is new, and the
`8.241973` the packaging is pinned at is untouched.

## The certificate this is stated over

The level-two side is discharged at the **compact grouped** certificate
`MatrixMultiplication/TotalQuotientExponentLevelTwoGroupedCertificate.lean`, whose 67-record
sufficient statistic replaces the 1,620 raw edge records: the strict bound transports through its
`branchᵢ_eq_established`, `groupedBranch_normalize` and `activeBranchRate_eq_grouped` with no new
finite reduction and no elaboration-budget override.  The older ungrouped certificate module is
deliberately *not* imported.
-/

namespace MatrixMultiplication.TotalQuotientExponentStrictFloorBridge

open AlgebraicComplexity.RetainedExponentAggregation
open MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo
open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoGroupedBranchTargets
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
open MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedProvenance
open MatrixMultiplication.TotalQuotientExponentLevelTwoGroupedCertificate
open MatrixMultiplication.TotalQuotientExponentLevelTwoStrictFloor

noncomputable section

/-! ## The strict level-two certificate at the compact table pair -/

/-- The stage floor lies **strictly** below the evaluation of every compact normalized target.

Exactly the proof of the grouped certificate's `levelTwoFloor_le_target`, with the three directed
enclosures replaced by their strict analogues. -/
theorem levelTwoFloor_lt_target (coordinate : Fin 3) :
    levelTwoFloor () < Form.eval levelTwoFormBits (certifiedTargets coordinate) := by
  rw [levelTwoFloor_eq_commonFloor]
  fin_cases coordinate
  · change commonFloor < Form.eval levelTwoFormBits branch0
    rw [branch0_eq_established]
    exact commonFloor_lt_branch0
  · change commonFloor < Form.eval levelTwoFormBits branch1
    rw [branch1_eq_established]
    exact commonFloor_lt_branch1
  · change commonFloor < Form.eval levelTwoFormBits branch2
    rw [branch2_eq_established]
    exact commonFloor_lt_branch2

/-- **The compact checker proves the *strict* semantic level-two branch floor.**

The strict analogue of the grouped certificate's `branchFloorCertified`, over the same table pair
and by the same semantic provenance rewrite. -/
theorem branchFloorCertifiedStrict :
    BranchFloorCertifiedStrict certifiedTables certifiedMassThree := by
  intro coordinate
  unfold TotalQuotientExponentLevelTwoRecurrence.branchRate
  rw [activeBranchRate_eq_grouped]
  calc
    levelTwoFloor () < Form.eval levelTwoFormBits (certifiedTargets coordinate) :=
      levelTwoFloor_lt_target coordinate
    _ = Form.eval levelTwoFormBits (inputBranchForm groupedInputs coordinate) := by
      rw [← groupedBranch_normalize coordinate, Form.eval_normalize]

/-- The strict level-two family transfer at the certified table pair, with no hypothesis left. -/
theorem levelTwoFamilyFloor_lt_levelTwoFamilyExponent :
    familyFloor levelTwoFloor <
      familyExponent
        (TotalQuotientExponentLevelTwoRecurrence.familyRate certifiedTables certifiedMassThree) :=
  levelTwoFamilyFloor_lt_familyExponent certifiedTables certifiedMassThree branchFloorCertifiedStrict

/-! ## The strict stage-floor endpoint -/

/-- **Strict stage-floor transfer, hypothesis form.**  The strict analogue of
`TotalQuotientExponentStageAggregation.coarseFourFamilyFloor_le_fourFamilyExponent`: the three
outer stages are dominated as before, the level-two family strictly, and the committed four-family
stage-floor sum `8.241973` is then a *strict* lower bound for the four-family retained exponent.

Same argument order as the non-strict endpoint, so a client upgrades by replacing `hlevelTwo`. -/
theorem coarseFourFamilyFloor_lt_fourFamilyExponent_of_levelTwoStrict
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (levelTwoRate : LevelTwoGroup → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch)
    (hlevelTwo : ∀ group branch, levelTwoFloor group < levelTwoRate group branch) :
    coarseFourFamilyFloor <
      fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate := by
  have hcoarse : coarseFourFamilyFloor =
      fourFamilyFloor rootFloor levelFourFloor levelThreeFloor levelTwoFloor := rfl
  rw [hcoarse]
  exact fourFamilyFloor_lt_fourFamilyExponent_of_levelTwo
    rootRate levelFourRate levelThreeRate levelTwoRate
    rootFloor levelFourFloor levelThreeFloor levelTwoFloor
    hroot hlevelFour hlevelThree hlevelTwo

/-- **The strict floor-domination bridge.**

```text
coarseFourFamilyFloor < fourFamilyExponent rootRate levelFourRate levelThreeRate
  (TotalQuotientExponentLevelTwoRecurrence.familyRate certifiedTables certifiedMassThree)
```

for the concrete four certificate families of the `e7987` total-weight candidate: the level-two
family is the compact grouped certificate's, discharged outright, and only the three outer
componentwise dominations remain as hypotheses — exactly the hypotheses the committed non-strict
endpoint already has.

This is the named public bridge a `RetainedCountValid` client cites: it supplies the strict
`lowerBase < base` that `Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul` needs,
at the packaging's own retained constant `8.241973`, with the exact rational slack witnessing a guaranteed gap of at least
`1345218400141681 / 4294967296000000000000 ≈ 3.132e-07`. -/
theorem coarseFourFamilyFloor_lt_fourFamilyExponent
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch) :
    coarseFourFamilyFloor <
      fourFamilyExponent rootRate levelFourRate levelThreeRate
        (TotalQuotientExponentLevelTwoRecurrence.familyRate certifiedTables certifiedMassThree) :=
  coarseFourFamilyFloor_lt_fourFamilyExponent_of_levelTwoStrict
    rootRate levelFourRate levelThreeRate
    (TotalQuotientExponentLevelTwoRecurrence.familyRate certifiedTables certifiedMassThree)
    hroot hlevelFour hlevelThree fun _ branch ↦ branchFloorCertifiedStrict branch

/-- **The bridge in copy-base form**, which is how a counting client meets
`Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul`'s `lowerBase < base`: the
packaging's retained copy base at any positive stride is strictly below the four-family one.

Instantiate `stride` at `((strideValue : ℕ) : ℝ) = 38` to get literally the two bases of
`SimplifiedSequencePackaging.RetainedCountValid`. -/
theorem retainedCopyBase_lt_fourFamilyCopyBase
    (stride : ℝ) (hstride : 0 < stride)
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch) :
    (2 : ℝ) ^ (stride * coarseFourFamilyFloor) <
      (2 : ℝ) ^ (stride *
        fourFamilyExponent rootRate levelFourRate levelThreeRate
          (TotalQuotientExponentLevelTwoRecurrence.familyRate
            certifiedTables certifiedMassThree)) := by
  refine (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 ?_
  exact mul_lt_mul_of_pos_left
    (coarseFourFamilyFloor_lt_fourFamilyExponent rootRate levelFourRate levelThreeRate
      hroot hlevelFour hlevelThree)
    hstride

end

end MatrixMultiplication.TotalQuotientExponentStrictFloorBridge
