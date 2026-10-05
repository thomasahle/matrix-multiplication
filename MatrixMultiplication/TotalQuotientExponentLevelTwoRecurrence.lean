/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
import MatrixMultiplication.SimplifiedExponentRecurrence

/-!
# Level-two retained-exponent recurrence for the total-weight quotient candidate

The total-weight analogue of `MatrixMultiplication/SimplifiedExponentLevelTwoReconstruction.lean`,
which is the only stage of the sorted-pair per-stage stack that carries a floor all the way to a
semantic retained exponent.

## Why no arithmetic had to be re-derived

The level-two retained rate is the sum, over the geometrically positive level-two edges, of the
occurrence mass times the CW `112` leaf value of the heavy coordinate.  Both factors are read from
the *primary* tables: the occurrence mass is `mass₃ · A₃ · (α₃ + α₃ ∘ complement)` and the leaf
value is the three-symbol edge entropy of `μ`.  Neither factor mentions the complete-split
alphabet, so the level-two stage is **unaffected by the choice of split-word quotient** — the
total-weight quotient `2:1=0|0;2:2=0|0|0;2:3=0|0` acts on depth-two split words, which first enter
the recurrence at level three, where children are convolved into a depth-four parent law.

`MatrixMultiplication.SimplifiedExponentRecurrence.Chunked` is already parametric in
`SimplifiedVolumeReconstruction.PrimaryTables`, so this module is a pure instantiation of the
shared recurrence, and it stays parametric in the tables for the same reason: the same statements
serve the sorted-pair and the total-weight candidate, and no table can silently substitute for
another.

## Provenance and the intended instantiation

The floors this module transfers come from certificate SHA-256
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` with coarsening spec
`2:1=0|0;2:2=0|0|0;2:3=0|0`; the exporter invocation that produced them is recorded in
`better_bound/total_weight_stage_floor_prep.md` §4 and the resulting rationals are committed in
`Generated/TotalQuotientExponentStageFloors.lean`.

The intended arguments are the total-weight primary tables and their cached top-law pushforward:

```
data      := TotalQuotientVolumeReconstruction.primaryTables
massThree := SimplifiedVolumeReconstruction.levelThreeMassNumerators data
```

Those two definitions are **not in the repository yet** — `TotalQuotientVolumeReconstructionBase`
and the `Generated/TotalQuotientPrimary*` families are still uncommitted working-tree artifacts.
Nothing here depends on them; when they land, the instantiation is one `def`.

## The remaining finite obligation

`BranchFloorCertified` isolates the one thing a generated checker still has to supply: that the
certified rational floor is below all three exact branch rates.  `of_normalizedForms` reduces it to
decidable integer form normalizations against exported target forms plus a directed logarithm
bound, exactly as `SimplifiedExponentLevelTwoReconstruction.ExactFormReconstruction` does for the
sorted-pair candidate.  The target forms do not exist for this candidate; the exact missing
artifact and the exporter change that would emit it are recorded in the module documentation of
`MatrixMultiplication/TotalQuotientExponentStageAggregation.lean`.
-/

namespace MatrixMultiplication.TotalQuotientExponentLevelTwoRecurrence

open AlgebraicComplexity
open AlgebraicComplexity.RetainedExponentAggregation
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence

noncomputable section

variable (data : SimplifiedVolumeReconstruction.PrimaryTables) (massThree : Array ℕ)

/-! ## The three exact level-two branches -/

/-- The three exact level-two retained-rate branches over a sparse primary-table family. -/
def branchRate (coordinate : Fin 3) : ℝ :=
  Chunked.activeBranchRateWithMassThree data massThree coordinate

/-- The exact signed-log form of one level-two branch, at the common denominator `2 ^ 56`. -/
def branchForm (coordinate : Fin 3) : Form :=
  Chunked.activeBranchFormWithMassThree data massThree coordinate

theorem branchForm_eval (coordinate : Fin 3) :
    Form.eval levelTwoFormBits (branchForm data massThree coordinate) =
      branchRate data massThree coordinate :=
  Chunked.activeBranchFormWithMassThree_eval data massThree coordinate

/-- Actual level-two bottleneck: the minimum of the three exact branches. -/
def retainedExponent : ℝ :=
  RegionalExponent.threeWayMin (branchRate data massThree)

/-! ## The aggregation interface

`RetainedExponentAggregation` indexes a family by a `Fintype` of groups and a `Fin 3` of branches.
The level-two family of a depth-four recursive certificate is a single group, so its index type is
`Unit` — exactly the `LevelTwoGroup` already used by the committed stage floors. -/

/-- The level-two family rate in the shape `RetainedExponentAggregation` consumes. -/
def familyRate : Generated.TotalQuotientExponentStageFloors.LevelTwoGroup → Fin 3 → ℝ :=
  fun _ ↦ branchRate data massThree

/-- The generic one-group family exponent is the level-two bottleneck. -/
theorem familyExponent_familyRate :
    familyExponent (familyRate data massThree) = retainedExponent data massThree := by
  simp [familyExponent, familyRate, retainedExponent]

/-! ## The remaining finite obligation -/

/-- The one obligation a generated level-two checker must still discharge for this candidate: the
certified rational floor `1.742834` is below all three exact branch rates. -/
def BranchFloorCertified : Prop :=
  ∀ coordinate : Fin 3,
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor () ≤
      branchRate data massThree coordinate

/-- Reduction of the obligation to generated data: three decidable integer form normalizations
against exported target forms, plus a directed logarithm bound on each target.

This is the total-weight analogue of `SimplifiedExponentLevelTwoReconstruction`'s
`ExactFormReconstruction`; the `target` family is what a per-stage Lean emitter would supply. -/
theorem branchFloorCertified_of_normalizedForms
    (target : Fin 3 → Form)
    (hnormalize : ∀ coordinate,
      Form.normalize (branchForm data massThree coordinate) = target coordinate)
    (hfloor : ∀ coordinate,
      Generated.TotalQuotientExponentStageFloors.levelTwoFloor () ≤
        Form.eval levelTwoFormBits (target coordinate)) :
    BranchFloorCertified data massThree := by
  intro coordinate
  rw [← branchForm_eval data massThree coordinate, ← Form.eval_normalize,
    hnormalize coordinate]
  exact hfloor coordinate

/-- **Level-two floor transfer.**  The certified per-stage floor is a lower bound for the level-two
family exponent.  This is the first application of
`RetainedExponentAggregation.familyFloor_le_familyExponent`. -/
theorem levelTwoFamilyFloor_le_familyExponent
    (certificate : BranchFloorCertified data massThree) :
    familyFloor Generated.TotalQuotientExponentStageFloors.levelTwoFloor ≤
      familyExponent (familyRate data massThree) :=
  familyFloor_le_familyExponent (familyRate data massThree)
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor
    fun _ branch ↦ certificate branch

/-- **Inner acceptance floor.**  `433/250 = 1.732`, the inner retained floor of the `C′` split
fixed in `MatrixMultiplication/TotalWeightAcceptanceFloors.lean`, is a lower bound for the exact
level-two family exponent.  Certified margin `1.742834 − 1.732 = 1.083e-02`. -/
theorem innerRetainedFloor_le_familyExponent
    (certificate : BranchFloorCertified data massThree) :
    (433 / 250 : ℝ) ≤ familyExponent (familyRate data massThree) :=
  le_trans Generated.TotalQuotientExponentStageFloors.innerRetainedFloor_le_innerFloor
    (levelTwoFamilyFloor_le_familyExponent data massThree certificate)

/-- The same statement against the concrete level-two bottleneck. -/
theorem innerRetainedFloor_le_retainedExponent
    (certificate : BranchFloorCertified data massThree) :
    (433 / 250 : ℝ) ≤ retainedExponent data massThree := by
  rw [← familyExponent_familyRate]
  exact innerRetainedFloor_le_familyExponent data massThree certificate

end

end MatrixMultiplication.TotalQuotientExponentLevelTwoRecurrence
