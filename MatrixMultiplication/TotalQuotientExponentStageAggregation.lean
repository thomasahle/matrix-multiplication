/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentRecursiveConstituent
import MatrixMultiplication.TotalQuotientExponentLevelTwoRecurrence
import MatrixMultiplication.TotalWeightAcceptanceFloors

/-!
# From the certified per-stage floors to the retained family exponents

This module is the first client of `AlgebraicComplexity/Analysis/RetainedExponentAggregation.lean`.
It carries the committed per-stage rational floors of
`Generated/TotalQuotientExponentStageFloors.lean` across to the *semantic* retained exponents —
the summed three-way bottlenecks that a copy-growth construction must eventually meet — for the
volume-only total-weight candidate (`CW₅⁸`, depth 4, certificate SHA-256
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`, coarsening spec
`2:1=0|0;2:2=0|0|0;2:3=0|0`, exporter invocation in
`better_bound/total_weight_stage_floor_prep.md` §4).

## The two shapes that had to be matched

`RetainedExponentAggregation` indexes a retained family by a `Fintype` of groups and a `Fin 3` of
directional branches, and sums `threeWayMin` over the groups.  The recursive-constituent machinery
of `MatrixMultiplication/SimplifiedExponentRecursiveConstituent.lean` instead sums
`weightedFamilyRetainedExponent` — itself a `threeWayMin` — over a region type.  These are the same
expression up to eta, so `regionalRetainedExponent_eq_familyExponent` below is `rfl`: **no
adjustment to the aggregation theorems was needed and none was made**, and their hypotheses are
used at full strength.

The only interface observation worth recording is that the aggregator has no notion of a *stage
split*.  The `C′` acceptance split of `MatrixMultiplication/TotalWeightAcceptanceFloors.lean`
groups root, level four, and level three into one "outer" floor and keeps level two as the "inner"
floor, whereas `fourFamilyExponent` bundles all four families symmetrically.  The outer statement
is therefore phrased as a sum of three `familyExponent`s rather than through `fourFamilyExponent`;
`outer_add_inner_le_fourFamilyExponent` records that the two phrasings agree exactly.

## What is proved unconditionally, and what is not

Unconditional: the shape identification, and the *transfer* theorems — given per-group,
per-branch domination of the certified floors, the acceptance floors `811/125` (outer) and
`433/250` (inner) are lower bounds for the corresponding family exponents, and `411/50 = 8.22` is
a strict lower bound for the four-family exponent.

Hypothetical: the per-group, per-branch domination itself, for all four stages.  Discharging it
needs generated directed-logarithm certificates per region, and the total-weight candidate has
none.  This is the same gap the sorted-pair candidate has: `SimplifiedExponentCoarseFloors.lean`
already says that "separate generated reconstruction modules must prove that each floor is below
all three semantic branch rates", and those modules were never written for it either.  Level two is
the single exception on the sorted-pair side (`SimplifiedExponentLevelTwoReconstruction.lean`), and
`MatrixMultiplication/TotalQuotientExponentLevelTwoRecurrence.lean` is its total-weight analogue.

## The exact missing artifacts

1. **Per-stage directed-log certificates.**  `better_bound/total_weight_stage_floor_prep.md` §4
   records that the exponent exporter has *no per-stage Lean emitter*: `write_lean_modules` emits
   only the aggregate compressed floor (`Generated/TotalQuotientExponentScalarData.lean`), and the
   per-region floors live only in `better_bound/total_weight_exponent_stage_floors.json`.  The
   `--level2-lean-output` / `--level2-recurrence-lean-output` switches do emit the level-two
   payload, but use the supplied path only for the *directory*: the emitted files keep the
   hard-coded `SimplifiedExponentLevelTwo*` stems and namespaces.  The exporter command that
   produces that payload for this candidate is

   ```
   cd better_bound
   python3.12 export_simplified_exponent_scalar.py \
     --certificate <repo>/better_bound/sorted_pair_volume_certificate.npz \
     --coarsening-spec '2:1=0|0;2:2=0|0|0;2:3=0|0' \
     --compression-bits 11 \
     --retained-floor 82419803/10000000 \
     --level2-floor 433/250 \
     --output <out>/total_weight_exponent_scalar.json \
     --lean-output <out>/TotalQuotientExponentScalarData.lean \
     --scalar-lean-family TotalQuotientExponentScalar \
     --level2-lean-output <out>/TotalQuotientExponentLevelTwoData.lean \
     --level2-recurrence-lean-output <out>/TotalQuotientExponentLevelTwoRecurrenceData.lean
   ```

   (`--compression-bits 11` is required; the module default `6` reproduces only
   `8.24179759280781` instead of the published `directed_compressed_lower_value =
   8.24198033029317`.)  What is missing is a `--level2-lean-family` switch mirroring the existing
   `--scalar-lean-family`, so that the emitted stems and namespaces become
   `TotalQuotientExponentLevelTwo*`.  With that, the `target` family of
   `TotalQuotientExponentLevelTwoRecurrence.branchFloorCertified_of_normalizedForms` is supplied
   and the inner side becomes unconditional.

2. **The primary tables themselves.**  The level-two transfer here is stated for an arbitrary
   `PrimaryTables` precisely because the total-weight tables (`Generated/TotalQuotientPrimary*`)
   and their `PrimaryTables` binding (`TotalQuotientVolumeReconstructionBase`) are not committed to
   the repository.

3. **Outer-stage recurrences.**  A total-weight level-three or level-four recurrence would be the
   sorted-pair one with the depth-two pushforward replaced by the total-weight quotient of
   `TotalQuotientCompleteSplitRecurrence` (also uncommitted, and at the time of writing not
   compiling against the in-flight `cwSplitWordTotalDigit` refactor).  Beyond that, the per-region
   coordinate orders and per-node positive integer dual factors (`CoordinateOrder`, `DualWeights`)
   are optimizer output that has never been exported for this candidate, and no level-four
   recurrence exists for either candidate in committed form.

## Distance to the copy-growth field

`AlgebraicComplexity/MatrixMultiplication/NestedLaserVolume.lean` asks a sequence for
`outer_copy_growth : ∀ r, 0 < r → outerBase ^ r ≤ loss r * (count r : ℝ)` with
`outerBase = 2 ^ (38 * outerRetainedFloor)`.  The theorems here bound a *retained exponent* — a sum
of entropy bottlenecks — not a hash-bucket count, so an entropy-to-count step (the counting
arguments of `AlgebraicComplexity/Combinatorics/AggregateMarkedHashing.lean` and its relatives)
still separates them.  Nothing in this module asserts anything about a tensor.
-/

namespace MatrixMultiplication.TotalQuotientExponentStageAggregation

open AlgebraicComplexity.RetainedExponentAggregation
open MatrixMultiplication.Generated.TotalQuotientExponentStageFloors

noncomputable section

/-! ## Shape identification -/

/-- The recursive-constituent regional retained exponent *is* the aggregator's generic family
exponent, at the branch-rate family of the same regions.  Both sides sum a three-way bottleneck
over the region type, so the equality is definitional up to eta.

This is the adapter that lets any future root, level-four, or level-three total-weight recurrence
feed the transfer theorems below. -/
theorem regionalRetainedExponent_eq_familyExponent {Region : Type*} [Fintype Region]
    {coordinateCount : ℕ} (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : Region →
      List (SimplifiedExponentRecursiveConstituent.WeightedLocalRows coordinateCount)) :
    SimplifiedExponentRecursiveConstituent.regionalRetainedExponent
        outerBits referenceBits compatibilityExtraBits entries =
      familyExponent (fun region branch ↦
        SimplifiedExponentRecursiveConstituent.weightedFamilyBranchRate
          outerBits referenceBits compatibilityExtraBits (entries region) branch) :=
  rfl

/-- The same identification for the root stage, whose family is assembled from `RootRows` rather
than from weighted local constituents. -/
theorem rootFamilyRetainedExponent_eq_familyExponent
    {A X Y Z : Type*} {Root : Type*} [Fintype Root]
    (topBits childBits : ℕ) (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : Root → SimplifiedExponentRootRecurrence.RootRows A X Y Z) :
    SimplifiedExponentRootRecurrence.rootFamilyRetainedExponent
        topBits childBits coordX coordY coordZ rows =
      familyExponent (fun root branch ↦
        SimplifiedExponentRootRecurrence.rootBranchRate topBits childBits
          coordX coordY coordZ (rows root) branch) :=
  rfl

/-! ## Transfer of the outer acceptance floor -/

/-- **Outer floor transfer.**  If each certified per-region floor of the root, level-four, and
level-three stages is below all three directional branch rates of its region, then the outer
acceptance floor `811/125 = 6.488` of the `C′` split is a lower bound for the summed retained
exponents of those three stages.

First application of `RetainedExponentAggregation.familyFloor_le_familyExponent`; the certified
margin is `6.499139 − 6.488 = 1.114e-02`. -/
theorem outerRetainedFloor_le_outerFamilyExponent
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch) :
    TotalWeightAcceptanceFloors.outerRetainedFloor ≤
      familyExponent rootRate + familyExponent levelFourRate + familyExponent levelThreeRate := by
  have hr := familyFloor_le_familyExponent rootRate rootFloor hroot
  have h4 := familyFloor_le_familyExponent levelFourRate levelFourFloor hlevelFour
  have h3 := familyFloor_le_familyExponent levelThreeRate levelThreeFloor hlevelThree
  have hfloor : TotalWeightAcceptanceFloors.outerRetainedFloor ≤ outerFloor :=
    outerRetainedFloor_le_outerFloor
  have houter : outerFloor =
      familyFloor rootFloor + familyFloor levelFourFloor + familyFloor levelThreeFloor := rfl
  rw [houter] at hfloor
  linarith

/-! ## Transfer of the inner acceptance floor

The inner stage is the only one whose semantic rate is quotient-independent, hence already
available from the shared primary-table recurrence; see
`MatrixMultiplication/TotalQuotientExponentLevelTwoRecurrence.lean`. -/

/-- **Inner floor transfer.**  The inner acceptance floor `433/250 = 1.732` is a lower bound for
the exact level-two family exponent, given the one remaining finite branch-floor certificate.
Certified margin `1.742834 − 1.732 = 1.083e-02`. -/
theorem innerRetainedFloor_le_levelTwoFamilyExponent
    (data : SimplifiedVolumeReconstruction.PrimaryTables) (massThree : Array ℕ)
    (certificate :
      TotalQuotientExponentLevelTwoRecurrence.BranchFloorCertified data massThree) :
    TotalWeightAcceptanceFloors.innerRetainedFloor ≤
      familyExponent (TotalQuotientExponentLevelTwoRecurrence.familyRate data massThree) :=
  TotalQuotientExponentLevelTwoRecurrence.innerRetainedFloor_le_familyExponent
    data massThree certificate

/-! ## The four-family endpoint -/

/-- **Four-family transfer.**  Componentwise domination of the certified per-stage floors makes the
`C′` retained floor `411/50 = 8.22` a *strict* lower bound for the four-family retained exponent.

First application of `RetainedExponentAggregation.fourFamilyFloor_le_fourFamilyExponent`.
Strictness comes from the committed arithmetic `8.22 < 8.241973` of
`Generated/TotalQuotientExponentStageFloors.retainedFloor_lt_coarseFourFamilyFloor`. -/
theorem retainedFloor_lt_fourFamilyExponent
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (levelTwoRate : LevelTwoGroup → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch)
    (hlevelTwo : ∀ group branch, levelTwoFloor group ≤ levelTwoRate group branch) :
    TotalWeightAcceptanceFloors.retainedFloor <
      fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate := by
  have haggregate := fourFamilyFloor_le_fourFamilyExponent
    rootRate levelFourRate levelThreeRate levelTwoRate
    rootFloor levelFourFloor levelThreeFloor levelTwoFloor
    hroot hlevelFour hlevelThree hlevelTwo
  have hfloor : TotalWeightAcceptanceFloors.retainedFloor < coarseFourFamilyFloor :=
    retainedFloor_lt_coarseFourFamilyFloor
  have hcoarse : coarseFourFamilyFloor =
      fourFamilyFloor rootFloor levelFourFloor levelThreeFloor levelTwoFloor := rfl
  rw [hcoarse] at hfloor
  linarith

/-- The four-family endpoint with the level-two side discharged to its concrete recurrence, so only
the three outer stages remain hypothetical. -/
theorem retainedFloor_lt_fourFamilyExponent_of_levelTwoCertificate
    (data : SimplifiedVolumeReconstruction.PrimaryTables) (massThree : Array ℕ)
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch)
    (certificate :
      TotalQuotientExponentLevelTwoRecurrence.BranchFloorCertified data massThree) :
    TotalWeightAcceptanceFloors.retainedFloor <
      fourFamilyExponent rootRate levelFourRate levelThreeRate
        (TotalQuotientExponentLevelTwoRecurrence.familyRate data massThree) :=
  retainedFloor_lt_fourFamilyExponent rootRate levelFourRate levelThreeRate
    (TotalQuotientExponentLevelTwoRecurrence.familyRate data massThree)
    hroot hlevelFour hlevelThree fun _ branch ↦ certificate branch

/-- The `C′` stage split loses nothing: the outer and inner statements add up to the four-family
one. -/
theorem outer_add_inner_le_fourFamilyExponent
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (levelTwoRate : LevelTwoGroup → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch)
    (hlevelTwo : ∀ group branch, levelTwoFloor group ≤ levelTwoRate group branch) :
    TotalWeightAcceptanceFloors.outerRetainedFloor +
        TotalWeightAcceptanceFloors.innerRetainedFloor ≤
      fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate := by
  have houter := outerRetainedFloor_le_outerFamilyExponent
    rootRate levelFourRate levelThreeRate hroot hlevelFour hlevelThree
  have hinner : TotalWeightAcceptanceFloors.innerRetainedFloor ≤
      familyExponent levelTwoRate :=
    le_trans innerRetainedFloor_le_innerFloor
      (familyFloor_le_familyExponent levelTwoRate levelTwoFloor hlevelTwo)
  have hsum : fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate =
      familyExponent rootRate + familyExponent levelFourRate + familyExponent levelThreeRate +
        familyExponent levelTwoRate := rfl
  rw [hsum]
  linarith

/-! ## The stage-floor endpoint

The four transfers above are pinned at the `C′` acceptance split.  The volume-only `2.36999`
track needs the same transfer at the *committed stage-floor sum itself*, which is a strictly larger
floor than the split and the only one that clears at the realized mean rectangular volume `6`. -/

/-- **Stage-floor transfer.**  Componentwise domination of the certified per-stage floors makes the
committed four-family stage-floor sum `coarseFourFamilyFloor = 8.241973` a lower bound for the
four-family retained exponent.

`MatrixMultiplication/SimplifiedSequencePackaging.retainedFloor` is *defined* as this same
`Generated/TotalQuotientExponentStageFloors` constant, so this conclusion is exactly the retained
bound that track consumes; no restatement in the packaging vocabulary, and no import edge, is
needed.  Prefer it to `retainedFloor_lt_fourFamilyExponent` above, which is pinned at the
acceptance floor `411/50 = 8.22` and therefore throws away the `2.1973e-02` that separates the two
constants — a margin the mean volume `6` does not leave available.

Second application of `RetainedExponentAggregation.fourFamilyFloor_le_fourFamilyExponent`,
composed with the same definitional unfolding of `coarseFourFamilyFloor` used above.  Nothing here
is strict and nothing here is certificate arithmetic: the hypotheses are the four per-stage
semantic identifications, and this theorem is only their sum. -/
theorem coarseFourFamilyFloor_le_fourFamilyExponent
    (rootRate levelFourRate levelThreeRate : Region → Fin 3 → ℝ)
    (levelTwoRate : LevelTwoGroup → Fin 3 → ℝ)
    (hroot : ∀ region branch, rootFloor region ≤ rootRate region branch)
    (hlevelFour : ∀ region branch, levelFourFloor region ≤ levelFourRate region branch)
    (hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch)
    (hlevelTwo : ∀ group branch, levelTwoFloor group ≤ levelTwoRate group branch) :
    coarseFourFamilyFloor ≤
      fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate := by
  have hcoarse : coarseFourFamilyFloor =
      fourFamilyFloor rootFloor levelFourFloor levelThreeFloor levelTwoFloor := rfl
  rw [hcoarse]
  exact fourFamilyFloor_le_fourFamilyExponent rootRate levelFourRate levelThreeRate levelTwoRate
    rootFloor levelFourFloor levelThreeFloor levelTwoFloor
    hroot hlevelFour hlevelThree hlevelTwo

end

end MatrixMultiplication.TotalQuotientExponentStageAggregation
