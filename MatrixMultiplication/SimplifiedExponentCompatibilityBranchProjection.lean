/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentRecursiveConstituent

set_option autoImplicit false

/-!
# Compatibility-branch projections for weighted recursive constituents

The recursive-constituent evaluator has one integer-dual branch and two compatibility-row
branches.  This module records that branches one and two of any weighted family are exactly the
outer-mass-weighted sums of its stored logical-`Y` and logical-`Z` compatibility rates.

The statements are independent of recursion depth, certificate data, coordinate alphabets, and
the choice of outer denominator.  Level-three and level-four clients should specialize these laws
rather than unfolding the root evaluator separately.
-/

namespace MatrixMultiplication.SimplifiedExponentRecursiveConstituent

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.SimplifiedExponentRootRecurrence

noncomputable section

/-- Branch one of a weighted local-row family is its outer-mass-weighted logical-`Y` rate sum.

Proof sketch: compare the summands in `weightedFamilyBranchRate`.  At branch one,
`rootBranchRate` projects the `logicalY` record and no integer-dual term remains. -/
theorem weightedFamilyBranchRate_one_eq_logicalY_sum
    {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) :
    weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits entries 1 =
      (entries.map fun entry ↦
        mass outerBits entry.outerNumerator *
          entry.rows.logicalY.rate (referenceBits + compatibilityExtraBits)).sum := by
  unfold weightedFamilyBranchRate
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry _hentry
  simp [WeightedLocalRows.branchRate, LocalRows.branchRate, rootBranchRate,
    LocalRows.toRootRows]

/-- Branch two of a weighted local-row family is its outer-mass-weighted logical-`Z` rate sum.

Proof sketch: this is the branch-two twin of
`weightedFamilyBranchRate_one_eq_logicalY_sum`; `rootBranchRate` projects `logicalZ`. -/
theorem weightedFamilyBranchRate_two_eq_logicalZ_sum
    {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) :
    weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits entries 2 =
      (entries.map fun entry ↦
        mass outerBits entry.outerNumerator *
          entry.rows.logicalZ.rate (referenceBits + compatibilityExtraBits)).sum := by
  unfold weightedFamilyBranchRate
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry _hentry
  simp [WeightedLocalRows.branchRate, LocalRows.branchRate, rootBranchRate,
    LocalRows.toRootRows]

end

end MatrixMultiplication.SimplifiedExponentRecursiveConstituent
