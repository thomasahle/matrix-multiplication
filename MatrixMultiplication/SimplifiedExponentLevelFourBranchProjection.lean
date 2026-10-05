/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentCompatibilityBranchProjection
import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option autoImplicit false

/-!
# Compatibility-branch projections for the level-four recurrence

The level-four recurrence packages each parent as a weighted three-branch local row.  Its two
compatibility branches contain no integer-dual calculation: branch one is exactly the stored
logical-`Y` compatibility rate and branch two is exactly the stored logical-`Z` compatibility
rate.  This module exposes those facts after summing an arbitrary explicit parent list.

These identities are certificate independent.  They use only two definitional choices of the
level-four recurrence: every parent has outer numerator one, and the outer denominator has zero
bits.  In particular, the dual weights disappear from both conclusions.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.SimplifiedExponentRootRecurrence

noncomputable section

/-- Branch one of an explicit level-four parent family is the sum of its logical-`Y`
compatibility-row rates.

Proof sketch: expand the family map and compare its summands.  Each entry has outer mass
`1 / 2^0 = 1`; branch one of `rootBranchRate` then projects the `logicalY` field installed by
`localRowsFrom`. -/
theorem branchRateOnParentsFrom_one_eq_logicalY_sum
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (parents : List ℕ) :
    branchRateOnParentsFrom top betaThree orders weights region parents 1 =
      (parents.map fun parent ↦
        (logicalYRows top betaThree (orders region) region region parent).rate
          (referenceBits + compatibilityExtraBits)).sum := by
  unfold branchRateOnParentsFrom regionEntriesOnParentsFrom
  rw [weightedFamilyBranchRate_one_eq_logicalY_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro parent _hparent
  simp [weightedLocalRowsFrom, localRowsFrom, outerBits,
    MatrixMultiplication.DyadicEntropy.mass]

/-- Branch two of an explicit level-four parent family is the sum of its logical-`Z`
compatibility-row rates.

Proof sketch: this is the branch-two twin of
`branchRateOnParentsFrom_one_eq_logicalY_sum`; the outer unit mass disappears and
`rootBranchRate` projects the `logicalZ` field. -/
theorem branchRateOnParentsFrom_two_eq_logicalZ_sum
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (parents : List ℕ) :
    branchRateOnParentsFrom top betaThree orders weights region parents 2 =
      (parents.map fun parent ↦
        (logicalZRows top betaThree (orders region) region region parent).rate
          (referenceBits + compatibilityExtraBits)).sum := by
  unfold branchRateOnParentsFrom regionEntriesOnParentsFrom
  rw [weightedFamilyBranchRate_two_eq_logicalZ_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro parent _hparent
  simp [weightedLocalRowsFrom, localRowsFrom, outerBits,
    MatrixMultiplication.DyadicEntropy.mass]

end

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
