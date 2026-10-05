/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeRecurrence
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopRecurrence

set_option autoImplicit false

/-!
# Semantic level-four branch-floor certificate for the total-weight quotient

The generated analytic checker proves all eighteen directed floor inequalities against an explicit
selected-parent family using compact cached top and depth-three tables.  This module performs the
semantic handoff: the separately checked recurrence theorems identify those caches with the tables
reconstructed from the primary `e7987…` total-weight certificate.

The public `branchFloorCertified` theorem is therefore independent of the generated encoding.  It
states exactly that every level-four regional floor lies below every selected-parent
*integer-dual* branch rate computed by the quotient-parametric recurrence on the primary tables.
Relating that conservative rate to the mathematical fixed-marginal construction is a separate
validity bridge; no tensor extraction, support exhaustiveness, or optimizer optimality is asserted
here.
-/

namespace MatrixMultiplication.TotalQuotientExponentLevelFourCertificate

open AlgebraicComplexity.RetainedExponentAggregation
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentStageFloors

/-- Exact selected-parent integer-dual level-four branch rate reconstructed from the total-weight
primary certificate.

The coordinate order and positive integer duals are certificate data.  Both probability tables,
however, are recomputed from the checked primary tables rather than taken from generated literals.
The explicit parent list describes what the certificate retains; it need not exhaust the ambient
positive support.
-/
noncomputable def levelFourRate (region : Region) (branch : Fin 3) : ℝ :=
  branchRateOnParentsFrom
    (reconstructedTopBranchRows TotalQuotientVolumeReconstruction.primaryTables)
    (reconstructedBetaThreeRowsFor TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot
      TotalQuotientVolumeReconstruction.primaryTables)
    Orientation.order (weights region.val) region.val (parents region.val) branch

/-- The semantic rate agrees with the compact checker's cached rate.

Proof sketch: replace the reconstructed top and depth-three tables using their independently
kernel-checked recurrence equalities.  The remaining expression is definitionally the generated
selected-parent regional rate.
-/
theorem levelFourRate_eq_generated (region : Region) (branch : Fin 3) :
    levelFourRate region branch = branchRate region branch := by
  unfold levelFourRate branchRate
  rw [Top.recurrence_eq, BetaThree.recurrence_eq]

/-- Every certified regional level-four floor lies below every reconstructed integer-dual rate. -/
theorem levelFourFloor_le_levelFourRate (region : Region) (branch : Fin 3) :
    levelFourFloor region ≤ levelFourRate region branch := by
  rw [levelFourRate_eq_generated]
  exact levelFourFloor_le_branchRate region branch

/-- Paper-facing proposition packaging all eighteen level-four branch-floor inequalities. -/
def BranchFloorCertified : Prop :=
  ∀ region branch, levelFourFloor region ≤ levelFourRate region branch

/-- The compact generated certificate establishes all eighteen selected-parent floor bounds. -/
theorem branchFloorCertified : BranchFloorCertified :=
  levelFourFloor_le_levelFourRate

/-- The certified level-four family floor is below the reconstructed integer-dual family exponent.

Proof sketch: apply the reusable three-branch bottleneck aggregation theorem pointwise with
`branchFloorCertified`, then sum over the six regions.  No additional numerical calculation is
performed here.
-/
theorem levelFourFamilyFloor_le_familyExponent :
    familyFloor levelFourFloor ≤ familyExponent levelFourRate :=
  familyFloor_le_familyExponent levelFourRate levelFourFloor branchFloorCertified

end MatrixMultiplication.TotalQuotientExponentLevelFourCertificate
