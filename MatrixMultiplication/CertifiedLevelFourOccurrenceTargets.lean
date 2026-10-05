/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityChecks
import MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences

/-!
# Occurrence targets instantiated at the compact level-four certificate

`levelFourOccurrenceTargetData` builds the semantic compatibility-target package of one level-four
parent from two finite inputs: child-row normalization and the per-slot boundary complementation
law.  The compact certificate `e7987d7f…` proves the first input for every positive parent in each
of the six diagonal `(root, incomingRegion) = (region, region)` occurrences at the repeated `XZY`
orientation, so this module discharges it once and for all.

What remains visible is exactly one premise per tuple: `FixedParentSlotBoundaryValid` at the
committed rows and the committed evaluator coordinate order.  `certifiedTargetData_ofChecked` is
the seam meant for the generated shards — a `true` value of the bounded checker
`fixedParentSlotBoundaryValid` is all a producer has to emit.

The export theorem identifies the semantic targets with the proof-free
`fixedParentCompatibilityTargets` consumed by the finite checker, so a client may move between the
occurrence-law side and the evaluator side without re-deriving either.

No hashing statement, tensor restriction, counting floor, numerical rate, or asymptotic premise
occurs here.
-/

namespace MatrixMultiplication.CertifiedLevelFourOccurrenceTargets

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-! ## The committed data of certificate `e7987d7f…` -/

/-- The committed level-four top branch rows. -/
abbrev certifiedTop : TopBranchRows :=
  Generated.TotalQuotientExponentLevelFourRecurrence.Top.expectedRows

/-- The committed padded depth-three beta rows. -/
abbrev certifiedBetaThree : BetaThreeRows :=
  Generated.TotalQuotientExponentLevelFourRecurrence.BetaThree.expectedRows

/-- The committed evaluator coordinate order, one per region. -/
abbrev certifiedOrder (region : ℕ) : CoordinateOrder :=
  Generated.TotalQuotientExponentLevelFourRecurrence.Orientation.order region

/-- The committed evaluator coordinate order describes the same logical-to-physical assignment as
the repeated `XZY` orientation used by the semantic occurrence laws. -/
theorem certifiedOrder_agreesWithOrientation (region : ℕ) :
    CoordinateOrder.AgreesWithOrientation (certifiedOrder region) xzy := by
  intro c
  cases c <;> rfl

/-- Child-row normalization at one committed diagonal tuple, from the compact certificate. -/
theorem certifiedChildRowsValid (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) :
    LevelFourChildRowsValid certifiedTop certifiedBetaThree region region parent xzy :=
  Generated.TotalQuotientExponentLevelFourValidity.childRowsValid region parent

/-! ## The occurrence-target package per diagonal tuple -/

/-- The per-slot occurrence profile of one committed diagonal tuple: the ordered top split
numerator scaled by the two depth-three child sample counts. -/
abbrev certifiedSlotProfile (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (slot : LevelFourValidSlot parent) : ℕ :=
  levelFourSlotNumerator certifiedTop region region parent slot *
    (levelFourChildSamples * levelFourChildSamples)

/-- **Item 12.**  The semantic occurrence-target package of one committed diagonal
`(parent, region)` tuple.  Child-row normalization and the coordinate-order agreement are
discharged from the certificate; only the finite per-slot boundary law is still an input. -/
noncomputable def certifiedTargetData (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hboundary : FixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val) :
    RecursiveOccurrenceTargetData (depth := 2)
      (levelFourOccurrenceCoarseIndex parent xzy)
      (certifiedSlotProfile region parent) :=
  levelFourOccurrenceTargetData certifiedTop certifiedBetaThree
    (certifiedOrder region.val) xzy (certifiedOrder_agreesWithOrientation region.val)
    region region parent (certifiedChildRowsValid region parent) hboundary

/-- The occurrence law of the committed package is the semantic level-four law. -/
theorem certifiedTargetData_law (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hboundary : FixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val) (c : Leg) :
    (certifiedTargetData region parent hboundary).law c =
      levelFourOccurrenceLaw certifiedTop certifiedBetaThree region region parent xzy
        (certifiedChildRowsValid region parent) c :=
  rfl

/-- **Item 12 export.**  The compatibility targets carried by the committed occurrence package are
exactly the proof-free targets the finite checker and the evaluator consume. -/
theorem certifiedTargetData_toCompatibilityTargets (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hboundary : FixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val) :
    (certifiedTargetData region parent hboundary).toCompatibilityTargets =
      fixedParentCompatibilityTargets certifiedTop certifiedBetaThree
        (certifiedOrder region.val) region.val region.val parent.val hboundary :=
  levelFourOccurrenceTargets_eq_fixedParentCompatibilityTargets certifiedTop certifiedBetaThree
    (certifiedOrder region.val) xzy (certifiedOrder_agreesWithOrientation region.val)
    region region parent (certifiedChildRowsValid region parent) hboundary

/-- Every labelled occurrence of a committed parent is a tight depth-two constituent.  This is the
`htotal` input of the count-facing clients. -/
theorem certifiedOccurrenceCoarseIndex_total
    (parent : Fin positiveLevelFourShapeCount)
    (occurrence : ComplementaryOccurrence (LevelFourValidSlot parent)) :
    (levelFourOccurrenceCoarseIndex parent xzy occurrence).x +
        (levelFourOccurrenceCoarseIndex parent xzy occurrence).y +
        (levelFourOccurrenceCoarseIndex parent xzy occurrence).z = coarseTotal 2 :=
  levelFourOccurrenceCoarseIndex_total parent xzy occurrence

/-! ## The producer seam and the whole diagonal family -/

/-- **Producer seam.**  A `true` value of the bounded boundary checker at one committed diagonal
tuple already yields the occurrence-target package.  Generated shards need to expose nothing but
this Boolean equation. -/
noncomputable def certifiedTargetData_ofChecked (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hchecked : fixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val = true) :
    RecursiveOccurrenceTargetData (depth := 2)
      (levelFourOccurrenceCoarseIndex parent xzy)
      (certifiedSlotProfile region parent) :=
  certifiedTargetData region parent
    (fixedParentSlotBoundaryValid_sound certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val hchecked)

/-- The checked package exports the same proof-free targets. -/
theorem certifiedTargetData_ofChecked_toCompatibilityTargets (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hchecked : fixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val = true) :
    (certifiedTargetData_ofChecked region parent hchecked).toCompatibilityTargets =
      fixedParentCompatibilityTargets certifiedTop certifiedBetaThree
        (certifiedOrder region.val) region.val region.val parent.val
        (fixedParentSlotBoundaryValid_sound certifiedTop certifiedBetaThree
          (certifiedOrder region.val) region.val region.val parent.val hchecked) :=
  certifiedTargetData_toCompatibilityTargets region parent _

/-- The one residual premise of the whole compact certificate: the finite per-slot boundary law at
all `6 * 105` committed diagonal tuples. -/
def CertifiedDiagonalBoundaryValid : Prop :=
  ∀ (region : Fin 6) (parent : Fin positiveLevelFourShapeCount),
    FixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val

/-- The bounded-checker form of the residual premise, stated exactly as a generated aggregator
would emit it. -/
def CertifiedDiagonalBoundaryChecked : Prop :=
  ∀ (region : Fin 6) (parent : Fin positiveLevelFourShapeCount),
    fixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val = true

/-- The bounded checker soundly discharges the residual premise for the whole family. -/
theorem certifiedDiagonalBoundaryValid_of_checked
    (hchecked : CertifiedDiagonalBoundaryChecked) : CertifiedDiagonalBoundaryValid :=
  fun region parent ↦
    fixedParentSlotBoundaryValid_sound certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val (hchecked region parent)

/-- **Item 12, family form.**  The occurrence-target package at every committed diagonal tuple. -/
noncomputable def certifiedDiagonalTargetData (hboundary : CertifiedDiagonalBoundaryValid)
    (region : Fin 6) (parent : Fin positiveLevelFourShapeCount) :
    RecursiveOccurrenceTargetData (depth := 2)
      (levelFourOccurrenceCoarseIndex parent xzy)
      (certifiedSlotProfile region parent) :=
  certifiedTargetData region parent (hboundary region parent)

/-- Every member of the family exports the certificate's proof-free targets. -/
theorem certifiedDiagonalTargetData_toCompatibilityTargets
    (hboundary : CertifiedDiagonalBoundaryValid) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) :
    (certifiedDiagonalTargetData hboundary region parent).toCompatibilityTargets =
      fixedParentCompatibilityTargets certifiedTop certifiedBetaThree
        (certifiedOrder region.val) region.val region.val parent.val
        (hboundary region parent) :=
  certifiedTargetData_toCompatibilityTargets region parent (hboundary region parent)

end MatrixMultiplication.CertifiedLevelFourOccurrenceTargets
