/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedHoleRepairGeneral

set_option autoImplicit false

/-! # Axiom audit for the general segmented Hole Lemma -/

#assert_axioms AlgebraicComplexity.restricts_indexedDirectSum_segmentedHoleRepair_general
#assert_axioms AlgebraicComplexity.restricts_indexedDirectSum_segmentedHoleRepair_general_batched
#assert_axioms AlgebraicComplexity.segmentedKeeps_ofLeg_availability
#assert_axioms AlgebraicComplexity.restricts_indexedDirectSum_segmentedPowerHoleRepair_batched
