/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.BetaFourLocalGatherAgreement

/-! Focused trust audit for parent-local beta-four scatter/gather agreement. -/

#assert_axioms MatrixMultiplication.BetaFourSemanticAgreement.BetaFourLocalSlotData.gatherNumerator_eq_selected
#assert_axioms MatrixMultiplication.BetaFourSemanticAgreement.BetaFourLocalSlotData.symbols_eq_selected_of_route_eq
#assert_axioms MatrixMultiplication.BetaFourSemanticAgreement.BetaFourLocalSlotData.selected_route_eq
#assert_axioms MatrixMultiplication.BetaFourSemanticAgreement.BetaFourLocalSlotData.addToNumeratorAt_eq_add_gatherNumerator
