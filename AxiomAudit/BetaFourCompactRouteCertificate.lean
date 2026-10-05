/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.BetaFourCompactRouteCertificate

/-!
# Enforcing audit for compact beta-four route certificates

These assertions cover the optional positive/zero slot packaging and its parent-level soundness
theorem without pulling that packaging into the lower routed-arithmetic module.
-/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalSlotData.CheckedRoute.routedContributions_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalSlotData.CompactRoute.routedContributions_eq
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.CheckedRoute.routedContributions_eq
