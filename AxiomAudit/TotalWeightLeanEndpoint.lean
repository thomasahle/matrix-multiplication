/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalWeightLeanEndpoint

/-! Focused trust audit for the total-weight Lean endpoints. -/

open MatrixMultiplication.TotalWeightLeanEndpoint

#assert_axioms omega_lt_236999_of_nestedSequenceData
#assert_axioms omega_lt_236999_of_nestedAcceptanceData
