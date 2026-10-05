/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalWeightVolumeLossEndpoint

/-!
# Axiom audit for the backed-off total-weight endpoint
-/

open MatrixMultiplication.TotalWeightVolumeLossEndpoint

#assert_axioms rankBudgetUpper_lt_backedOff_endpoint
#assert_axioms sourceBudget_lt_backedOff_endpoint
#assert_axioms acceptanceTarget_eq_decimal
#assert_axioms omega_lt_236999_of_volumeLossSequence
#assert_axioms omega_lt_236999_of_volumeLossSequence_at_floor
