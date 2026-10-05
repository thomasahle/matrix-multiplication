/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.UniformPowerSelection

/-! Focused trust audit for the uniform local `q`-power refinement: the named subexponential
outer-power loss, the division-free pigeonhole and its real-valued form, the projection-closed
sub-family degeneration, and the exact-complete-split uniformity law that makes the refinement
free at an exact interface term. -/

open AlgebraicComplexity
open AlgebraicComplexity.UniformPowerSelection

#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.positivePowerProfile_counts
#assert_axioms uniformPowerLoss
#assert_axioms uniformPowerLoss_pos
#assert_axioms uniformPowerLoss_subexponential
#assert_axioms exists_uniform_power_fibre
#assert_axioms exists_uniform_power_fibre_le_uniformPowerLoss_mul
#assert_axioms filter_eq_self_of_uniform
#assert_axioms isProjectionClosed_of_injOn_x
#assert_axioms restricts_withSupport_of_injOn_x
#assert_axioms splitWordMiddleCount_le_two_pow
#assert_axioms outerChunkStatistic
#assert_axioms outerChunkStatistic_le
#assert_axioms outerChunkStatistic_eq_of_mem_selectEncodedCompleteSplitProfiles_support
#assert_axioms outerChunkStatistic_eq_of_mem_selectEncodedExactInterfaceTerm_support
#assert_axioms mergedDimension_selectEncodedExactInterfaceTerm
