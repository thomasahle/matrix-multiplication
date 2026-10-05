/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.UniformPowerFusion

/-! Focused trust audit for the fusion of a uniform-local-power family into one merged leaf:
the merged-dimension restriction in both its sub-family and full-support forms, the merged
one-slice `WholeConstituentLaserVolumeStage`, the combined selection-plus-fusion statement, and
the two label-map helpers a shared-`Z` client discharges its pointwise hypothesis with. -/

open AlgebraicComplexity
open AlgebraicComplexity.UniformPowerSelection

#assert_axioms AlgebraicComplexity.CTensor.FiberRetyping.sourceAddress_mem
#assert_axioms AlgebraicComplexity.CTensor.FiberRetyping.oneSliceLabelConstituentMap
#assert_axioms restricts_matrixMultiplication_mergedDimension
#assert_axioms restricts_matrixMultiplication_mergedDimension_of_support
#assert_axioms mergedOneSliceStage
#assert_axioms exists_uniform_power_fibre_restricts_mergedDimension
