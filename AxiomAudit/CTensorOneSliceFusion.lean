/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensorOneSliceFusion
import AxiomAudit.Command

/-! Axiom audit for finite one-slice C-tensor fusion. -/

open AlgebraicComplexity AlgebraicComplexity.CTensor

#assert_axioms oneSliceBlockCoordinateEquiv
#assert_axioms oneSliceFusionEquiv
#assert_axioms oneSliceFusionEquiv_block_mmTerm
#assert_axioms map_oneSliceFusionMap_embedded_constituent
#assert_axioms partitioned_oneSliceMatrixMultiplication_isomorphic
#assert_axioms partitioned_oneSliceMatrixMultiplication_restricts
