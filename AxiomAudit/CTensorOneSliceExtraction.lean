/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensorOneSliceExtraction
import AxiomAudit.Command

/-!
# Axiom audit for shared-fiber one-slice extraction
-/

open AlgebraicComplexity

#assert_axioms CTensor.FiberRetyping.restricts_oneSliceMatrixMultiplication
#assert_axioms CTensor.FiberRetyping.restricts_oneSliceMatrixMultiplication_of_support
