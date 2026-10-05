/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SharedOneSliceFiber
import AxiomAudit.Command

/-! Axiom audit for the coherent shared-fibre one-slice bridge. -/

open AlgebraicComplexity

#assert_axioms CTensor.SharedOneSliceFiberData.toFiberRetyping
#assert_axioms CTensor.SharedOneSliceFiberData.toFiberRetyping_sourceAddress
#assert_axioms CTensor.SharedOneSliceFiberData.toFiberRetyping_targetConstituent
#assert_axioms CTensor.SharedOneSliceFiberData.restricts_oneSliceMatrixMultiplication
#assert_axioms CTensor.SharedOneSliceFiberData.restricts_oneSliceMatrixMultiplication_of_support
