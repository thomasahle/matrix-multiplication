/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroDimensionRestriction
import AxiomAudit.Command

/-! Axiom audit for explicit zero-coordinate CW one-slice restrictions. -/

open AlgebraicComplexity
open AlgebraicComplexity.Examples

#assert_axioms cwZeroChunkOuterWordData
#assert_axioms cwSelectedExactInterfaceConstituentOneSliceRestriction_zeroZ
#assert_axioms cwSelectedExactInterface_constituent_restricts_oneSlice_of_zeroZ
