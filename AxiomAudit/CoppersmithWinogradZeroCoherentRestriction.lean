/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroCoherentRestriction
import AxiomAudit.Command

/-! Axiom audit for the exact coherent zero-coordinate CW fusion. -/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwZeroBaseCoherentRestriction
#assert_axioms cwZeroBaseWordCoherentRestriction
#assert_axioms cwZeroChunkCoherentRestriction
#assert_axioms cwZeroChunkOuterWordCoherentRestriction
#assert_axioms cwSelectedExactInterfaceConstituentCoherentRestriction_zeroZ
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_sharedOneSliceData
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_restricts_fusedOneSlice
