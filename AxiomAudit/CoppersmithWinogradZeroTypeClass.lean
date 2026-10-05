/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroTypeClass
import AxiomAudit.Command

/-! Axiom audit for the concrete zero-coordinate CW type-class certificate. -/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwBlockDigit_cwBlockOfSplitDigit
#assert_axioms cwZeroBaseAddressOfSplitDigit_mem
#assert_axioms cwChunkSplitWord_zeroChunkSupport_x
#assert_axioms cwChunkSplitWord_zeroChunkSupport_y
#assert_axioms cwChunkSplitWord_zeroChunkSupport_z
#assert_axioms cwZeroCoordinateCompleteFiberData
#assert_axioms card_cwSelectedExactInterfaceTerm_zeroZ_eq_card_typeClass
