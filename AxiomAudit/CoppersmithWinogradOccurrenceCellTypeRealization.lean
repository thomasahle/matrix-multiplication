/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradOccurrenceCellTypeRealization
import AxiomAudit.Command

/-! Enforcing axiom audit for recursive occurrence full-cell realizations. -/

#assert_axioms AlgebraicComplexity.Examples.profileMass_cwRecursiveOccurrenceFullCellType
#assert_axioms AlgebraicComplexity.Examples.cwRecursiveOccurrenceFullCellType_mem_types
#assert_axioms AlgebraicComplexity.Examples.proportional_cwRecursiveOccurrenceFullCellType_mem_types
#assert_axioms AlgebraicComplexity.Examples.exists_recursiveOccurrenceReference
#assert_axioms AlgebraicComplexity.Examples.exists_proportionalRecursiveOccurrenceReference
#assert_axioms AlgebraicComplexity.Examples.exists_proportionalRecursiveOccurrenceReference_pUnit
