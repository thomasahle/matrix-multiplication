/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ReaderIndexedParentType

/-!
# Axiom audit for reader-indexed parent-type counting

This focused audit covers the exact finite count in `better_bound/paper.tex`, Appendix C.1,
Theorem `thm:reader-indexed-parent-type`, based on [alman2025more, Claim 6.18] at
`papers/sources/2404.16349/constituent.tex:376-440`.
-/

set_option autoImplicit false

open AlgebraicComplexity

#assert_axioms WordType.ReaderIndexedParentModel
#assert_axioms WordType.ReaderIndexedParentModel.occurrenceWeight
#assert_axioms WordType.ReaderIndexedParentModel.occurrenceProfileOfType
#assert_axioms WordType.ReaderIndexedParentModel.occurrenceProfileOfBlock
#assert_axioms
  WordType.ReaderIndexedParentModel.occurrenceProfileOfBlock_eq_occurrenceProfileOfType_multiplicity
#assert_axioms WordType.ReaderIndexedParentModel.IsFeasibleProfile
#assert_axioms WordType.ReaderIndexedParentModel.feasibleProfiles
#assert_axioms WordType.ReaderIndexedParentModel.mem_feasibleProfiles
#assert_axioms WordType.ReaderIndexedParentModel.parentBlocks
#assert_axioms WordType.ReaderIndexedParentModel.mem_parentBlocks
#assert_axioms WordType.ReaderIndexedParentModel.card_parentBlocks_eq_sum_rowMultinomial
