/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.GroupCoarsePairCounting

set_option autoImplicit false

/-! # Axiom audit for the deduplicated coarse-pair counting bound -/

#assert_axioms AlgebraicComplexity.groupCoarsePairs
#assert_axioms AlgebraicComplexity.mem_groupCoarsePairs
#assert_axioms AlgebraicComplexity.retainedGroupCoarsePairs
#assert_axioms AlgebraicComplexity.mem_retainedGroupCoarsePairs
#assert_axioms AlgebraicComplexity.card_le_sum_fiber_of_encoding
#assert_axioms AlgebraicComplexity.card_le_card_fiber_of_encoding
#assert_axioms AlgebraicComplexity.card_retainedGroupCoarsePairs_le_sum_fiber
