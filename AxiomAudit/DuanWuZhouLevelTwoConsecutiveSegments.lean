/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoConsecutiveSegments

/-! # Axiom audit for section 6.3's leaf on consecutive segments

The fifteen consecutive regions of the reference leaf, their multiplicity profile and pointwise
type sum, and the permutation that sorts the leaf onto them. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63Alpha_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63ConsecutiveBlock
#assert_axioms AlgebraicComplexity.Examples.dwz63ConsecutiveBlocks
#assert_axioms AlgebraicComplexity.Examples.dwz63_mem_consecutiveBlocks
#assert_axioms AlgebraicComplexity.Examples.dwz63_multiplicityProfile_consecutiveBlocks
#assert_axioms AlgebraicComplexity.Examples.dwz63_parentType_consecutiveBlocks
#assert_axioms AlgebraicComplexity.Examples.dwz63_multiplicity_seg_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_fiber_seg_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_consecutiveBlocks
#assert_axioms AlgebraicComplexity.Examples.dwz63_referenceLeaf_isomorphic_consecutive
