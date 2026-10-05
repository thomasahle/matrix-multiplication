/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentedFiberStabilizer

set_option autoImplicit false

/-! # Axiom audit for the section 6.3 fiber stabilizer and common leaf -/

#assert_axioms AlgebraicComplexity.Examples.dwz63CellIndex_injOn_support
#assert_axioms AlgebraicComplexity.Examples.dwz63Seg_injective
#assert_axioms AlgebraicComplexity.Examples.dwz63Seg_positionEquiv
#assert_axioms AlgebraicComplexity.Examples.dwz63_segPreserving_iff_fixes_word
#assert_axioms AlgebraicComplexity.Examples.dwz63_positionRelabel_target_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_segmentedFineFiber_isomorphic_position
