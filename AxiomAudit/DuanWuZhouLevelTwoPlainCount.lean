/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainCount

set_option autoImplicit false

/-! # Axiom audit for the level-two counts at the plain partition -/

#assert_axioms AlgebraicComplexity.Examples.mappedType_subtype_of_vanishing
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainAlpha
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainLegRead
#assert_axioms AlgebraicComplexity.Examples.profileMass_dwz63PlainAlpha
#assert_axioms AlgebraicComplexity.Examples.mappedType_dwz63PlainLegRead
#assert_axioms AlgebraicComplexity.Examples.mappedType_dwz63PlainLegRead_proportionalCounts
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainJointCount
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainLegCount
#assert_axioms AlgebraicComplexity.Examples.proportionalCounts_dwz63PlainAlpha_mem_types
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainJointCount_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainLegCount_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainLegCount_mul_card_typedWordMapFiber
