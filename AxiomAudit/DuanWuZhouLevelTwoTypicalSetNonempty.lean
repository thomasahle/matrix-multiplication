/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTypicalSetNonempty

set_option autoImplicit false

/-! # Axiom audit for the discharge of `hT` and the unconditional cofinal `hVdeg` -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_card_split_typicalSet_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_cofinal_competitorBound_le_plainSharpDegree
