/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoInstanceData

set_option autoImplicit false

/-! # Axiom audit for section 6.3's engine data -/

#assert_axioms AlgebraicComplexity.Examples.dwz63EngineInner_realize
#assert_axioms AlgebraicComplexity.Examples.dwz63EngineInner_support_card
#assert_axioms AlgebraicComplexity.Examples.dwz63EngineSplit_Z
#assert_axioms AlgebraicComplexity.Examples.dwz63EngineSplit_X
#assert_axioms AlgebraicComplexity.Examples.dwz63EngineSplit_Y
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63EngineLeafPartition_support
#assert_axioms AlgebraicComplexity.Examples.restricts_dwz63EnginePower_leaf
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_dwz63EngineData
