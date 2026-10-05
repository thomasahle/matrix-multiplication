/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPreimageAmbient

set_option autoImplicit false

/-! # Axiom audit for the reachable fine ambient -/

#assert_axioms AlgebraicComplexity.Examples.mem_dwz63PreimageFine_support
#assert_axioms AlgebraicComplexity.Examples.dwz63PreimageFine_hcover
#assert_axioms AlgebraicComplexity.Examples.dwz63_power_restricts_preimageFine
