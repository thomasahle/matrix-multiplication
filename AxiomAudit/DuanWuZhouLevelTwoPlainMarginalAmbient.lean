/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalAmbient

set_option autoImplicit false

/-! # Axiom audit for the plain marginal-typical ambient family -/

#assert_axioms AlgebraicComplexity.Examples.Dwz63PlainMarginalTypical
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarginalWords
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63PlainMarginalWords
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarginalKeep
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarginalTypicalPower
#assert_axioms AlgebraicComplexity.Examples.dwz63_restricts_positivePower_plainMarginalTypical
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainJointRetainedSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63_x_injOn_plainJointRetained
#assert_axioms AlgebraicComplexity.Examples.exists_seed_dwz63PlainJointRetained
