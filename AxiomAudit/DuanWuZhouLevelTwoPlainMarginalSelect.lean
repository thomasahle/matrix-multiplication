/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalSelect

set_option autoImplicit false

/-! # Axiom audit for `hselect` at the plain marginal-typical ambient -/

#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarginalKeep_supportWordAddress
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63PlainMarginalWords_iff_keep
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarginalTypicalPower_support
#assert_axioms AlgebraicComplexity.Examples.dwz63_restricts_plainMarginalTypicalPower_plainJointRetained
#assert_axioms AlgebraicComplexity.Examples.dwz63_restricts_positivePower_plainJointRetained
#assert_axioms AlgebraicComplexity.Examples.card_image_x_dwz63PlainJointRetainedSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainCopyCount_forces_card_xWords
