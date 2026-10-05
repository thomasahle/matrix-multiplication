/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainRate

set_option autoImplicit false

/-! # Axiom audit for the plain-partition rate and its loss -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount
#assert_axioms AlgebraicComplexity.Examples.subexponential_dwz63PlainLossHash
