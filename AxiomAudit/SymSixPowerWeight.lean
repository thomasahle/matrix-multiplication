/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SymSixPowerWeight

set_option autoImplicit false

/-! # Axiom audit for the `sym₃`-power to `sym₆`-power weight bridge -/

#assert_axioms AlgebraicComplexity.restricts_power_symSix_external_power_symThree
#assert_axioms AlgebraicComplexity.hasTauWeight_power_symSix_of_power_symThree
