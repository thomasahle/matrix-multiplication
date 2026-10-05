/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.AsymmetricLaserIntegerDualWitness

/-!
# Audit of the finite-atom integer maximum-entropy adapter

Checks the sign-sensitive dual verification in [duan2023faster],
`second_power.tex:536-563` and `global_value.tex:286-309`.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.AsymmetricLaserData.integerDualUpper
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.integerDualUpper_bounds
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.integerDualGapUpper_bounds
