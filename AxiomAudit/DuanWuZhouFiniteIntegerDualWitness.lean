/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DuanWuZhouFiniteIntegerDualWitness

/-!
# Audit of the finite-atom DWZ global combination-loss certificate

Checks the complete fifteen-state maximum-entropy gap in [duan2023faster],
`global_value.tex:286-309,350-375`, with directed rational logarithms.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_integerAtomGap_bound
