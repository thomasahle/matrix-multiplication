/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DuanWuZhouFiniteEntropyWitness

/-!
# Audit of the literal DWZ finite-profile entropy witness

Checks the shared rational-atanh adapter on the actual 022 profile in [duan2023faster],
`global_value.tex:332-378`. No extraction or exponent endpoint is asserted here.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63Row022EntropyWitness_bounds
