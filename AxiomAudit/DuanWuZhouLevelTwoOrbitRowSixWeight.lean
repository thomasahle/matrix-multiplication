/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitRowSixWeight

/-! # Axiom audit for the `(1,1,2)` orbit row's `sym₃` weight

The row's share of the global distribution, the period reconciliation onto the assembly's lattice,
the index-length identification, the `sym₃` weight at `eps = 10^(-22)`, and the assembly's `R3`
binder at `eps = dwz63LeafMargin`.  Formalizes `[duan2023faster]` `global_value.tex:270-320` and
`:338-347`. -/

set_option autoImplicit false

open AlgebraicComplexity.Examples

#assert_axioms dwz63_orbitRowSix_alpha
#assert_axioms dwz63_orbitRowSix_period
#assert_axioms dwz63_symThree_orbitRowSix_weight_of_ambient
#assert_axioms dwz63_orbitRowSix_depth
#assert_axioms dwz63_orbitRowSix_R3_of_ambient
