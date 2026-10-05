/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainLeafValueDischarge

set_option autoImplicit false

/-! # Axiom audit for the plain-leaf hypothesis discharge -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_nonOrbit_cases
#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_nonOrbitCell
#assert_axioms AlgebraicComplexity.Examples.dwz63Alpha112_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63Alpha121_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_power_symSix_orbitCell_scaled
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_orbitCertificates
