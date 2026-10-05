/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellWeight

/-! # Axiom audit for the `tau`-weight of one fused fine cell

The fused cell's weight `(|fibre| * q ^ k) ^ tau` in the
rotated and unrotated frames. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_permuted_fineCellPower
#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_fineCellPower
