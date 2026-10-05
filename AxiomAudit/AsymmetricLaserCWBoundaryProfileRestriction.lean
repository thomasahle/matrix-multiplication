/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryProfileRestriction

/-! # Axiom audit for the actual native boundary-profile cell and its restriction -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfileCell
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfileExponent
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfile_restricts
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfile_nonempty
