/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryChild
import AxiomAudit.Command

/-! Axiom coverage for the native boundary child of [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.CWBoundaryChild
#assert_axioms AlgebraicComplexity.Examples.decodeCWBoundaryChild
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryChildProfile
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryChildCell
#assert_axioms AlgebraicComplexity.Examples.decodeCWBoundaryChild_sound
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryChild_mem_support_iff
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryChild_realize
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryChild_nonempty
