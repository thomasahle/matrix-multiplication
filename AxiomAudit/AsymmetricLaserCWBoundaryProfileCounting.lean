/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryProfileCounting

/-! # Axiom audit for native boundary-profile counting -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfile_card_eq_typeClass
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfile_card_eq_multinomial
#assert_axioms AlgebraicComplexity.Examples.cwBoundaryProfile_restricts_multinomial
