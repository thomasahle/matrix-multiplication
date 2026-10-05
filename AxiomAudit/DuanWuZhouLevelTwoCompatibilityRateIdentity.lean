/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompatibilityRateIdentity

set_option autoImplicit false

/-! Focused trust audit for the section 6.3 compatibility-rate identity and the brick it produces
(`[DuanWuZhou2022]` section 6.2--6.3, `lemma:pcomp_g`).

`dwz63_compatibilityLogLoss_dwz63Split` is an *identity*, not an enclosure: the certificate
expression `dwz63LogCompat` is literally the normalized conditional-entropy mass of the committed
section 6.3 split tables.  Its proof is exact rational arithmetic over `Real.log` atoms, with no
`decide`, no `native_decide` and no interval certificate, so
`dwz63_compatibleFractionUpper_dwz63Split` is unconditional. -/

/-! ## Generic rearrangements -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_profileMass_mul_profileEntropyNats
#assert_axioms AlgebraicComplexity.Examples.dwz63_profileMass_scaledRow
#assert_axioms AlgebraicComplexity.Examples.dwz63_rowEntropyTerm_scaledRow
#assert_axioms AlgebraicComplexity.Examples.dwz63_fin3_rowEntropyTerm

/-! ## The section 6.3 identity -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_compatibilityLogLoss_dwz63Split
#assert_axioms AlgebraicComplexity.Examples.dwz63_profileMass_usefulType_dwz63Split
#assert_axioms AlgebraicComplexity.Examples.dwz63_compatibilityRateLog_dwz63Split

/-! ## The brick, at section 6.3 -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_compatibleFractionUpper_dwz63Split
