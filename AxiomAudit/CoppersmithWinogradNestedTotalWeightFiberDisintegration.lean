/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradNestedTotalWeightFiberDisintegration

set_option autoImplicit false

/-! # Axiom audit for finite nested CW total-weight fiber disintegration -/

#assert_axioms AlgebraicComplexity.Examples.cwDepthTwoTotalWeightOuter_comp_payload
#assert_axioms AlgebraicComplexity.Examples.cwDepthTwoTotalWeightFiberCompEquiv
#assert_axioms AlgebraicComplexity.Examples.card_cwDepthTwoTotalWeightFiber_eq_sum
#assert_axioms AlgebraicComplexity.Examples.mappedType_cwDepthTwoTotalWeightPayload_outer
