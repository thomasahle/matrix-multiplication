/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedRegionalAssembly

/-! # Axiom audit for assembling the regional weight bundle

The fifteen concatenation obligations of `SegmentedRegionalSymSixWeights` collapse to one
invariant on the parent coarse target.

Primary source: `[duan2023faster]`, section 6.3 (the level-two global-value example),
`papers/sources/2210.10173/global_value.tex:332-348`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.positiveWordEquiv_appendEquiv_symm_snd
#assert_axioms AlgebraicComplexity.segmentedRegionalSymSixWeights_of_letterwise
