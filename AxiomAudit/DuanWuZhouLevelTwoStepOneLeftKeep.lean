/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneLeftKeep

set_option autoImplicit false

/-! # Axiom audit for Additional Zeroing-Out Step 1 in the paper's alphabet

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:32, 35, 44-50, 52-61`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_typicalType_zDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63_cwSquareComplementLetter_degree_add
#assert_axioms AlgebraicComplexity.Examples.dwz63_boundary_index_sum
#assert_axioms AlgebraicComplexity.Examples.dwz63FineStepOneLeftKeep
#assert_axioms AlgebraicComplexity.Examples.dwz63_splresReflected_degree
#assert_axioms AlgebraicComplexity.Examples.dwz63_fineStepOneKeep_of_leftKeep
#assert_axioms AlgebraicComplexity.Examples.dwz63_fineStepOneLeftKeep_of_keep
#assert_axioms AlgebraicComplexity.Examples.dwz63_stepOneCut_isCompatible_left
