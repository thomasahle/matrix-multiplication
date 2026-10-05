/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCompatiblePosition

set_option autoImplicit false

/-! # Axiom audit for the per-position and per-leg readings of a Step-1 address

The bookkeeping consumed by the transcription of `lemma:triple_implies_compatible` of
`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:32-71`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_boundary_index_zero
#assert_axioms AlgebraicComplexity.Examples.dwz63_fineLetterAddress_mem_cwSquareRawSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63_cell_cellWordOfAddress
#assert_axioms AlgebraicComplexity.Examples.dwz63_tripleOfLegWord_eq
