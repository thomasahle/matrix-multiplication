/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutDominationInputs

set_option autoImplicit false

/-! # Axiom audit for the encoding inputs of the Step-1 cut's domination

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:28, 32, 44-50, 249-265`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63Seg_eq_cellWordOfAddress
#assert_axioms AlgebraicComplexity.Examples.dwz63_zIndex_dwz63Seg
#assert_axioms AlgebraicComplexity.Examples.dwz63_multiplicity_dwz63Seg_of_mem_markedWords
#assert_axioms AlgebraicComplexity.Examples.dwz63_segmentedAvailable_frameTransport
