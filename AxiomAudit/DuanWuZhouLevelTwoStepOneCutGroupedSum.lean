/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutGroupedSum

set_option autoImplicit false

/-! # Axiom audit for Additional Zeroing-Out Step 2 on the Step-1 cut

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:72, 84-89, 98-102`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63CutFineHcover
#assert_axioms AlgebraicComplexity.Examples.dwz63CutYSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63CutZSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63CutIsolated
#assert_axioms AlgebraicComplexity.Examples.dwz63_cutIsolated_hasGroupUniqueLegFibers
#assert_axioms AlgebraicComplexity.Examples.dwz63CutGrouping
#assert_axioms AlgebraicComplexity.Examples.dwz63_stepOneCut_restricts_groupedDirectSum
