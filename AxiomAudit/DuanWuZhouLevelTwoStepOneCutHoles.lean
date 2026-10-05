/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutHoles

set_option autoImplicit false

/-! # Axiom audit for the Step-1 cut's hole family and its competitor facts

`[duan2023faster]`, section 6.1 `sec:global-algo`, claim `claim:hole_frac_low`,
`papers/sources/2210.10173/global_value.tex:249-265` (necessary condition at `:255`), over the
Step-1 cut of `:52-72`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63CutReferenceHoles
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63CutReferenceHoles
#assert_axioms AlgebraicComplexity.Examples.dwz63Seg_sourceWordOfLegalTriple
#assert_axioms AlgebraicComplexity.Examples.dwz63_coarseZ_of_cutReferenceHole
#assert_axioms AlgebraicComplexity.Examples.dwz63_cutReferenceHole_isCompatible
#assert_axioms AlgebraicComplexity.Examples.dwz63_inCommonTriple_of_zIndex_eq
