/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneKeep

set_option autoImplicit false

/-! # Axiom audit for Additional Zeroing-Out Step 1

`[duan2023faster]`, `global_value.tex:32-61`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63CellWordOfAddress
#assert_axioms AlgebraicComplexity.Examples.dwz63TripleOfLegWord
#assert_axioms AlgebraicComplexity.Examples.dwz63SplresReflected
#assert_axioms AlgebraicComplexity.Examples.dwz63FineStepOneKeep
#assert_axioms AlgebraicComplexity.Examples.dwz63FineStepOneKeepDecidable
#assert_axioms AlgebraicComplexity.Examples.dwz63FineStepOneCut
#assert_axioms AlgebraicComplexity.Examples.dwz63_restricts_preimageFine_stepOne
