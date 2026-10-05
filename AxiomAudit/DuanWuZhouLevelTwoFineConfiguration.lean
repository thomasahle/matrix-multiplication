/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineConfiguration
import AxiomAudit.Command

/-! # Axiom audit for the parameterized DWZ level-two fine configuration -/

#assert_axioms AlgebraicComplexity.Examples.cwDepthOneRawAddress_mem_cwSquareRawSupport
#assert_axioms AlgebraicComplexity.Examples.cwDepthOneCoarseShape_mem_cwSquareSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63FineComponent
#assert_axioms AlgebraicComplexity.Examples.dwz63Cell_dwz63FineComponent
#assert_axioms AlgebraicComplexity.Examples.dwz63FineSplit
#assert_axioms AlgebraicComplexity.Examples.splitWordWeight_dwz63FineSplit
#assert_axioms AlgebraicComplexity.Examples.dwz63FineZLeftCount
#assert_axioms AlgebraicComplexity.Examples.Dwz63FineConfiguration
#assert_axioms AlgebraicComplexity.Examples.dwz63FineCountScale
#assert_axioms AlgebraicComplexity.Examples.dwz63FineZLeftCount_scale
#assert_axioms AlgebraicComplexity.Examples.dwz63FineComponentLegExact
#assert_axioms AlgebraicComplexity.Examples.dwz63FineXExact
#assert_axioms AlgebraicComplexity.Examples.dwz63FineYExact
#assert_axioms AlgebraicComplexity.Examples.dwz63FineZExact
#assert_axioms AlgebraicComplexity.Examples.dwz63FineZExact_eq_dwz63ZExact
