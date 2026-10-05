/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineTargetSupport
import AxiomAudit.Command

/-! # Axiom audit for support and coarse mass of the DWZ fine targets -/

#assert_axioms AlgebraicComplexity.Examples.cwSplitWordTotalDigit_dwz63FineSplit
#assert_axioms AlgebraicComplexity.Examples.dwz63FineCompatibilityTargets_isWeightSupported
#assert_axioms AlgebraicComplexity.Examples.dwz63FineComponentMass
#assert_axioms AlgebraicComplexity.Examples.dwz63FineComponentMass_eq_proportionalCounts
#assert_axioms AlgebraicComplexity.Examples.dwz63FineComponentMass_scale
#assert_axioms AlgebraicComplexity.Examples.dwz63FineComponentMass_scale_eq_proportionalCounts
