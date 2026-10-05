/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompatibilityTargets

/-! Focused trust audit for the depth-one `Z` compatibility tables of [DuanWuZhou2022] section 6.3:
the ordered-left-digit bridge on `SplitWord 1`, the identification of the two canonical boundary
constituents of a pooled-all `Z` cell with the two boundary components of that `Z`-index, and the
fifteen-entry integer identity that is `PooledAllTargets.z_decompose` for these tables. -/

#assert_axioms AlgebraicComplexity.Examples.splitWordWeight_one
#assert_axioms AlgebraicComplexity.Examples.splitWordWeight_one_le
#assert_axioms AlgebraicComplexity.Examples.splitWord_one_eq_of_left_of_weight
#assert_axioms AlgebraicComplexity.Examples.dwz63CoarseIndex_injective
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitRow_dwz63CoarseIndex
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitRow_zXBoundaryIndex
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitRow_zYBoundaryIndex
#assert_axioms AlgebraicComplexity.Examples.dwz63AverageCount_eq_boundary_add_pooled
#assert_axioms AlgebraicComplexity.Examples.dwz63_zAll_eq_zBoundaryAggregate_add_zPooled
#assert_axioms AlgebraicComplexity.Examples.dwz63LiftSplitRow_of_weight
#assert_axioms AlgebraicComplexity.Examples.dwz63LiftSplitRow_of_weight_ne
#assert_axioms AlgebraicComplexity.Examples.coarseTotal_one
#assert_axioms AlgebraicComplexity.Examples.dwz63_zXBoundaryIndex_z
#assert_axioms AlgebraicComplexity.Examples.dwz63_zYBoundaryIndex_z
#assert_axioms AlgebraicComplexity.Examples.dwz63CoarseIndex_zXBoundary
#assert_axioms AlgebraicComplexity.Examples.dwz63CoarseIndex_zYBoundary
