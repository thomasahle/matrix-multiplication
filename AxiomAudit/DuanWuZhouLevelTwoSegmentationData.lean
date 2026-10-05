/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentationData

set_option autoImplicit false

/-! # Axiom audit for section 6.3's segmentation data -/

#assert_axioms AlgebraicComplexity.Examples.card_fiber_dwz63Seg
#assert_axioms AlgebraicComplexity.Examples.dwz63FinePartition
#assert_axioms AlgebraicComplexity.Examples.dwz63SegmentedLeaf
#assert_axioms AlgebraicComplexity.Examples.dwz63BrokenSegmentedLeaf
