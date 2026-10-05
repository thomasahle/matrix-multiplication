/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGroupedLeaf

set_option autoImplicit false

/-! # Axiom audit for the grouped leaf and the discharged stage -/

#assert_axioms AlgebraicComplexity.Examples.partitionedSelect_select
#assert_axioms AlgebraicComplexity.Examples.partitionedSelect_congr
#assert_axioms AlgebraicComplexity.Examples.dwz63BrokenFineLeaf_eq_select
#assert_axioms AlgebraicComplexity.Examples.dwz63BrokenFineLeaf_eq_fiberSelect
#assert_axioms AlgebraicComplexity.Examples.dwz63_brokenFineLeaf_isomorphic_position
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63PlainFine_support
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainFine_hcover
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainFine_hambient
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63PlainBrokenGroup_dwz63PlainFine
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainBrokenGroup_select_eq_brokenFineLeaf
#assert_axioms AlgebraicComplexity.Examples.dwz63_brokenGroup_restricts_brokenReferenceLeaf
#assert_axioms AlgebraicComplexity.Examples.dwz63_groupedStage_of_claim3
