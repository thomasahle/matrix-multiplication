/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleSupplier

set_option autoImplicit false

/-! # Axiom audit for the Additional Zeroing-Out Step 2 hole supplier

The hole set of one retained copy under the paper's two rules, its membership characterisation and
the positive reading of a non-hole, and the `1/8` Hole-Lemma budget in the segmented alphabet,
single and batched. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63HoleSet
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63HoleSet
#assert_axioms AlgebraicComplexity.Examples.usefulFor_of_notMem_dwz63HoleSet
#assert_axioms AlgebraicComplexity.Examples.dwz63_segmentedHoleBudget
#assert_axioms AlgebraicComplexity.Examples.dwz63_segmentedHoleBudget_batched
