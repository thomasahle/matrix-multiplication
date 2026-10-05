/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineExpansion

/-! # Axiom audit for the coarse-to-fine expansion at the level-two square

One coarse letter to its fine fiber, plain and legwise-selected; the whole coarse word; and the
indexed form that is the `⊕_retained` left-hand side of the batched Hole Lemma.  All four are
instantiations of committed `Tensor/LocalizedCoarsenedSelection.lean` bridges. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwSquareConstituent_restricts_fineFiber
#assert_axioms AlgebraicComplexity.Examples.cwSquareConstituent_restricts_fineFiberSelect
#assert_axioms AlgebraicComplexity.Examples.dwz63_coarseWord_restricts_fineFiberSelect
#assert_axioms AlgebraicComplexity.Examples.dwz63_indexedDirectSum_coarseWord_restricts_fineFiberSelect
