/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellWord

/-! # Axiom audit for the rotated zero-`X` and zero-`Y` coherent word certificates

The two canonical word-level shared-leg maps, the two word recursions obtained by running the
committed `OneSliceRestriction.permutedCoherentWord` on the rotated bases, and the `r = 1`
fine-letter instance that `[DuanWuZhou2022]` section 6.3's pair alphabet needs. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwZeroXWordCanonicalZMap
#assert_axioms AlgebraicComplexity.Examples.cwZeroXWordCoherentRestriction
#assert_axioms AlgebraicComplexity.Examples.cwZeroXPairCoherentRestriction
#assert_axioms AlgebraicComplexity.Examples.cwZeroYWordCanonicalZMap
#assert_axioms AlgebraicComplexity.Examples.cwZeroYWordCoherentRestriction
