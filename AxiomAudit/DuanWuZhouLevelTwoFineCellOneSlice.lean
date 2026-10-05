/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellOneSlice

/-! # Axiom audit for the rotated zero-`X` and zero-`Y` coherent one-slice bases

The two canonical shared-leg maps and the two coherent base certificates that
`[DuanWuZhou2022]` section 6.3's twelve non-orbit fine cells need in the rotated frames.  Both
certificates go through `Classical.choice`, exactly as the committed zero-`Z` form
`cwZeroBaseCoherentRestriction` does; the coherence they carry is bundled into the returned
subtype, so the choice does not make the shared-leg map opaque to a client. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwZeroXBaseCanonicalZMap
#assert_axioms AlgebraicComplexity.Examples.cwZeroXBaseCoherentRestriction
#assert_axioms AlgebraicComplexity.Examples.cwZeroYBaseCanonicalZMap
#assert_axioms AlgebraicComplexity.Examples.cwZeroYBaseCoherentRestriction
