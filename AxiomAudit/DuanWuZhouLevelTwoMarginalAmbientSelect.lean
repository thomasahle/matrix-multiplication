/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarginalAmbientSelect

set_option autoImplicit false

/-! # Axiom audit for `hselect` at the marginal-typical ambient

The transposition lemma joining the partition-level cut to the word-level one, the characterisation
of the marginal word family by the legwise predicate, the seam identity itself, and the two
`hselect` forms it unlocks --- from the marginal-typical subpartition, and from the full
six-orientation positive power. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63MarginalKeep_supportWordAddress
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63MarginalWords_iff_keep
#assert_axioms AlgebraicComplexity.Examples.dwz63MarginalTypicalPower_support
#assert_axioms AlgebraicComplexity.Examples.dwz63_restricts_marginalTypicalPower_jointRetainedMarginal
#assert_axioms AlgebraicComplexity.Examples.dwz63_restricts_positivePower_jointRetainedMarginal
