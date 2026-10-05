/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarginalAmbientFamily

set_option autoImplicit false

/-! # Axiom audit for the marginal-typical ambient family of `[DuanWuZhou2022]` section 6.3

The three leg marginals of `dwz63Alpha` and the pushforward identity behind them; marginal
typicality of a block word and the family it cuts out; target typicality implying it (`hmarked`);
the legwise `select` and its restriction, which is the step a joint-type cut cannot take; and the
retained family at the new ambient with its `hX` certificate and its good seed. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63LegMarginal
#assert_axioms AlgebraicComplexity.Examples.mappedType_legProjection_dwz63AlphaAddress
#assert_axioms AlgebraicComplexity.Examples.Dwz63MarginalTypical
#assert_axioms AlgebraicComplexity.Examples.dwz63MarginalWords
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63MarginalWords
#assert_axioms AlgebraicComplexity.Examples.dwz63MarginalTypical_of_targetTypical
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetTypicalWords_subset_dwz63MarginalWords
#assert_axioms AlgebraicComplexity.Examples.dwz63MarginalKeep
#assert_axioms AlgebraicComplexity.Examples.dwz63MarginalTypicalPower
#assert_axioms AlgebraicComplexity.Examples.dwz63_restricts_positivePower_marginalTypical
#assert_axioms AlgebraicComplexity.Examples.dwz63JointRetainedSupportMarginal
#assert_axioms AlgebraicComplexity.Examples.dwz63_x_injOn_jointRetainedMarginal
#assert_axioms AlgebraicComplexity.Examples.exists_seed_dwz63JointRetainedMarginal
