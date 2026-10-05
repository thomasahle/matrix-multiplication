/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTripleEntropy
import AxiomAudit.Command

/-! # Axiom audit for the DWZ level-two Gibbs-witness reading -/

#assert_axioms AlgebraicComplexity.Examples.profile_div_profileMass_le_one
#assert_axioms AlgebraicComplexity.Examples.profileEntropyNats_nonneg
#assert_axioms AlgebraicComplexity.Examples.dwz63GibbsX_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63GibbsY_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63GibbsZ_pos
#assert_axioms AlgebraicComplexity.Examples.exp_dwz63GibbsScore
#assert_axioms AlgebraicComplexity.Examples.dwz63_partition_dwz63GibbsScore
#assert_axioms AlgebraicComplexity.Examples.marginal_div_profileMass
