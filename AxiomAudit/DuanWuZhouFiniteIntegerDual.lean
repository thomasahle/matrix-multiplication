/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DuanWuZhouFiniteIntegerDual

set_option autoImplicit false

/-!
# Axiom audit for the finite DWZ integer dual

All eleven public declarations of the [duan2023faster] global-alpha integer-factor client are
checked against the standard allowlist, including the three finite factor definitions.
-/

#assert_axioms AlgebraicComplexity.Examples.dwz63IntegerGibbsX
#assert_axioms AlgebraicComplexity.Examples.dwz63IntegerGibbsY
#assert_axioms AlgebraicComplexity.Examples.dwz63IntegerGibbsZ
#assert_axioms AlgebraicComplexity.Examples.dwz63_integerGibbs_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_integerGibbs_scale
#assert_axioms AlgebraicComplexity.Examples.dwz63_integerGibbs_score_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_globalAlpha_isProbability
#assert_axioms AlgebraicComplexity.Examples.dwz63_globalAlpha_entropy_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_integerPartition_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_integerDualGap_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_combinationLossBits_le_log_hashLossMultiplier
