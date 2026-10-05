/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoJointHashBranch

set_option autoImplicit false

/-! # Axiom audit -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_legCount_mul_retentionLoss_le_atDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63_branch_pow_mul_retentionLoss_le_atDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63_hashBranch_atDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63JointHashDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63_jointHashModulus_degree
#assert_axioms AlgebraicComplexity.Examples.dwz63_jointHashModulus_competitor
#assert_axioms AlgebraicComplexity.Examples.dwz63_jointHashModulus_seedSelection
#assert_axioms AlgebraicComplexity.Examples.dwz63JointHashDegree_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_legCount_mul_jointHashDegree_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_jointHashBranch
