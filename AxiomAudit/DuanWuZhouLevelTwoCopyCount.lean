/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCopyCount

set_option autoImplicit false

/-! # Axiom audit for the level-two copy count of `[DuanWuZhou2022]` section 6.3

The integer-to-real floor conversion; the hashing branch of the true copy rate and the `min`
comparison against it; the subexponential loss the chain accumulates; the hash step; and the
three assembled forms of `hcount`. -/

#assert_axioms AlgebraicComplexity.Examples.card_le_ratio_mul_of_nat_le
#assert_axioms AlgebraicComplexity.Examples.dwz63HashingBranch
#assert_axioms AlgebraicComplexity.Examples.dwz63HashingBranch_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63TrueCopyRate_le_hashingBranch
#assert_axioms AlgebraicComplexity.Examples.dwz63TrueCopyRate_pow_le_hashingBranch_pow
#assert_axioms AlgebraicComplexity.Examples.dwz63CopyCountLoss
#assert_axioms AlgebraicComplexity.Examples.subexponential_dwz63CopyCountLoss
#assert_axioms AlgebraicComplexity.Examples.dwz63_hashingBranch_pow_le_card_jointRetained
#assert_axioms AlgebraicComplexity.Examples.dwz63_copyCount_of_estimates
#assert_axioms AlgebraicComplexity.Examples.dwz63_copyCount_of_estimates_natFloor
#assert_axioms AlgebraicComplexity.Examples.dwz63_copyCount_fintype_of_estimates
#assert_axioms AlgebraicComplexity.Examples.pos_of_copyCount_le
#assert_axioms AlgebraicComplexity.Examples.card_dwz63JointIsolatedSupport_pos
#assert_axioms AlgebraicComplexity.Examples.fintype_card_dwz63JointIsolatedSupport_pos
