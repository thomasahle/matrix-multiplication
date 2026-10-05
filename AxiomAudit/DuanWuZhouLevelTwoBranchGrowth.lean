/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoBranchGrowth

/-! Focused trust audit for the hashing-branch growth facts: the branch is above one, a
subexponential times an affine factor is eventually dominated by any power above one, and the
batching requirement is eventually below the branch power.

Paper step: `[duan2023faster]` §6.3's level-two parameters
(`papers/sources/2210.10173/global_value.tex:332-378`, `table:result-2nd`), feeding the
asymmetric-hashing modulus paragraph (`:130-140`). -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_one_lt_hashingBranch
#assert_axioms AlgebraicComplexity.Examples.dwz63_eventually_subexp_mul_affine_le_pow
#assert_axioms AlgebraicComplexity.Examples.dwz63_eventually_hlarge_le_branch_pow
