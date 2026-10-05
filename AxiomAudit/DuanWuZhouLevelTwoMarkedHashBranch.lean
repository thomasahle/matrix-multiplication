/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedHashBranch

set_option autoImplicit false

/-! # Axiom audit for the hashing branch at the joint type class

The branch in retention-loss form, its `4 |R|²` / Behrend form, and the wrapper that produces the
progression-free set.  The enlarged loss and the marginal-to-joint passage they rest on are
audited in `AxiomAudit/DuanWuZhouLevelTwoMarkedHashJointLoss.lean`.

Primary source: `[duan2023faster]`, the fixed-marginal count at
`papers/sources/2210.10173/hashing.tex:60-70` (`lem:numtriple_singledist` at `:63-70`) and its use
in the section 6.2 analysis at
`papers/sources/2210.10173/global_value.tex:130-140,292-323`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_markedBranch_pow_mul_retentionLoss_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_markedHashBranch
#assert_axioms AlgebraicComplexity.Examples.exists_behrend_dwz63_plainHashBranch_marked
