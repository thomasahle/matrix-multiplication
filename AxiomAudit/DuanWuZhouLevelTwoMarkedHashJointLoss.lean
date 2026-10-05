/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedHashJointLoss

set_option autoImplicit false

/-! # Axiom audit for the joint-class hash loss and the marginal-to-joint passage

The enlarged loss `dwz63PlainMarkedLossHashJoint` with its positivity and subexponentiality, the
identification of the marginal-typical family with the bridge's ambient family, the counting
passage from that family to the joint type class, and the containment in the other direction.

Primary source: `[duan2023faster]`, the fixed-marginal count at
`papers/sources/2210.10173/hashing.tex:60-70` (`lem:numtriple_singledist` at `:63-70`) and its use
in the section 6.2 analysis at
`papers/sources/2210.10173/global_value.tex:130-140,292-323`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarkedLossHashJoint
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarkedLossHashJoint_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarkedLossHashJoint_nonneg
#assert_axioms AlgebraicComplexity.Examples.subexponential_dwz63PlainMarkedLossHashJoint
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainMarginalWords_eq_ambientWords
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_plainMarginalWords_le_marked
#assert_axioms AlgebraicComplexity.Examples.dwz63_markedWords_subset_plainMarginalWords
