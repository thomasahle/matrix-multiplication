/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainSharpDegree
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainRate

set_option autoImplicit false

/-! Focused trust audit for the plain fifteen-block rebuild of [DuanWuZhou2022] section 6.3's
counting step: the two counts `N_α` and `N_c`, the exact leg-fibre identity over the
marginal-typical ambient, the `hXfiber`/`hYfiber` obligations of
`exists_seed_dwz63PlainJointRetained` at the sharp degree, and the lossy branch rate with its
subexponential loss.

Everything is unconditional: no hypothesis beyond the forced word length, no `sorry`, no new
axiom. -/

-- The three leg marginals, below the orientation machinery.
#assert_axioms AlgebraicComplexity.Examples.mappedType_legRead_dwz63AlphaAddress
#assert_axioms AlgebraicComplexity.Examples.mappedType_legRead_proportionalCounts
#assert_axioms AlgebraicComplexity.Examples.mem_cwSquareSupport_of_dwz63AlphaAddress_ne_zero

-- The plain profile and the two counts.
#assert_axioms AlgebraicComplexity.Examples.mappedType_subtype_of_vanishing
#assert_axioms AlgebraicComplexity.Examples.profileMass_dwz63PlainAlpha
#assert_axioms AlgebraicComplexity.Examples.mappedType_dwz63PlainLegRead
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainJointCount_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainLegCount_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainLegCount_mul_card_typedWordMapFiber

-- The double count over the marginal-typical ambient.
#assert_axioms AlgebraicComplexity.Examples.card_dwz63PlainLegTargets
#assert_axioms AlgebraicComplexity.Examples.dwz63PlainMarginalWords_stable
#assert_axioms AlgebraicComplexity.Examples.card_dwz63PlainMarginalWords_eq
#assert_axioms AlgebraicComplexity.Examples.card_sourceWordLegFiber_le_sharpDegree

-- `hsharp` at the sharp degree, and the seed it certifies.
#assert_axioms AlgebraicComplexity.Examples.dwz63_plain_legFiber_le_sharpDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63_plain_hXfiber
#assert_axioms AlgebraicComplexity.Examples.dwz63_plain_hYfiber
#assert_axioms AlgebraicComplexity.Examples.exists_seed_dwz63PlainJointRetained_at_sharpDegree

-- The lossy branch and its subexponential loss.
#assert_axioms AlgebraicComplexity.Examples.dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount
#assert_axioms AlgebraicComplexity.Examples.subexponential_dwz63PlainLossHash
