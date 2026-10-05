/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting

/-! Focused trust audit for the 15-cell distribution of [DuanWuZhou2022] section 6.3, its three
coordinate marginals, and the two ambient method-of-types estimates of
`better_bound/dwz_endpoint_prep/PREP.md` section 4.3.

Three groups are audited: the exact marginal identities that connect the 15-cell distribution to
the two five-letter profiles the previous module's estimates (b) and (c) are stated over; the
ambient estimate (a), which uses no numerical value of `H(alpha)`; and estimate (d), whose
polynomial half is proved here and whose maximum-entropy half is the single named hypothesis
`Dwz63TripleEntropyBound`.

Estimate (d)'s conclusion is **conditional** on that hypothesis; the audit records only that its
proof uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`. -/

/-! ## The generic pushforward/repetition compatibility -/

#assert_axioms AlgebraicComplexity.Examples.mappedType_proportionalCounts

/-! ## The 15-cell distribution and its three marginals -/

#assert_axioms AlgebraicComplexity.Examples.profileMass_dwz63Alpha
#assert_axioms AlgebraicComplexity.Examples.profileMass_dwz63Alpha_pos
#assert_axioms AlgebraicComplexity.Examples.mappedType_dwz63XIndex_dwz63Alpha
#assert_axioms AlgebraicComplexity.Examples.mappedType_dwz63YIndex_dwz63Alpha
#assert_axioms AlgebraicComplexity.Examples.mappedType_dwz63ZIndex_dwz63Alpha
#assert_axioms AlgebraicComplexity.Examples.mappedType_dwz63XIndex_proportionalCounts
#assert_axioms AlgebraicComplexity.Examples.mappedType_dwz63YIndex_proportionalCounts
#assert_axioms AlgebraicComplexity.Examples.mappedType_dwz63ZIndex_proportionalCounts
#assert_axioms AlgebraicComplexity.Examples.proportionalCounts_dwz63Alpha_mem_types

/-! ## Estimate (a): the ambient count -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_ambientRate_pow_le_loss_mul_card_typeClass
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_cutoff_pow_le_card_ambientTypeClass

/-! ## Estimate (d): the triple count, modulo one named hypothesis -/

#assert_axioms AlgebraicComplexity.Examples.mem_dwz63TripleSet
#assert_axioms AlgebraicComplexity.Examples.dwz63_tripleEntropyBound_premises
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_tripleSet_le_typeCountLoss_mul

/-! ## Step (1): Bertrand -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_four_mul_modulus_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_requirement_lt_modulus
