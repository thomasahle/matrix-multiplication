/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.SplitRequirementsLetterPushforward

set_option autoImplicit false

/-! # Axiom audit for the split-alphabet coarsening

Reusable project infrastructure, not a published theorem.  It serves `[duan2023faster]`,
section 6.1 `sec:global-algo`: the left-digit reading of `split`
(`papers/sources/2210.10173/global_value.tex:35`), the compatibility and usefulness definitions
(`:44-50`), and the compatibility probability `p_comp` (`:145-190`). -/

open AlgebraicComplexity.CompatibleSplit.SplitRequirements

#assert_axioms AlgebraicComplexity.WordType.mappedType_prodMap_snd_apply
#assert_axioms usefulType_letterPushforward
#assert_axioms typicalType_letterPushforward
#assert_axioms isCompatible_of_letterPushforward
#assert_axioms matchableCompatible_subset_of_letterPushforward
#assert_axioms card_matchableCompatible_le_of_letterPushforward
