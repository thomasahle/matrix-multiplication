/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCountingSplit

/-! Focused trust audit for the concrete `SplitRequirements` at the [DuanWuZhou2022] section 6.3
splits, and for the exact block counts it produces --- estimates (e) and (f) of
`better_bound/dwz_endpoint_prep/PREP.md` section 4.3.

Everything audited here is a *finite, exact* statement: an integral split table, its consistency
with the 15-cell distribution, the evaluated requirement rows, and the division-free product
closed forms for the compatible, typical and useful block counts.  No rate, no enclosure and no
asymptotic statement occurs, so nothing here is conditional. -/

/-! ## The split table and its consistency with the 15-cell distribution -/

#assert_axioms AlgebraicComplexity.Examples.dwz63Split_refinesType
#assert_axioms AlgebraicComplexity.Examples.dwz63Split_profileMass

/-! ## The requirement rows, evaluated -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_compatibleType_inl
#assert_axioms AlgebraicComplexity.Examples.dwz63_compatibleType_inr
#assert_axioms AlgebraicComplexity.Examples.dwz63_typicalType

/-! ## Estimates (e) and (f): the exact block counts -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_card_compatibleSet_eq_prod
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_typicalSet_eq_prod
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_usefulSet_eq_prod
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_usefulSet_le_card_compatibleSet

/-! ## Anti-vacuity and the competitor pair count -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_compatibleSet_nonempty
#assert_axioms AlgebraicComplexity.Examples.dwz63_typicalSet_nonempty
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_matchableCompatible_mul_card_typicalSet
