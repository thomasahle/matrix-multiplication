/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoRegionalLeafWeight

/-! # Axiom audit for the section 6.3 leaf's `sym₆`-weight

A cell weighed by the fine route is a region entry, and the fifteen regions compose into the
leaf's `sym₆`-weight --- the shape the batched endpoint's `hleafWeight` binder consumes.  The
composition is unconditional; its conclusion is conditional on the fifteen-weight bundle `hw`.

Primary source: `[duan2023faster]`, section 6.3 (the level-two global-value example),
`papers/sources/2210.10173/global_value.tex:332-348`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_symSix_regionEntry_logVal
#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_symSix_referenceLeaf_of_regional
