/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoRegionalLeafAssembly

/-! # Axiom audit for the assembled `sym₆`-weight of the section 6.3 leaf

The two strengthened packagings of image 96 and the list-level assembly of the fifteen region
entries into one `HasTauWeight` fact in `hleafWeight`'s shape. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63NestedValue
#assert_axioms AlgebraicComplexity.Examples.dwz63_totalValue_consecutiveBlocks
#assert_axioms AlgebraicComplexity.Examples.dwz63_nestedValue_eq_prod
#assert_axioms AlgebraicComplexity.Examples.dwz63_nestedValue_regionValue
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_consecutiveBlocks'
#assert_axioms AlgebraicComplexity.Examples.dwz63_referenceLeaf_isomorphic_consecutive'
#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_symSix_referenceLeaf
