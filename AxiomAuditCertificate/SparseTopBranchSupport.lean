/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SparseTopBranchSupport

set_option autoImplicit false

/-!
# Axiom audit for sparse level-four top support

These checks cover sparse support for the complete-split objects of [alman2025more,
`papers/sources/2404.16349/prelim.tex:249-278` and
`papers/sources/2404.16349/constituent.tex:41-47`].  The sparse address and chunk layout are
project-specific implementation invariants.
-/

namespace MatrixMultiplication.SparseTopBranchSupport

#assert_axioms topBranchEntryNumerator
#assert_axioms topNumeratorFrom_reconstructedTopBranchRows_eq_sum
#assert_axioms exists_massEntry_of_topNumeratorFrom_reconstructed_ne_zero

end MatrixMultiplication.SparseTopBranchSupport
