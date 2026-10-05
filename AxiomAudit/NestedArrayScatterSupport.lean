/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.NestedArrayScatterSupport

set_option autoImplicit false

/-!
# Axiom audit for additive three-level array scatters

This checks the reusable sparse-reconstruction support lemmas used by [alman2025more].
-/

namespace MatrixMultiplication.NestedArrayScatterSupport

#assert_axioms readCell3
#assert_axioms addCell3
#assert_axioms Cell3InBounds
#assert_axioms readCell3_addCell3
#assert_axioms foldl_readCell3
#assert_axioms exists_entry_of_readCell3_foldl_ne_zero

end MatrixMultiplication.NestedArrayScatterSupport
