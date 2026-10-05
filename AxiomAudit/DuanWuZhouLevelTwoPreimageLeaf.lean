/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPreimageLeaf

set_option autoImplicit false

/-! # Axiom audit for the isolated fibre and the Step 2 holes -/

#assert_axioms AlgebraicComplexity.Examples.dwz63PreimageYSupport_eq
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63PreimageZSupport
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63IsolationHoles
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63PreimageGrouping_fiber_support
#assert_axioms AlgebraicComplexity.Examples.dwz63PreimageGrouping_fiber_select_eq
#assert_axioms AlgebraicComplexity.Examples.segmentedAvailable_position_symm
#assert_axioms AlgebraicComplexity.Examples.dwz63ReferenceHoles_image
#assert_axioms AlgebraicComplexity.Examples.dwz63_preimageFiber_restricts_brokenReferenceLeaf
