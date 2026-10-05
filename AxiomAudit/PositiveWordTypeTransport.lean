/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.PositiveWordTypeTransport

/-! Focused trust audit for the reference-frame transport: the position permutation between two
positive words of the same letter type, its block-address form, and the family form that supplies
the localized stage's `perm`/`hperm`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.exists_positiveWordPositionEquiv_of_multiplicity_eq
#assert_axioms AlgebraicComplexity.exists_positiveSupportWordBlockAddress_position
#assert_axioms AlgebraicComplexity.exists_perm_positiveSupportWordBlockAddress
