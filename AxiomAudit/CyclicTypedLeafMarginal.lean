/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.CyclicTypedLeafMarginal

/-! # Axiom audit for the three marginals of a cyclic product leaf

Each component of the three-orientation product marginal is the corresponding source marginal,
scaled by the square of the profile mass. -/

set_option autoImplicit false

open AlgebraicComplexity.RationalTypedLeaf

#assert_axioms marginalProfile_cyclicProduct_fst_fst
#assert_axioms marginalProfile_cyclicProduct_fst_snd
#assert_axioms marginalProfile_cyclicProduct_snd
