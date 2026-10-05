/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSharpDegree

set_option autoImplicit false

/-! # Axiom audit for the sharp leg-fiber degree

The six orientations' leg-source computation, the marginals each leg reads, the rounded sharp
degree with its division-free specification, the sharp hashing parameters, and hash retention at a
certified degree. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63SymSixOrientation
#assert_axioms AlgebraicComplexity.Examples.dwz63SymSixLegSource
#assert_axioms AlgebraicComplexity.Examples.dwz63SymSixXLegSource_values
#assert_axioms AlgebraicComplexity.Examples.dwz63SymSixZLegSource_values
#assert_axioms AlgebraicComplexity.Examples.dwz63SymSixYLegSource_values
#assert_axioms AlgebraicComplexity.Examples.dwz63SymSix_legSource_count
#assert_axioms
  AlgebraicComplexity.Examples.dwz63SymSix_xLegSource_multiset_eq_zLegSource_multiset
#assert_axioms AlgebraicComplexity.Examples.dwz63LegSourceMarginal
#assert_axioms AlgebraicComplexity.Examples.dwz63LegSourceMarginal_X
#assert_axioms AlgebraicComplexity.Examples.dwz63LegSourceMarginal_Z
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpDegree_spec
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpDegree_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpHashModulus
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpHashModulus_char_floor
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpHashModulus_requirement
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpHashModulus_le
#assert_axioms AlgebraicComplexity.Examples.card_dwz63SharpHashField
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpModulusLoss
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpBehrendLoss
#assert_axioms AlgebraicComplexity.Examples.dwz63SharpRetentionLoss
#assert_axioms AlgebraicComplexity.Examples.dwz63_retained_card_lower_sharp
#assert_axioms AlgebraicComplexity.Examples.Dwz63SharpRateStatement
