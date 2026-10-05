/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MergedLeafClassFactor
import AxiomAudit.Command

/-!
# Axiom audit for the merged-leaf letterwise premise

Checks the merged one-slice factor's dimensions and the adapter that turns the single named premise
`MergedLetterClassFactor` into the letterwise degeneration every merged typed-leaf consumer takes.
-/

open AlgebraicComplexity

#assert_axioms MergedRationalTypedLeaf.factorDimension
#assert_axioms MergedRationalTypedLeaf.factorDimension_self
#assert_axioms MergedRationalTypedLeaf.factorDimension_of_ne
#assert_axioms MergedRationalTypedLeaf.MergedLetterClassFactor
#assert_axioms MergedRationalTypedLeaf.restricts_toRationalTypedLeaf_dimension_of_letterClassFactor
