/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PositiveWordProduct
import AxiomAudit.Command

/-!
# Axiom audit for positive-word products

This audit keeps the lightweight word-dimension layer visibly free of project-specific axioms.
-/

#assert_axioms AlgebraicComplexity.positiveWordProduct
#assert_axioms AlgebraicComplexity.positiveWordProduct_zero
#assert_axioms AlgebraicComplexity.positiveWordProduct_succ
#assert_axioms AlgebraicComplexity.positiveWordProduct_pos_of_forall
#assert_axioms AlgebraicComplexity.positiveWordProduct_eq_fin_prod
