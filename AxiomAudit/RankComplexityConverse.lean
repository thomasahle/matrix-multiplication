/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.RankComplexityConverse

set_option autoImplicit false

/-!
# Axiom audit for the converse of Proposition 2.7

Focused trust audit for `MatrixMultiplication/RankComplexityConverse.lean`: Strassen's bound of
the rank of a bilinear map by twice the number of multiplication gates of a straight-line program
computing it, and the resulting equivalence between the rank-growth exponent `omega` and the
exponent of arithmetic complexity over an infinite field.
-/

namespace AlgebraicComplexity

#assert_axioms Circuit.eval_mapCoeff
#assert_axioms Straightline.eval_mapCoeff
#assert_axioms Trunc.bil_mul
#assert_axioms Trunc.bil_monomial
#assert_axioms Circuit.exists_bilSpan
#assert_axioms Straightline.exists_bilSpan
#assert_axioms exists_bilinearAlgorithm_of_straightline
#assert_axioms rankLE_matrixMultiplication_of_straightline
#assert_axioms omega_le_of_straightline
#assert_axioms omega_le_iff_exists_straightline

end AlgebraicComplexity
