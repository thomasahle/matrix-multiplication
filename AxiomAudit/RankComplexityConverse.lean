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
#assert_axioms Circuit.exists_bilSpan
#assert_axioms Circuit.mapCoeff
#assert_axioms Circuit.mapCoeff_id
#assert_axioms Circuit.mapCoeff_mapCoeff
#assert_axioms Circuit.mulOps_mapCoeff
#assert_axioms Straightline.eval_mapCoeff
#assert_axioms Straightline.exists_bilSpan
#assert_axioms Straightline.mapCoeff
#assert_axioms Straightline.mapCoeff_id
#assert_axioms Straightline.mapCoeff_mapCoeff
#assert_axioms Straightline.mulOps_mapCoeff
#assert_axioms Trunc
#assert_axioms Trunc.bil
#assert_axioms Trunc.bil_add
#assert_axioms Trunc.bil_monomial
#assert_axioms Trunc.bil_mul
#assert_axioms Trunc.bil_ofScalar
#assert_axioms Trunc.bil_sum
#assert_axioms Trunc.bil_varX
#assert_axioms Trunc.bil_varY
#assert_axioms Trunc.bil_zero
#assert_axioms Trunc.const
#assert_axioms Trunc.const_add
#assert_axioms Trunc.const_mul
#assert_axioms Trunc.const_ofScalar
#assert_axioms Trunc.const_varX
#assert_axioms Trunc.const_varY
#assert_axioms Trunc.linX
#assert_axioms Trunc.linX_add
#assert_axioms Trunc.linX_mul
#assert_axioms Trunc.linX_ofScalar
#assert_axioms Trunc.linX_varX
#assert_axioms Trunc.linX_varY
#assert_axioms Trunc.linY
#assert_axioms Trunc.linY_add
#assert_axioms Trunc.linY_mul
#assert_axioms Trunc.linY_ofScalar
#assert_axioms Trunc.linY_varX
#assert_axioms Trunc.linY_varY
#assert_axioms Trunc.ofScalar
#assert_axioms Trunc.ofScalarHom
#assert_axioms Trunc.ofScalarHom_apply
#assert_axioms Trunc.varX
#assert_axioms Trunc.varY
#assert_axioms TruncX
#assert_axioms bilSpan
#assert_axioms bilSpan_mono
#assert_axioms exists_bilinearAlgorithm_of_straightline
#assert_axioms omega_le_iff_exists_straightline
#assert_axioms omega_le_of_straightline
#assert_axioms rankLE_matrixMultiplication_of_straightline
#assert_axioms rankOneGens
#assert_axioms rankOne_mem_bilSpan

end AlgebraicComplexity
