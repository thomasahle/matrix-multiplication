/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.AlmanLiOneSliceSpeedup
import AlgebraicComplexity.MatrixMultiplication.DirectSumIdentityBound

set_option autoImplicit false

/-!
# Axiom audit for the Alman–Li direct-sum identity

Focused trust audit for [AlmanLi2026, Theorem 7.3, p. 29] and its consequences: the identity in
standard coordinates and in the indexed-direct-sum presentation
(`MatrixMultiplication/DirectSumIdentity.lean`), the discharged statement
`AlmanLi.DirectSumIdentity` (`Examples/AlmanLiOneSliceSpeedup.lean`), and the exponent bounds of
`MatrixMultiplication/DirectSumIdentityBound.lean`, including Schönhage's inequality for all
sizes and `ω < 2.55`.
-/

namespace AlgebraicComplexity

#assert_axioms DSCol
#assert_axioms DSIndex
#assert_axioms DSRow
#assert_axioms DSSliceSpace
#assert_axioms Tensor.map_pure_ofLegs
#assert_axioms Tensor.pure_ofLegs_sum_X
#assert_axioms Tensor.pure_ofLegs_sum_Y
#assert_axioms basisFun_constr_single
#assert_axioms dsA
#assert_axioms dsB
#assert_axioms dsF
#assert_axioms dsG
#assert_axioms dsGX
#assert_axioms dsGY
#assert_axioms dsMMToSource
#assert_axioms dsSliceX
#assert_axioms dsSliceY
#assert_axioms dsSliceZ
#assert_axioms dsSource
#assert_axioms dsUnitIndex
#assert_axioms dsUnitToSource
#assert_axioms instDecidableEqDSIndex
#assert_axioms instFintypeDSIndex
#assert_axioms map_dsF_dsF_dsG_dsSource
#assert_axioms map_dsF_dsG_dsG_dsSource
#assert_axioms map_dsF_dsSource
#assert_axioms map_dsG_dsF_dsG_dsSource
#assert_axioms map_dsG_dsSource
#assert_axioms oneSliceDirectSum_eq_sum_dsSlice
#assert_axioms polynomialDegenerates_dsSource
#assert_axioms polynomialDegenerates_unit_directSum_matrixMultiplication
#assert_axioms restricts_directSum_dsSource
#assert_axioms sum_dsA
#assert_axioms sum_dsB
#assert_axioms borderRankLE_directSum_slices
#assert_axioms directSumIdentity_asymptoticSum
#assert_axioms dsOptM
#assert_axioms dsOptN
#assert_axioms dsOptP
#assert_axioms omega_lt_of_schonhage_four
#assert_axioms rankLE_dsSource
#assert_axioms restricts_directSum_slices_option
#assert_axioms schonhage_asymptoticSum_general
#assert_axioms AlmanLi.directSumIdentity

end AlgebraicComplexity
