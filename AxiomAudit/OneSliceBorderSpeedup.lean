/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.AlmanLiOneSliceSpeedup

set_option autoImplicit false

/-!
# Axiom audit for the border-rank one-slice speedup

Focused trust audit for the border-rank form of [AlmanLi2026, Theorem 6.1, p. 19] and the layers
it is built from: the polynomial-scalar calculus of `Tensor/PolynomialScalar.lean`, the kernel
frames of `Tensor/PolynomialKernelFrame.lean`, the presentation-independent core of
`Tensor/OneSliceBorderSpeedup.lean`, its matrix-multiplication instance in
`MatrixMultiplication/NonminimalBorderRankSpeedup.lean`, and the discharged statement
`AlmanLi.NonminimalBorderRankSpeedup` of `Examples/AlmanLiOneSliceSpeedup.lean`.
-/

namespace AlgebraicComplexity

#assert_axioms Tensor.PolynomialVector.mapLinear_polySMul
#assert_axioms Tensor.PolynomialVector.sum_polySMul_basis
#assert_axioms Tensor.polynomialPure_polySMul_X
#assert_axioms Tensor.polynomialPure_polySMul_Y
#assert_axioms Tensor.polynomialPure_polySMul_Z
#assert_axioms Tensor.polynomialPure_sum_polySMul_XY
#assert_axioms Tensor.hasLeadingTerm_polySMul_constant
#assert_axioms Tensor.exists_mul_coeff_eq_one_of_ne_zero
#assert_axioms Tensor.exists_polynomial_kernel_frame
#assert_axioms Tensor.exists_polynomial_kernel_frame_finset
#assert_axioms Tensor.PolynomialLinearMap.applyVector_ofBasis
#assert_axioms Tensor.polynomialTransform_oneSliceFrameTensor
#assert_axioms Tensor.BorderRankLE.exists_fin_family
#assert_axioms Tensor.sum_polynomialPure_cancel
#assert_axioms Tensor.sum_polynomialPure_kernel
#assert_axioms Tensor.sum_polynomialPure_frame
#assert_axioms Tensor.polynomialDegenerates_oneSliceFrameTensor_directSum
#assert_axioms oneSliceFrameTensor_eq_directSum_diagonalTensor
#assert_axioms polynomialDegenerates_diagonalTensor_oneSlice_of_borderRankLE
#assert_axioms AlmanLi.nonminimalBorderRankSpeedup

end AlgebraicComplexity
