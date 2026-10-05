/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SixSymmetrizedValue

/-! Focused trust audit for the six-symmetrized value `V^{(6)}` of `[DuanWuZhou2022]` §2.2, the
leg-permutation action on polynomial degenerations that supports it, and the three comparison laws
`V^{(6)} ≥ V^{(3)} ≥ V^{(nrot)}` together with the `X`–`Y` symmetric equality. -/

#assert_axioms AlgebraicComplexity.Tensor.PolynomialDegeneratesAt.permute
#assert_axioms AlgebraicComplexity.Tensor.PolynomialDegenerates.permute
#assert_axioms AlgebraicComplexity.symSix_eq_sixOrientationProduct
#assert_axioms AlgebraicComplexity.HasTauWeight.permute_swapXY
#assert_axioms AlgebraicComplexity.HasTauWeight.symThree_pow_three
#assert_axioms AlgebraicComplexity.HasTauWeight.symSix_pow_two
#assert_axioms AlgebraicComplexity.tauValue_pow_three_le_tauValue_symThree
#assert_axioms AlgebraicComplexity.tauValue_symThree_pow_two_le_tauValue_symSix
#assert_axioms AlgebraicComplexity.tauValue_le_threeValue
#assert_axioms AlgebraicComplexity.threeValue_le_sixValue
#assert_axioms AlgebraicComplexity.Isomorphic.symSix_of_swapSymmetric
#assert_axioms AlgebraicComplexity.sixValue_eq_threeValue_of_swapSymmetric
#assert_axioms AlgebraicComplexity.degenerationValue_le_threeValue
#assert_axioms AlgebraicComplexity.threeValue_le_degenerationValue
