/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradDepthOneRateBarrierArithmetic

/-!
# Axiom audit for the depth-one CW rate obstruction

This audit covers the reusable finite-conditioning and entropy-mixture spine, the exact
36-letter geometry, and the directed rational calculation proving the `433/1000` obstruction.
The endpoint is a diagnostic for the obsolete global-competitor route; it is not itself a
matrix-multiplication exponent bound.
-/

#assert_axioms AlgebraicComplexity.ProbabilityVector.mixture_conditionOnFiber
#assert_axioms AlgebraicComplexity.ProbabilityVector.entropyBits_pair_sub_mul_entropyBits_coarse_mixture_le
#assert_axioms AlgebraicComplexity.ProbabilityVector.entropyBits_pair_sub_two_mul_entropyBits_coarse_boolConditioning_le
#assert_axioms AlgebraicComplexity.ProbabilityVector.entropyBits_le_one_of_card_positiveSupport_le_two
#assert_axioms AlgebraicComplexity.ProbabilityVector.entropyBits_bool_eq_binEntropy_weight_true_div_log_two
#assert_axioms AlgebraicComplexity.Examples.card_cwDepthOneEventCoarseFiber_le_two
#assert_axioms AlgebraicComplexity.Examples.exists_leg_entropyBits_pair_sub_two_mul_coarse_le_zero_of_noCorner
#assert_axioms AlgebraicComplexity.Examples.exists_leg_depthOne_rateResidual_le_cornerEntropy_add_mass
#assert_axioms AlgebraicComplexity.Examples.cwDepthOne_binEntropy_nine_div_152_add_lt
#assert_axioms AlgebraicComplexity.Examples.exists_leg_depthOne_rateResidual_lt_433_div_1000
