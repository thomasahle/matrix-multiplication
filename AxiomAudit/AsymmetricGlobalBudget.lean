/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.AsymmetricGlobalBudget

/-! Focused trust audit for the budget arithmetic of [DuanWuZhou2022]'s global analysis: the
available-block count of `hole_lemma.tex`, the passage from the paper's `∑ η ≥ Nℓ + 1` to the
finite Hole-Lemma inequality, and the two branches of the modulus `M₀`. -/

#assert_axioms AlgebraicComplexity.AsymmetricGlobal.card_availableWord_le_pow
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.succ_two_pow_pred_le_two_pow
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.card_availableWord_le_two_pow_mul
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.card_availableWord_le_two_pow_mul_of_level
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.card_availableWord_pos
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.prod_one_sub_le_exp_neg_sum
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.holeBudget_of_etaSum
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.holeBudget_of_eight_mul_card_le
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.restrictedSplittingHoleRepair_of_eight_mul_card_le
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.quarter_of_globalModulusBound
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.eight_mul_le_of_globalModulusBound
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.globalModulusBound_branches
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.holeFraction_le_of_modulus
