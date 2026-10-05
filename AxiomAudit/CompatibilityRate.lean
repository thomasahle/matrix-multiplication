/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Analysis.CompatibilityRate

/-! Focused trust audit for [DuanWuZhou2022] `lemma:pcomp_g`'s closed form for the combination-loss
rate `ᾱ_p` and for the modulus arithmetic of `claim:hole_frac_low`. -/

#assert_axioms AlgebraicComplexity.CompatibleSplit.SplitRequirements.compatibilityRate_eq_two_rpow
#assert_axioms AlgebraicComplexity.CompatibleSplit.SplitRequirements.rowEntropyMass_compatibleType
#assert_axioms AlgebraicComplexity.CompatibleSplit.SplitRequirements.rowEntropyMass_typicalType
#assert_axioms AlgebraicComplexity.CompatibleSplit.SplitRequirements.compatibilityRateLog_eq_dwz
#assert_axioms AlgebraicComplexity.CompatibleSplit.SplitRequirements.compatibleFraction_eq_prod_div_prod
#assert_axioms AlgebraicComplexity.CompatibleSplit.SplitRequirements.card_matchableCompatible_eq_mul_compatibleFraction
#assert_axioms AlgebraicComplexity.CompatibleSplit.SplitRequirements.eight_mul_card_matchableCompatible_le
#assert_axioms AlgebraicComplexity.CompatibleSplit.SplitRequirements.holeFraction_le
#assert_axioms AlgebraicComplexity.CompatibleSplit.SplitRequirements.seven_eighths_le_one_sub_holeFraction
