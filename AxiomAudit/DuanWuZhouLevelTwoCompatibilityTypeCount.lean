/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompatibilityTypeCount

set_option autoImplicit false

/-! Focused trust audit for the method-of-types half of `Dwz63CompatibleFractionUpper`
(`[DuanWuZhou2022]` section 6.2, `lemma:pcomp_g`).

Everything audited here is unconditional: the polynomial slack and its subexponentiality, the two
zero-tolerant Stirling directions on a single profile row, their products over the requirement
cells and the Z-indices, and the resulting brick under the single hypothesis
`compatibilityLogLoss ≤ n · rateLog`.  No section 6.3 number enters this module, so nothing here
depends on a certificate. -/

/-! ## The polynomial slack -/

#assert_axioms AlgebraicComplexity.Examples.dwz63CompatSlack
#assert_axioms AlgebraicComplexity.Examples.dwz63CompatSlack_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63CompatSlack_subexponential
#assert_axioms AlgebraicComplexity.Examples.dwz63CompatSlack_eq_typeClassEntropyLoss_pow

/-! ## The two zero-tolerant row estimates -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_multinomial_le_exp_profileMassEntropy
#assert_axioms AlgebraicComplexity.Examples.dwz63_typeClassEntropyLoss_mono
#assert_axioms AlgebraicComplexity.Examples.dwz63_one_le_typeClassEntropyLoss
#assert_axioms AlgebraicComplexity.Examples.dwz63_exp_profileMassEntropy_le_loss_mul_multinomial

/-! ## The two product estimates -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_prod_multinomial_le_exp_rowEntropyMass
#assert_axioms AlgebraicComplexity.Examples.dwz63_exp_rowEntropyMass_le_slack_mul_prod_multinomial

/-! ## The brick, from the conditional-entropy mass -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_compatibleFractionUpper_of_compatibilityLogLoss_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_compatibleFractionUpper_of_compatibilityRateLog_le
