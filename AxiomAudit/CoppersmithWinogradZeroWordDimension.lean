/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroWordDimension
import AxiomAudit.Command

/-!
# Axiom audit for zero-coordinate CW word dimensions

Checks the exact zero-fiber dimension products and their split-word statistic identity.
-/

open AlgebraicComplexity.Examples

#assert_axioms positiveSupportWord_letter_z_eq_zero_of_address_z_eq_const
#assert_axioms positiveWordProduct_cwBaseDimension_X_eq_one_of_z_eq_const
#assert_axioms positiveWordProduct_cwBaseDimension_Y_eq_pow_middleCount_of_z_eq_const
#assert_axioms positiveWordProduct_cwBaseDimension_Z_eq_one_of_z_eq_const
#assert_axioms splitWordMiddleCount_cwChunkSplitWord_positiveSupportWordBlockAddress
