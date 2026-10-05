/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeightBeta

set_option autoImplicit false

/-! # Axiom audit for the free-`beta` `(1,2,1)` / `(2,1,1)` orbit leaf weight -/

#assert_axioms AlgebraicComplexity.Examples.dwz121Mass_eq
#assert_axioms AlgebraicComplexity.Examples.dwz121Stride_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63LogVal_beta_atom_coefficients
#assert_axioms AlgebraicComplexity.Examples.dwz121InnerCopyBase_pos
#assert_axioms AlgebraicComplexity.Examples.dwz121InnerCopyBase_lt
#assert_axioms AlgebraicComplexity.Examples.log_dwz121InnerEntropyBase
#assert_axioms AlgebraicComplexity.Examples.log_dwz121InnerCopyBase
#assert_axioms AlgebraicComplexity.Examples.log_dwz121InnerDimensionVolume
#assert_axioms AlgebraicComplexity.Examples.dwz121LeafTerm_pos
#assert_axioms AlgebraicComplexity.Examples.scaled_log_dwz121LeafTerm
#assert_axioms AlgebraicComplexity.Examples.log_dwz121LeafTerm_eq
#assert_axioms AlgebraicComplexity.Examples.dwz121LogValue_sub_le_log_dwz121LeafTerm
#assert_axioms AlgebraicComplexity.Examples.dwz121_exp_le_leafTerm
#assert_axioms AlgebraicComplexity.Examples.exists_eventually_dwz121LeafHasTauWeight
#assert_axioms AlgebraicComplexity.Examples.exists_eventually_dwz121ConstituentHasTauWeight
#assert_axioms AlgebraicComplexity.Examples.dwz121LogValue_eq_paperForm
#assert_axioms AlgebraicComplexity.Examples.exists_eventually_dwz121LeafHasTauWeight_exp
