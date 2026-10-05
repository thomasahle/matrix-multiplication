/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineComplementaryLetter

set_option autoImplicit false

/-! # Axiom audit for the complementary-letter facts and the completion

`[duan2023faster]`, section 6.1 `sec:global-algo`. -/

#assert_axioms AlgebraicComplexity.Examples.cwBlockDegree_injective
#assert_axioms AlgebraicComplexity.Examples.cwBlockComplement
#assert_axioms AlgebraicComplexity.Examples.cwBlockDegree_cwBlockComplement
#assert_axioms AlgebraicComplexity.Examples.mem_cwBlockSupport_ofLegs
#assert_axioms AlgebraicComplexity.Examples.cwBlock_eq_complement_of_zeroY
#assert_axioms AlgebraicComplexity.Examples.cwSquareComplementLetter
#assert_axioms AlgebraicComplexity.Examples.cwSquare_fineX_eq_complement_of_zeroY
#assert_axioms AlgebraicComplexity.Examples.cwBlockAddress_exists_split
