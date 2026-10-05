/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellGeneral

/-! # Axiom audit for the general zero-coordinate fine cell

The third leg and the pair complement, the forced fine letter in either zero frame with its
supportedness, the cell's coarse target, the witness address with its leg readings and coarsening,
the type-class injection for every cell `(0, 4-k, k)` and its mirror, the two-case `huniform`, and
the eventual entropy-rate weight. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63ThirdLeg
#assert_axioms AlgebraicComplexity.Examples.dwz63PairComplement
#assert_axioms AlgebraicComplexity.Examples.dwz63_squareBlockDegree_pairComplement
#assert_axioms AlgebraicComplexity.Examples.dwz63_wordMiddleCount_pairComplement
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroFineLetterAddress
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroFineLetterAddress_mem
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroFineLetter
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroCellTarget
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroCellTarget_self
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroFineWitness
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroFineWitness_equiv
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroFineWitness_zero
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroFineWitness_Z
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroFineWitness_mem
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroFineWitness_coarsens
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_typeClass_le_zeroFineCellSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellPower_cellOnes_eq_alphaSum
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_zeroFineCellWeight
