/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.KoszulBorderRank

/-!
# Axiom audit for the explicit Koszul lower-bound certificate

This focused audit checks the symbolic biorthogonality calculation, the resulting linear
independence theorem, and the exact-rank lower bound `rank ⟨2,2,2⟩ ≥ 6`.  Keeping it separate from
the compatibility audit makes changes to the finite certificate cheap to verify.
-/

#assert_axioms AlgebraicComplexity.koszulTwoTest_koszulFlattening
#assert_axioms AlgebraicComplexity.linearIndependent_koszulFlattening_two
#assert_axioms AlgebraicComplexity.six_le_rank_matrixMultiplication_two_koszul
