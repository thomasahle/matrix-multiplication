/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityRegion0Check
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityRegion1Check
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityRegion2Check
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityRegion3Check
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityRegion4Check
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityRegion5Check
import Mathlib.Tactic.FinCases

/-!
# Checked level-four child-row validity for all six regions

Certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` supplies only compact key lists.  This theorem is the semantic
endpoint: for repeated `XZY` orientation, every positive level-four parent in every diagonal
regional family has normalized labelled child rows.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity

open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

/-- All six diagonal regional families satisfy level-four child-row normalization. -/
theorem childRowsValid (region : Fin 6) :
    ∀ parent, LevelFourChildRowsValid
      Top.expectedRows BetaThree.expectedRows region region parent xzy := by
  fin_cases region
  · exact Region0.childRowsValid
  · exact Region1.childRowsValid
  · exact Region2.childRowsValid
  · exact Region3.childRowsValid
  · exact Region4.childRowsValid
  · exact Region5.childRowsValid

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity
