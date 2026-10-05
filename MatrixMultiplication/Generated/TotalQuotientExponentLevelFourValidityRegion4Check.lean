/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityNormalizationRegion4Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk8
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk9
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk10
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk11
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk12
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk13
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk14
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk15
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk16
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk17
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk18
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk19
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk20
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk21
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk22
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk23
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk24
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk25
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk26
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk27
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk28
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk29
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk30
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk31
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk32
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk33
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk34
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk35
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk36
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk37
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk38
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk39
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk40
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk41
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk42
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk43
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk44
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk45
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk46
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk47
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk48
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk49
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk50
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk51
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion4Chunk52
import Mathlib.Tactic.FinCases

/-!
# Semantic level-four child-row validity: region 4

For certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`, bounded parent-local index oracles check that the submitted
keys cover both labelled children of every active ordered split.  Separate bounded chunk proofs
establish each distinct key's normalization.  The reusable indexed soundness theorem then recovers
the original semantic proposition for all 105 positive parents.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region4

open AlgebraicComplexity.Tensor
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedRecursiveFiniteFamilies
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false
set_option autoImplicit false

/-- All submitted keys in this region name normalized beta-three rows. -/
theorem normalizationChecked :
    levelFourChildRowKeysNormalizedCheck
      BetaThree.expectedRows Keys.Region4.entries = true := by
  unfold Keys.Region4.entries
  exact Normalization.Region4.Chunk0.checked

/-- Every positive parent in this region has normalized left and right child rows. -/
theorem childRowsValid :
    ∀ parent, LevelFourChildRowsValid
      Top.expectedRows BetaThree.expectedRows 4 4 parent xzy := by
  intro parent
  fin_cases parent
  · convert
      Coverage.Region4.Chunk0.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk0.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk1.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk1.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk2.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk2.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk3.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk3.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk4.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk4.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk5.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk5.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk6.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk6.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk7.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk7.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk8.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk8.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk9.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk9.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk10.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk10.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk11.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk11.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk12.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk12.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk13.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk13.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk14.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk14.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk15.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk15.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk16.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk16.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk17.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk17.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk18.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk18.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk19.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk19.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk20.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk20.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk21.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk21.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk22.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk22.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk23.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk23.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk24.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk24.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk25.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk25.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk26.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk26.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk27.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk27.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk28.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk28.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk29.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk29.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk30.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk30.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk31.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk31.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk32.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk32.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk33.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk33.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk34.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk34.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk35.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk35.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk36.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk36.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk37.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk37.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk38.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk38.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk39.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk39.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk40.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk40.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk41.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk41.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk42.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk42.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk43.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk43.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk44.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk44.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk45.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk45.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk46.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk46.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk47.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk47.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk48.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk48.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk49.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk49.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk50.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk50.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk51.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk51.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region4.Chunk52.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region4
