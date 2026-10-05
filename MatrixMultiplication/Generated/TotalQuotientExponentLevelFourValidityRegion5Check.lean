/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityNormalizationRegion5Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk8
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk9
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk10
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk11
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk12
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk13
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk14
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk15
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk16
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk17
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk18
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk19
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk20
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk21
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk22
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk23
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk24
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk25
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk26
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk27
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk28
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk29
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk30
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk31
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk32
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk33
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk34
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk35
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk36
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk37
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk38
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk39
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk40
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk41
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk42
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk43
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk44
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk45
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk46
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk47
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk48
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk49
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk50
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk51
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion5Chunk52
import Mathlib.Tactic.FinCases

/-!
# Semantic level-four child-row validity: region 5

For certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`, bounded parent-local index oracles check that the submitted
keys cover both labelled children of every active ordered split.  Separate bounded chunk proofs
establish each distinct key's normalization.  The reusable indexed soundness theorem then recovers
the original semantic proposition for all 105 positive parents.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region5

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
      BetaThree.expectedRows Keys.Region5.entries = true := by
  unfold Keys.Region5.entries
  exact Normalization.Region5.Chunk0.checked

/-- Every positive parent in this region has normalized left and right child rows. -/
theorem childRowsValid :
    ∀ parent, LevelFourChildRowsValid
      Top.expectedRows BetaThree.expectedRows 5 5 parent xzy := by
  intro parent
  fin_cases parent
  · convert
      Coverage.Region5.Chunk0.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk0.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk1.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk1.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk2.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk2.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk3.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk3.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk4.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk4.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk5.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk5.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk6.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk6.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk7.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk7.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk8.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk8.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk9.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk9.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk10.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk10.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk11.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk11.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk12.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk12.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk13.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk13.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk14.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk14.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk15.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk15.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk16.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk16.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk17.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk17.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk18.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk18.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk19.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk19.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk20.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk20.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk21.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk21.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk22.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk22.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk23.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk23.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk24.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk24.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk25.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk25.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk26.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk26.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk27.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk27.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk28.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk28.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk29.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk29.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk30.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk30.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk31.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk31.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk32.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk32.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk33.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk33.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk34.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk34.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk35.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk35.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk36.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk36.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk37.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk37.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk38.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk38.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk39.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk39.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk40.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk40.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk41.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk41.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk42.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk42.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk43.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk43.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk44.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk44.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk45.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk45.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk46.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk46.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk47.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk47.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk48.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk48.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk49.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk49.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk50.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk50.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk51.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk51.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region5.Chunk52.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region5
