/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk8
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk9
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk10
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk11
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk12
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk13
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk14
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk15
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk16
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk17
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk18
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk19
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk20
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk21
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk22
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk23
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk24
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk25
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk26
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk27
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk28
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk29
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk30
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk31
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk32
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk33
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk34
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk35
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk36
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk37
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk38
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk39
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk40
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk41
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk42
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk43
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk44
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk45
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk46
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk47
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk48
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk49
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk50
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk51
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion2Chunk52
import Mathlib.Tactic.FinCases

/-!
# Semantic level-four child-row validity: region 2

For certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`, bounded parent-local index oracles check that the submitted
keys cover both labelled children of every active ordered split.  Separate bounded chunk proofs
establish each distinct key's normalization.  The reusable indexed soundness theorem then recovers
the original semantic proposition for all 105 positive parents.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region2

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
      BetaThree.expectedRows Keys.Region2.entries = true := by
  unfold Keys.Region2.entries
  exact by rfl

/-- Every positive parent in this region has normalized left and right child rows. -/
theorem childRowsValid :
    ∀ parent, LevelFourChildRowsValid
      Top.expectedRows BetaThree.expectedRows 2 2 parent xzy := by
  intro parent
  fin_cases parent
  · convert
      Coverage.Region2.Chunk0.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk0.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk1.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk1.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk2.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk2.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk3.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk3.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk4.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk4.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk5.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk5.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk6.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk6.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk7.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk7.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk8.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk8.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk9.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk9.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk10.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk10.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk11.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk11.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk12.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk12.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk13.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk13.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk14.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk14.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk15.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk15.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk16.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk16.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk17.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk17.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk18.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk18.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk19.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk19.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk20.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk20.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk21.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk21.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk22.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk22.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk23.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk23.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk24.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk24.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk25.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk25.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk26.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk26.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk27.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk27.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk28.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk28.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk29.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk29.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk30.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk30.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk31.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk31.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk32.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk32.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk33.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk33.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk34.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk34.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk35.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk35.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk36.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk36.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk37.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk37.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk38.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk38.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk39.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk39.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk40.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk40.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk41.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk41.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk42.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk42.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk43.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk43.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk44.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk44.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk45.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk45.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk46.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk46.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk47.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk47.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk48.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk48.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk49.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk49.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk50.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk50.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk51.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk51.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region2.Chunk52.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region2
