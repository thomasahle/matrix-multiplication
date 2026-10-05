/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk8
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk9
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk10
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk11
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk12
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk13
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk14
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk15
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk16
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk17
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk18
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk19
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk20
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk21
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk22
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk23
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk24
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk25
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk26
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk27
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk28
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk29
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk30
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk31
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk32
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk33
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk34
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk35
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk36
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk37
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk38
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk39
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk40
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk41
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk42
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk43
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk44
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk45
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk46
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk47
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk48
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk49
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk50
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk51
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion3Chunk52
import Mathlib.Tactic.FinCases

/-!
# Semantic level-four child-row validity: region 3

For certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`, bounded parent-local index oracles check that the submitted
keys cover both labelled children of every active ordered split.  Separate bounded chunk proofs
establish each distinct key's normalization.  The reusable indexed soundness theorem then recovers
the original semantic proposition for all 105 positive parents.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region3

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
      BetaThree.expectedRows Keys.Region3.entries = true := by
  unfold Keys.Region3.entries
  exact by rfl

/-- Every positive parent in this region has normalized left and right child rows. -/
theorem childRowsValid :
    ∀ parent, LevelFourChildRowsValid
      Top.expectedRows BetaThree.expectedRows 3 3 parent xzy := by
  intro parent
  fin_cases parent
  · convert
      Coverage.Region3.Chunk0.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk0.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk1.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk1.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk2.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk2.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk3.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk3.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk4.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk4.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk5.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk5.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk6.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk6.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk7.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk7.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk8.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk8.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk9.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk9.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk10.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk10.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk11.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk11.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk12.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk12.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk13.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk13.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk14.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk14.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk15.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk15.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk16.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk16.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk17.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk17.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk18.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk18.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk19.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk19.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk20.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk20.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk21.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk21.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk22.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk22.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk23.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk23.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk24.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk24.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk25.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk25.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk26.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk26.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk27.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk27.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk28.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk28.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk29.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk29.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk30.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk30.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk31.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk31.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk32.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk32.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk33.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk33.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk34.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk34.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk35.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk35.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk36.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk36.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk37.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk37.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk38.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk38.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk39.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk39.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk40.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk40.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk41.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk41.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk42.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk42.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk43.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk43.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk44.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk44.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk45.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk45.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk46.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk46.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk47.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk47.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk48.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk48.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk49.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk49.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk50.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk50.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk51.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk51.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region3.Chunk52.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region3
