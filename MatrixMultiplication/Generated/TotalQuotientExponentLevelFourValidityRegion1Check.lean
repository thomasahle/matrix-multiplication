/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityKeysRegion1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityNormalizationRegion1Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityNormalizationRegion1Chunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityNormalizationRegion1Chunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk8
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk9
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk10
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk11
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk12
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk13
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk14
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk15
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk16
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk17
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk18
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk19
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk20
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk21
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk22
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk23
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk24
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk25
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk26
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk27
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk28
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk29
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk30
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk31
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk32
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk33
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk34
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk35
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk36
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk37
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk38
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk39
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk40
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk41
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk42
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk43
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk44
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk45
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk46
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk47
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk48
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk49
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk50
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk51
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidityCoverageRegion1Chunk52
import Mathlib.Tactic.FinCases

/-!
# Semantic level-four child-row validity: region 1

For certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`, bounded parent-local index oracles check that the submitted
keys cover both labelled children of every active ordered split.  Separate bounded chunk proofs
establish each distinct key's normalization.  The reusable indexed soundness theorem then recovers
the original semantic proposition for all 105 positive parents.
-/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region1

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
      BetaThree.expectedRows Keys.Region1.entries = true := by
  unfold Keys.Region1.entries
  exact levelFourChildRowKeysNormalizedCheck_append_eq_true
      BetaThree.expectedRows Keys.Region1.Chunk0.entries (Keys.Region1.Chunk1.entries ++ Keys.Region1.Chunk2.entries)
      Normalization.Region1.Chunk0.checked (levelFourChildRowKeysNormalizedCheck_append_eq_true
      BetaThree.expectedRows Keys.Region1.Chunk1.entries (Keys.Region1.Chunk2.entries)
      Normalization.Region1.Chunk1.checked (Normalization.Region1.Chunk2.checked))

/-- Every positive parent in this region has normalized left and right child rows. -/
theorem childRowsValid :
    ∀ parent, LevelFourChildRowsValid
      Top.expectedRows BetaThree.expectedRows 1 1 parent xzy := by
  intro parent
  fin_cases parent
  · convert
      Coverage.Region1.Chunk0.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk0.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk1.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk1.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk2.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk2.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk3.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk3.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk4.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk4.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk5.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk5.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk6.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk6.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk7.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk7.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk8.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk8.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk9.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk9.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk10.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk10.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk11.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk11.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk12.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk12.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk13.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk13.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk14.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk14.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk15.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk15.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk16.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk16.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk17.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk17.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk18.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk18.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk19.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk19.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk20.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk20.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk21.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk21.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk22.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk22.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk23.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk23.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk24.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk24.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk25.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk25.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk26.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk26.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk27.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk27.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk28.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk28.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk29.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk29.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk30.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk30.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk31.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk31.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk32.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk32.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk33.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk33.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk34.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk34.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk35.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk35.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk36.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk36.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk37.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk37.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk38.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk38.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk39.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk39.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk40.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk40.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk41.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk41.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk42.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk42.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk43.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk43.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk44.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk44.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk45.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk45.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk46.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk46.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk47.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk47.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk48.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk48.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk49.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk49.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk50.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk50.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk51.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk51.childRowsValid1
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl
  · convert
      Coverage.Region1.Chunk52.childRowsValid0
        BetaThree.expectedRows normalizationChecked using 1
    apply Fin.ext
    rfl

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourValidity.Region1
