import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21Parent1LocalArithmeticBandPart0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21Parent1LocalArithmeticBandPart1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21Parent1LocalArithmeticBandPart2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21Parent1LocalArithmeticBandPart3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21Parent1LocalArithmeticBandPart4

/-! Compositional beta-four arithmetic for region 1, branch 2, parent
87; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  Every decided normalization, support check, target
output check is bounded by at most 64 routed contributions or one
64-target band. Ordinary theorems compose those local facts; no decision
reduces the complete parent route or complete dense row. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Consecutive dense target-band certificates in increasing order. -/
def bands : List (BetaFourRoutedContribution.DenseBandCertificate partialRows) :=
  [
    Band0.certificate,
    Band1.certificate,
    Band2.certificate,
    Band3.certificate,
    Band4.certificate,
    Band5.certificate,
    Band6.certificate,
    Band7.certificate,
    Band8.certificate,
    Band9.certificate,
    Band10.certificate,
    Band11.certificate,
    Band12.certificate,
    Band13.certificate,
    Band14.certificate,
    Band15.certificate,
    Band16.certificate,
    Band17.certificate
  ]

/-- The named endpoint checker verifies exact, consecutive coverage of the padded parent row. -/
theorem bands_layout_check :
    BetaFourRoutedContribution.DenseBandCover.layoutCheck 0
      MatrixMultiplication.BetaFourLocalGeometry.parentSupportWidth bands = true := by
  unfold bands BetaFourRoutedContribution.DenseBandCover.layoutCheck
    BetaFourRoutedContribution.DenseBandCover.IsLayout
  decide +kernel

/-- The band certificates cover the whole padded parent row with no gap or overlap. -/
theorem bands_cover : BetaFourRoutedContribution.DenseBandCover partialRows 0
    MatrixMultiplication.BetaFourLocalGeometry.parentSupportWidth bands :=
  BetaFourRoutedContribution.DenseBandCover.of_layoutCheck_eq_true bands_layout_check

/-- Dense row assembled from the already-checked bounded output bands. -/
def expectedDenseNumerators : List ℕ :=
  BetaFourRoutedContribution.denseBandValues bands

/-- Nonzero pooled numerators, retaining their parent-support order. -/
def expectedPooledNumerators : List ℕ :=
  MatrixMultiplication.DyadicEntropyForm.dropZeros expectedDenseNumerators

/-- The certificate reconstructs the nonzero routed row and rules out absent-support sentinels. -/
theorem routedPooledNumerators_eq_and_targetsBelowSupport :
    MatrixMultiplication.DyadicEntropyForm.dropZeros
      (BetaFourRoutedContribution.scatterOn expectedRoutedContributions
        (List.range MatrixMultiplication.BetaFourLocalGeometry.parentSupportWidth)) =
        expectedPooledNumerators ∧
      BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length
        expectedRoutedContributions := by
  have h :=
    BetaFourRoutedContribution.dropZeros_scatterOn_range_eq_denseBandValues_and_allTargetsBelow
      expectedRoutedRows routeChunks partialRows bands
      MatrixMultiplication.BetaFourLocalGeometry.parentSupportWidth ParentSupport.codes.length
      rfl routeChunks_normalized routeChunks_bounded bands_cover
  rw [expectedRoutedRows_flatten] at h
  change _ = expectedPooledNumerators ∧ _ at h
  exact h

/-- The compact arithmetic component consumed by the semantic parent wrapper. -/
theorem routedPooledNumerators_eq :
    MatrixMultiplication.DyadicEntropyForm.dropZeros
      (BetaFourRoutedContribution.scatterOn expectedRoutedContributions
        (List.range MatrixMultiplication.BetaFourLocalGeometry.parentSupportWidth)) =
      expectedPooledNumerators := by
  exact routedPooledNumerators_eq_and_targetsBelowSupport.1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21.Parent1
