import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk0Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 5, branch 2,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band8

namespace Band9

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 576, upper := 640, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band9

namespace Band10

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 640, upper := 704, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2243567915861758279942144, 64431661576872617041723392, 0, 667980518565527073723514880, 0, 0, 0, 0, 0, 0, 0, 64428652512544188140617728, 0, 0, 0, 0, 0, 0, 2244523174378719835848704, 64418021222940024986664960, 0, 3120649139246486010753712128, 0, 0, 3120627117289448815649095680, 0, 0, 0, 0, 0, 0, 64428652512544188140617728, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band10

namespace Band11

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 704, upper := 768, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent1
