import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk4Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 0, branch 1,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 200381291702166433285799936, 9480970745061677922074492928, 0, 99427992728382993383731232768, 0, 0, 0, 0, 0, 0, 0, 9481041549492527787197595648, 0, 0, 0, 0, 0, 0, 200360050261447382971449344, 3428918954024458593203388416, 0, 122020532705745236294998425600, 0, 0, 122053590525340102387298205696, 0, 0, 0, 0, 0, 0, 3462246342420693262868152320, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band0

namespace Band1

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 64, upper := 128, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3428918954024458593203388416, 0, 0, 11536912299589398823004274688, 0, 3430340997430643169198866432, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 200381291702166433285799936, 0, 200557067426432184647417856, 0, 200557067426432184647417856, 9489228763808042387282853888] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band1

namespace Band2

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 128, upper := 192, values := [0, 99514119908717241279770001408, 0, 0, 0, 0, 0, 0, 0, 9489299630371678611516162048, 0, 0, 0, 0, 0, 0, 200535807568805408154845184, 11536912299589398823004274688, 0, 410772677290860783539553566720, 0, 0, 410885515998288889573894258688, 0, 0, 0, 0, 0, 0, 11650666136779692081309286400, 0, 0, 0, 122020532705745236294998425600, 0, 0, 410772677290860783539553566720, 0, 122070313078923159124783923200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band2

namespace Band3

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 192, upper := 256, values := [0, 0, 0, 0, 0, 9480970745061677922074492928, 0, 9489228763808042387282853888, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3430340997430643169198866432, 0, 122070313078923159124783923200, 0, 0, 122103375352135015073161674752, 0, 0, 0, 0, 0, 0, 3463673060955667166973132800, 0, 0, 0, 122053590525340102387298205696, 0, 0, 410885515998288889573894258688, 0, 122103375352135015073161674752, 0, 0, 0, 0, 99427992728382993383731232768, 0, 99514119908717241279770001408, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4.Parent2
