import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk7Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 2, for region 4, branch 1,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band8

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 512, upper := 576, values := [0, 1280507303188014667178967040, 0, 0, 0, 0, 0, 0, 34803988552701874901352448, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30710646819373688542986240, 0, 1129858140010670319174942720, 0, 0, 1129859385165895294569676800, 0] }

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
  { lower := 576, upper := 640, values := [0, 0, 0, 0, 0, 30709401664148713148252160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 620099143694520394497130496, 0, 22813718943715451528007385088, 0, 0, 22813744085474702489519390720, 0, 0, 0, 0, 0, 0, 620074001935269432985124864, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30710646819373688542986240, 0, 1129858140010670319174942720, 0, 0, 1129859385165895294569676800, 0, 0, 0, 0] }

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
  { lower := 640, upper := 704, values := [0, 0, 30709401664148713148252160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22040279962115409010753536, 693671353706459717886279680, 34803988552701874901352448, 7297984481309207445872050176, 30709401664148713148252160, 5118233610691452191375360, 34036253511098157072646144, 34803988552701874901352448, 30709401664148713148252160, 620074001935269432985124864, 30709401664148713148252160, 693422676024024501590163456, 34036253511098157072646144, 5118233610691452191375360, 30709401664148713148252160, 5118233610691452191375360, 34803988552701874901352448, 34803988552701874901352448, 22037873851245566516789248, 695120028350496240381722624, 0, 24748515000458415985517395968, 0, 0, 24750223763640269035901288448, 0, 0, 0, 0, 0, 0, 693422676024024501590163456, 0, 0, 0, 7110654670240474787888496640, 0, 0, 24644041587112222615322755072, 0, 7112297177456527781463588864, 0, 0, 0] }

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
  { lower := 704, upper := 768, values := [0, 34037633558139171468476416, 0, 1252259438511826270418894848, 0, 0, 1252260818558867284814725120, 0, 0, 0, 0, 0, 0, 34036253511098157072646144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent3
