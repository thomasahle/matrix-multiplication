import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk16Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 2,
parent 69; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [1048090525768793057258373120, 552838958647275458773647360, 12934128136685215420891791360, 1036573047463641485200588800, 6039277411692829590109028352, 1048090525768793057258373120, 40311174068030502202245120, 1036573047463641485200588800, 40311174068030502202245120, 1048090525768793057258373120, 1048090525768793057258373120, 69347343058386307547922432, 2915310373114253351030095872, 246196711991525511064977408, 100190237772699458599768817664, 1937179391722792837063901184, 233238990307761010482610176, 100190213284646700750339047424, 233238990307761010482610176, 233238990307761010482610176, 9990403418182429949005135872, 233238990307761010482610176, 1937179391722792837063901184, 9990403418182429949005135872, 2915334861167011200459866112, 233238990307761010482610176, 233238990307761010482610176, 246196711991525511064977408, 802222695012750190754922496, 883877939760180946330976256, 49656064031470839681515520, 3478478447755021920409485312, 1342368930984095032723636224, 802222444828783691069128704, 1342368930984095032723636224, 1342368930984095032723636224, 883877939760180946330976256, 49656064031470839681515520, 2828341796226200068010541056, 0, 104446899733097534378716692480, 0, 0, 104446874156686876180423376896, 0, 0, 0, 0, 0, 0, 2828367372636858266303856640, 0, 0, 0, 18013046457680944467627999232, 0, 0, 64440484386166548927489245184, 0, 18013040469406649539664805888, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band16

namespace Band17

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1088, upper := 1107, values := [0, 0, 0, 0, 752566630981279351073406976, 0, 0, 2692257433923400292118822912, 0, 752566380797312851387613184, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3
