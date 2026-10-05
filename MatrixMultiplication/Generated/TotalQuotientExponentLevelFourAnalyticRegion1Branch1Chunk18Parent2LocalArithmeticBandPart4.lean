import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk18Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 1,
parent 76; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [1254902742798359893087617024, 799301110062649613431603200, 19367065896818000133447745536, 1238916720597106900818984960, 6377624444017102609157455872, 1262895753898986389221933056, 47958066603758976805896192, 1238916720597106900818984960, 47958066603758976805896192, 1262895753898986389221933056, 1262895753898986389221933056, 95830798569432973226016768, 2651837796458980891573616640, 125885857327799061159346176, 99222786349322031493615190016, 1317195921795751152130719744, 116674697035521081074515968, 99222749990789462212088954880, 116674697035521081074515968, 113604310271428421046239232, 4292400696201538719530876928, 113604310271428421046239232, 1317195921795751152130719744, 4292400696201538719530876928, 2651849915969837318749028352, 113604310271428421046239232, 113604310271428421046239232, 125885857327799061159346176, 742570030231851405810860032, 0, 0, 2712250635422256182643916800, 0, 742569780047884906125066240, 0, 0, 0, 0, 2594247703638137737442230272, 0, 101189628430639213588808466432, 0, 0, 101189591314637215780583768064, 0, 0, 0, 0, 0, 0, 2594260075638803673517129728, 0, 0, 0, 17989357829165174379482447872, 0, 0, 65706458942003690102115532800, 0, 17989351768256824661287895040, 0, 0, 0, 0] }

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
  { lower := 1088, upper := 1107, values := [0, 0, 0, 0, 742570030231851405810860032, 0, 0, 2712250635422256182643916800, 0, 742569780047884906125066240, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18.Parent2
