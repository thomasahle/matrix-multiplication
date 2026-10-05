import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 2,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [1158075377327088835045097472, 1101973663510597449906388992, 20379542562017337226932781056, 1189356332909617364940619776, 38692192884638327906659991552, 1449804289172844037766381568, 51851583981908704446382080, 1189356332909617364940619776, 51851583981908704446382080, 1454224424200810025686401024, 1158075377327088835045097472, 321755289925008865684881408, 21537325095311931085871382528, 0, 790892873743389100535244128256, 0, 0, 790867211857849598965318680576, 0, 0, 0, 0, 0, 0, 21563011157615384261377916928, 0, 0, 0, 131117326766424676137059745792, 0, 0, 450804556993484385478521126912, 0, 131117326766424676137059745792, 0, 0, 0, 0, 5242450423909284581407195136, 0, 187914868705194309486865547264, 0, 0, 187914898406758111168457342976, 0, 0, 0, 0, 0, 0, 5242445973632276798977867776, 0, 0, 0, 190750678650770771306958815232, 0, 0, 667440055048566065628341862400, 0, 190750678650770771306958815232, 0, 0, 0, 0] }

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
  { lower := 1088, upper := 1107, values := [91356118672898396767458951168, 0, 91356094000378198180933664768, 0, 8485321043869241583870148608, 0, 0, 29761594395284622209701642240, 0, 8485321043869241583870148608, 0, 0, 0, 0, 86907270596028777166241005568, 0, 86907248044884147056314155008, 0, 79228162514264337593543950336] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10.Parent0
