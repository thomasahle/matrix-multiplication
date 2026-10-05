import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 1,
parent 7; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [880745698757366128962437120, 528447419254419677377462272, 13491923172839402388043333632, 864231716905665514044391424, 5919841721296506124033327104, 842213074436731360820330496, 27523303086167691530076160, 864231716905665514044391424, 27523303086167691530076160, 842213074436731360820330496, 880745698757366128962437120, 66228547426158215228817408, 2529587122540715806459691008, 88303480134633293149634560, 98081225110643967900019326976, 996567847233718594117304320, 88303480134633293149634560, 98081201159852631197380247552, 88303480134633293149634560, 88303480134633293149634560, 3660809990724368810289135616, 90826436709908530096766976, 996567847233718594117304320, 3660809990724368810289135616, 2529587122540715806459691008, 88303480134633293149634560, 90826436709908530096766976, 88303480134633293149634560, 637589120869652394261086208, 0, 0, 2322584568547031921656332288, 0, 637589549756452108008161280, 0, 0, 0, 0, 2503532393573293747504939008, 0, 100090760592393917404192702464, 0, 0, 100090736132011275665327259648, 0, 0, 0, 0, 0, 0, 2503532393573293747504939008, 0, 0, 0, 15631217156804381278658887680, 0, 0, 56940782970830460014800404480, 0, 15631227671448503293103308800, 0, 0, 0, 0] }

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
  { lower := 1088, upper := 1107, values := [0, 0, 0, 0, 637589120869652394261086208, 0, 0, 2322584568547031921656332288, 0, 637589549756452108008161280, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent2
