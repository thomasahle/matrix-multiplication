import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk16Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 2,
parent 69; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [1651489636979065615199030476800, 64224596993630329479962296320, 1669839521834388566479019704320, 1669839521834388566479019704320, 55084449474111785431342252032, 237326087818220246157754368, 19956570803024545488134209536, 0, 0, 0, 0, 19956565988424342249941237760, 0, 0, 0, 0, 0, 0, 0, 237330902418423484350726144, 0, 556782060873495317688877056, 88888693166023417018913390592, 0, 886975486901505181870637187072, 0, 0, 0, 0, 0, 0, 0, 88888693166023417018913390592, 0, 0, 0, 0, 0, 0, 556718530286905461993111552, 19539538194647213423993028608, 20702074884746726785104740352, 93578558069949333332469743616, 162892641856296613388060983296, 19612491996075846427993964544, 93578539023686077227357700096, 19612491996075846427993964544, 19612491996075846427993964544, 840068407165248755332408147968, 19612491996075846427993964544, 162892641856296613388060983296, 840068407165248755332408147968, 19539557240910469529105072128, 19612491996075846427993964544, 19612491996075846427993964544, 20702074884746726785104740352, 40598691938692366914813952, 6481467210022540824295768064, 0, 64675295919901419511400628224, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band4

namespace Band5

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 320, upper := 384, values := [0, 0, 0, 6481467210022540824295768064, 0, 0, 0, 0, 0, 0, 40594059500086856603664384, 2407099401043574525966417920, 0, 88890978496253220747843993600, 0, 0, 88890956729095213770573086720, 0, 0, 0, 0, 0, 0, 2407121168201581503237324800, 0, 0, 0, 802222695012750190754922496, 883877939760180946330976256, 49656064031470839681515520, 3478478447755021920409485312, 1342368930984095032723636224, 802222444828783691069128704, 1342368930984095032723636224, 1342368930984095032723636224, 883877939760180946330976256, 49656064031470839681515520, 0, 0, 0, 0, 1342368930984095032723636224, 0, 13002283573351238105540067328, 0, 0, 0, 0, 1342368930984095032723636224, 0, 0, 237326087818220246157754368, 19956570803024545488134209536, 0, 0, 0, 0, 19956565988424342249941237760, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band5

namespace Band6

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 384, upper := 448, values := [0, 237330902418423484350726144, 0, 1342368930984095032723636224, 0, 13002283573351238105540067328, 0, 0, 0, 0, 1342368930984095032723636224, 0, 0, 10165467428213767210423812096, 854806449396218031741748641792, 0, 0, 0, 0, 854806243170842659705816350720, 0, 0, 0, 0, 0, 0, 0, 10165673653589139246356103168, 0, 1055565990406001539785162752, 168518147460586061431689969664, 0, 1681557693917436907296416333824, 0, 0, 0, 0, 0, 0, 0, 168518147460586061431689969664, 0, 0, 0, 0, 0, 0, 1055445547002258271695273984, 237326087818220246157754368, 19956570803024545488134209536, 0, 0, 0, 0, 19956565988424342249941237760, 0, 0, 0, 0, 0, 0, 0, 237330902418423484350726144, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band6

namespace Band7

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 448, upper := 512, values := [1055565990406001539785162752, 168518147460586061431689969664, 0, 1681557693917436907296416333824, 0, 0, 0, 0, 0, 0, 0, 168518147460586061431689969664, 0, 0, 0, 0, 0, 0, 1055445547002258271695273984, 2828341796226200068010541056, 0, 104446899733097534378716692480, 0, 0, 104446874156686876180423376896, 0, 0, 0, 0, 0, 0, 2828367372636858266303856640, 0, 0, 0, 883877939760180946330976256, 0, 8561306323267029776027615232, 0, 0, 0, 0, 883877939760180946330976256, 0, 0, 1971125007156884822254682112, 165750407502898308359781351424, 0, 0, 0, 0, 165750367514968842575900835840, 0, 0, 0, 0, 0, 0, 0, 1971164995086350606135197696, 0, 556782060873495317688877056, 88888693166023417018913390592, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16.Parent3
