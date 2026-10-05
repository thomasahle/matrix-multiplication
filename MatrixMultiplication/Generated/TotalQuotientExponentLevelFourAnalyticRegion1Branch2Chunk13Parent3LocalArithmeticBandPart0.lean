import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 2,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [1585966312591012152160320225280, 22727805408755028484476108800, 55657866732126283652341541371904, 562392291284725492073313075200, 17892102130296511785651404800, 55657691423715340082502273335296, 18375672458142363455533875200, 18375672458142363455533875200, 310935720804882623734428467200, 16924961474604808445886464000, 562392291284725492073313075200, 310935720804882623734428467200, 1586149157898862381953349320704, 17892102130296511785651404800, 16924961474604808445886464000, 22727805408755028484476108800, 39964953056635172764549973540864, 51451882882798617675494850560, 2098695222850996247289921536, 136074080657354470312193835401216, 42380103532410440348499705856, 39964951761524703419470691958784, 42447803378308859582283251712, 38047313394911609386352771072, 51451882882798617675494850560, 2098695222850996247289921536, 39993585653855757051476305772544, 3530473872529688384298287104, 39993405766872056250045617405952, 3565154362436659782965264384, 3530473872529688384298287104, 0, 0, 12630037178497794918787842048, 0, 3530472698855596694528065536, 0, 0, 0, 0, 51451882882798617675494850560, 0, 51451882882798617675494850560, 0, 1588082178338394862437607145472, 2098695222850996247289921536, 0, 2098695222850996247289921536, 0, 21818693192404827345097064448, 39964782697524761608198467616768, 51451882882798617675494850560, 2098695222850996247289921536, 136073461441250236787486728650752, 42380103532410440348499705856, 39964781402414909256268135792640, 42447803378308859582283251712, 38047313394911609386352771072, 51451882882798617675494850560, 2098695222850996247289921536, 136175298639317650884431037071360, 12630037178497794918787842048, 136174644766763622742337448312832, 12754104341351407835475345408] }

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
  { lower := 64, upper := 128, values := [55772948989925087484255550832640, 42380103532410440348499705856, 0, 42380103532410440348499705856, 0, 539896599633336472390380552192, 17176418045084651314225348608, 39993584363467655315166576246784, 3530472698855596694528065536, 39993404476484569255085023952896, 3565153177233353047126573056, 55772773705125976328764508864512, 17640645559816668917312520192, 3565154362436659782965264384, 0, 0, 12754104341351407835475345408, 0, 3565153177233353047126573056, 0, 0, 0, 0, 42447803378308859582283251712, 0, 42447803378308859582283251712, 0, 17640645559816668917312520192, 38047313394911609386352771072, 0, 38047313394911609386352771072, 0, 298498291972687318785051328512, 16247963015620616108051005440, 51451882882798617675494850560, 0, 51451882882798617675494850560, 0, 539896599633336472390380552192, 298498291972687318785051328512, 1588264962255480814925248462848, 2098695222850996247289921536, 0, 2098695222850996247289921536, 0, 17176418045084651314225348608, 16247963015620616108051005440, 21818693192404827345097064448, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 128, upper := 192, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 192, upper := 256, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13.Parent3
