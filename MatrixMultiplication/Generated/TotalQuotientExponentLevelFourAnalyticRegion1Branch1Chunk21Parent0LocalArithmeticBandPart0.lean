import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk21Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 86; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [363415398418478922472812969984, 44411098909363017362006081536, 12703661621286916177414645088256, 464691742246749620690258755584, 41161506306238894140395880448, 12703658490357938034839868407808, 41161506306238894140395880448, 40078308771864186399859146752, 1514310153055841421270353707008, 40078308771864186399859146752, 464691742246749620690258755584, 1514310153055841421270353707008, 363416659290329848668085026816, 40078308771864186399859146752, 40078308771864186399859146752, 44411098909363017362006081536, 10284293949844132678620936142848, 162479610787124883685480857600, 8414122701476110047998115840, 37407357692012075058868896399360, 226310886453495373704776908800, 10284154596000129084498942885888, 226601028615615239568500981760, 226601028615615239568500981760, 162189468625005017821756784640, 8414122701476110047998115840, 10304438401528475631660149243904, 33416288713887804000206585856, 10304438862991797537613692272640, 33416288713887804000206585856, 33416288713887804000206585856, 0, 0, 119777172777926930332177661952, 0, 33425999430456342108658728960, 0, 0, 0, 0, 162479610787124883685480857600, 0, 162479649525287438475539251200, 0, 355500041617148829605038129152, 8414122701476110047998115840, 0, 8414124707559528063911854080, 0, 44411098909363017362006081536, 10284294421415705698164031881216, 162479649525287438475539251200, 8414124707559528063911854080, 37407359367194409484811054874624, 226310940410221789305215385600, 10284155067572463775329017659392, 226601082641516945445350277120, 226601082641516945445350277120, 162189507293992282335404359680, 8414124707559528063911854080, 37485921289394785326150283427840, 119777172777926930332177661952, 37485922928125226436635618443264, 119777172777926930332177661952] }

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
  { lower := 64, upper := 128, values := [12394664299696990022690372845568, 226310886453495373704776908800, 0, 226310940410221789305215385600, 0, 464691742246749620690258755584, 41161506306238894140395880448, 10304288819038671267786529964032, 33425999430456342108658728960, 10304289280502752593227238342656, 33425999430456342108658728960, 12394661253770608571769210011648, 41161506306238894140395880448, 33416288713887804000206585856, 0, 0, 119777172777926930332177661952, 0, 33425999430456342108658728960, 0, 0, 0, 0, 226601028615615239568500981760, 0, 226601082641516945445350277120, 0, 40078308771864186399859146752, 226601028615615239568500981760, 0, 226601082641516945445350277120, 0, 1514310153055841421270353707008, 40078308771864186399859146752, 162189468625005017821756784640, 0, 162189507293992282335404359680, 0, 464691742246749620690258755584, 1514310153055841421270353707008, 355501274154800858582438903808, 8414122701476110047998115840, 0, 8414124707559528063911854080, 0, 40078308771864186399859146752, 40078308771864186399859146752, 44411098909363017362006081536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent0
