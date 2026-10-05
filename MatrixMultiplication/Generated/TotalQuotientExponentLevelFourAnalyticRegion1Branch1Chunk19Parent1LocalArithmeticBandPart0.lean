import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk19Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 0, for region 1, branch 1,
parent 79; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band0

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 0, upper := 64, values := [1368392773571790299795801767936, 19033328104012721726574034944, 52855238886662687076780844515328, 199153603820035551724396609536, 17640645559816668917312520192, 52855233352049169153556654063616, 17640645559816668917312520192, 17176418045084651314225348608, 648990065595360609115865874432, 17176418045084651314225348608, 199153603820035551724396609536, 648990065595360609115865874432, 1368396249233521691854679048192, 17176418045084651314225348608, 17176418045084651314225348608, 19033328104012721726574034944, 39471283618908032019630940749824, 37911900144757876742265241600, 1963294828924961474153021440, 143511005977745197101711060107264, 52805860915912756891012300800, 39469109904336342029513699360768, 52873560737599824528052060160, 52873560737599824528052060160, 37844200323070809105225482240, 1963294828924961474153021440, 39436562351804453572064533544960, 3674707191248749283053142016, 39436560159470822951512484872192, 3674707191248749283053142016, 3674707191248749283053142016, 0, 0, 13386078803668915161374130176, 0, 3674709663112455160133058560, 0, 0, 0, 0, 37911900144757876742265241600, 0, 37911927261471665095306117120, 0, 1366428434397743427824486711296, 1963294828924961474153021440, 0, 1963296233183354085292638208, 0, 19033328104012721726574034944, 39471281433168837122902833758208, 37911927261471665095306117120, 1963296233183354085292638208, 143510998496240992413294587281408, 52805898685621247811319234560, 39469107718045570457273251135488, 52873598555731018641846566912, 52873598555731018641846566912, 37844227391361894264778784768, 1963296233183354085292638208, 143382370226398912853949357752320, 13386078803668915161374130176, 143382362720303255012038842253312, 13386078803668915161374130176] }

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
  { lower := 64, upper := 128, values := [52777975134157966854203293827072, 52805860915912756891012300800, 0, 52805898685621247811319234560, 0, 199153603820035551724396609536, 17640645559816668917312520192, 39434396535390009812336529899520, 3674709663112455160133058560, 39434394342506195254456904318976, 3674709663112455160133058560, 52777969500374752790716553887744, 17640645559816668917312520192, 3674707191248749283053142016, 0, 0, 13386078803668915161374130176, 0, 3674709663112455160133058560, 0, 0, 0, 0, 52873560737599824528052060160, 0, 52873598555731018641846566912, 0, 17176418045084651314225348608, 52873560737599824528052060160, 0, 52873598555731018641846566912, 0, 648990065595360609115865874432, 17176418045084651314225348608, 37844200323070809105225482240, 0, 37844227391361894264778784768, 0, 199153603820035551724396609536, 648990065595360609115865874432, 1366431867558176474056557068288, 1963294828924961474153021440, 0, 1963296233183354085292638208, 0, 17176418045084651314225348608, 17176418045084651314225348608, 19033328104012721726574034944, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19.Parent1
