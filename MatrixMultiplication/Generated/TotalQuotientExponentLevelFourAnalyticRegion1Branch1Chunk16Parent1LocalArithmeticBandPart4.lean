import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 4, for region 1, branch 1,
parent 67; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band16

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 1024, upper := 1088, values := [794229869532485936322969600, 505878897791392316129280000, 12257445693485435819812454400, 784112291576658090000384000, 21728706132531221264156590080, 799288658510399859484262400, 30352733867483538967756800, 784112291576658090000384000, 30352733867483538967756800, 799288658510399859484262400, 799288658510399859484262400, 158167292107176371130728448, 7888239657070798944224673792, 107419728031911050018291712, 304904005240369404303240069120, 1123977154285118059947491328, 99559747932015119529148416, 304903983756121896417849507840, 99559747932015119529148416, 96939754565383142699433984, 3662750726551503607940775936, 96939754565383142699433984, 1123977154285118059947491328, 3662750726551503607940775936, 7888246818486634906021527552, 96939754565383142699433984, 96939754565383142699433984, 107419728031911050018291712, 7293462509349332508479586304, 0, 0, 26383608155318363134332239872, 0, 7293463141003950045142188032, 0, 0, 0, 0, 6423352928757491616511426560, 0, 251377660252422950631231193088, 0, 0, 251377660252422950631231193088, 0, 0, 0, 0, 0, 0, 6423352928757491616511426560, 0, 0, 0, 111602777468025914166612066304, 0, 0, 401431871717697542418451136512, 0, 111602814699320062435521462272, 0, 0, 0, 0] }

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
  { lower := 1088, upper := 1107, values := [9903519133691421481781690368, 0, 9903521494874662916604297216, 0, 4606772438760057708608487424, 0, 0, 16570423466376329979989327872, 0, 4606773975604423349535506432, 0, 0, 0, 0, 9903519133691421481781690368, 0, 9903521494874662916604297216, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent1
