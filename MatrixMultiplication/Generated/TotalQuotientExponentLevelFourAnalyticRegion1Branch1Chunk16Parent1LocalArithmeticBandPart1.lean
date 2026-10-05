import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent1LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 1,
parent 67; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [2686287254616194982928082534400, 103985313081917225145603194880, 2738279911157153595500884131840, 2738279911157153595500884131840, 213459867345125575247693611008, 99559747932015119529148416, 19746166506861737412447436800, 0, 0, 0, 0, 19746166506861737412447436800, 0, 0, 0, 0, 0, 0, 0, 99559747932015119529148416, 0, 503978883151800232312832000, 162342362860699068036808704000, 0, 1726579298590206195297104691200, 0, 0, 0, 0, 0, 0, 0, 162342852160585623182665318400, 0, 0, 0, 0, 0, 0, 503978883151800232312832000, 286807950512088795766021160960, 21305074388982400892377497600, 10474624539775055669785633226752, 222923827143254877629998694400, 19746166506861737412447436800, 10474620771560652442118360399872, 19746166506861737412447436800, 19226530546154849585804083200, 726451073068229181647408332800, 19226530546154849585804083200, 222923827143254877629998694400, 726451073068229181647408332800, 286809206583556538321778769920, 19226530546154849585804083200, 19226530546154849585804083200, 21305074388982400892377497600, 30238732989108013938769920, 9740541771641944082208522240, 0, 103594757915412371717826281472, 0, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 9740571129635137390959919104, 0, 0, 0, 0, 0, 0, 30238732989108013938769920, 4981375740669075131172126720, 0, 194945940603919839265036435456, 0, 0, 194945940603919839265036435456, 0, 0, 0, 0, 0, 0, 4981375740669075131172126720, 0, 0, 0, 7279198961090326983193133056, 0, 0, 26331510284068718454790684672, 0, 7279199597550566797236764672, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96939754565383142699433984, 19226530546154849585804083200, 0, 0, 0, 0, 19226530546154849585804083200, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [0, 96939754565383142699433984, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3662750726551503607940775936, 726451073068229181647408332800, 0, 0, 0, 0, 726451073068229181647408332800, 0, 0, 0, 0, 0, 0, 0, 3662750726551503607940775936, 0, 796286635379844367054274560, 256500933319904527498157752320, 0, 2727995291772525788569425412096, 0, 0, 0, 0, 0, 0, 0, 256501706413725284628611203072, 0, 0, 0, 0, 0, 0, 796286635379844367054274560, 96939754565383142699433984, 19226530546154849585804083200, 0, 0, 0, 0, 19226530546154849585804083200, 0, 0, 0, 0, 0, 0, 0, 96939754565383142699433984, 0] }

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
  { lower := 448, upper := 512, values := [791246846548326364731146240, 254877509691297536817789665280, 0, 2710729498786623726616454365184, 0, 0, 0, 0, 0, 0, 0, 254878277892119428396784549888, 0, 0, 0, 0, 0, 0, 791246846548326364731146240, 6423352928757491616511426560, 0, 251377660252422950631231193088, 0, 0, 251377660252422950631231193088, 0, 0, 0, 0, 0, 0, 6423352928757491616511426560, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1123977154285118059947491328, 222923827143254877629998694400, 0, 0, 0, 0, 222923827143254877629998694400, 0, 0, 0, 0, 0, 0, 0, 1123977154285118059947491328, 0, 503978883151800232312832000, 162342362860699068036808704000, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent1
