import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 1,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 262566983814825419049187409920, 0, 0, 0, 0, 0, 0, 0, 24688048252696032328485437440, 0, 0, 0, 0, 0, 0, 76641840524545680945971200, 2137361378540294580448788480, 0, 83647984102072554068503429120, 0, 0, 83648014781313791656701460480, 0, 0, 0, 0, 0, 0, 2137392057781532168646819840, 0, 0, 0, 78831607396675557544427520, 25393344524374757145512509440, 0, 270068897638106145307735621632, 0, 0, 0, 0, 0, 0, 0, 25393421059915918966442164224, 0, 0, 0, 0, 0, 0, 78831607396675557544427520, 67113147286165249826091958272, 0, 2626546700805078197751007674368, 0, 0, 2626547664133253058020425859072, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band12

namespace Band13

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 832, upper := 896, values := [67114110614340110095510142976, 0, 0, 0, 42774789139356797201756979200, 0, 0, 153321733396289136567412326400, 0, 42787219420204791152771072000, 0, 0, 0, 0, 2137361378540294580448788480, 0, 83647984102072554068503429120, 0, 0, 83648014781313791656701460480, 0, 0, 0, 0, 0, 0, 2137392057781532168646819840, 0, 0, 0, 41649136793584249906973900800, 0, 0, 149286950938492054026164633600, 0, 41661239961778349280329728000, 0, 0, 0, 0, 1798880976256368641342177280, 0, 1798882262916767782583402496, 0, 76641840524545680945971200, 24687973843142125002581606400, 0, 262566983814825419049187409920, 0, 0, 0, 0, 0, 0, 0, 24688048252696032328485437440, 0, 0, 0, 0, 0, 0, 76641840524545680945971200, 65403258183333014161732927488] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band13

namespace Band14

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 896, upper := 960, values := [0, 2559628313523420154496204931072, 0, 0, 2559629252308202024695064690688, 0, 0, 0, 0, 0, 0, 65404196968114884360592687104, 0, 0, 0, 41649136793584249906973900800, 0, 0, 149286950938492054026164633600, 0, 41661239961778349280329728000, 0, 0, 0, 0, 68395564113289426574361231360, 0, 2676735491266321730192109731840, 0, 0, 2676736473002041333014446735360, 0, 0, 0, 0, 0, 0, 68396545849009029396698234880, 0, 0, 0, 1309133678133472503832720179200, 0, 0, 4692451998418006995471066726400, 0, 1309514110149951897649283072000, 0, 0, 0, 0, 36325790036660863531619450880, 0, 36325816018899891351522902016, 0, 41649136793584249906973900800, 0, 0, 149286950938492054026164633600, 0, 41661239961778349280329728000, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band14

namespace Band15

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 960, upper := 1024, values := [0, 36964102641138929823708610560, 0, 36964129079934873467923464192, 0, 0, 3726519150745622782091984896, 75145578995866914940518400, 144225005017139956936169488384, 848071534381926611471564800, 75145578995866914940518400, 144225031132447968845895827456, 75145578995866914940518400, 75145578995866914940518400, 3115321003514368387962634240, 77292595538605969653104640, 848071534381926611471564800, 3115321003514368387962634240, 3726555965835107887929622528, 75145578995866914940518400, 77292595538605969653104640, 75145578995866914940518400, 56788940693843440146053070848, 192282971101302834270830592, 9978756983301145091899392, 203953950011088586652598140928, 309725264827847080352415744, 56804701392890514759693107200, 309725264827847080352415744, 322774408575240885472591872, 192282971101302834270830592, 9594958637789562588364800, 2642578972085859455221104640, 0, 2642580258746258596462329856, 0, 54031312597082270149587763200, 0, 0, 193669557974259961979889254400, 0, 54047014004469209877184512000, 0, 0, 0, 0, 44101598127575489271614668800, 0, 44101629671507855314947932160, 0, 0, 1798880976256368641342177280, 0, 1798882262916767782583402496, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent2
