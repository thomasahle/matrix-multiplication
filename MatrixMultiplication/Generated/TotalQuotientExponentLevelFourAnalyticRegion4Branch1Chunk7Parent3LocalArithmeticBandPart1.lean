import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk7Parent3LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 4, branch 1,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [0, 138297570860224178752061440, 0, 0, 479310449703037267829850112, 0, 138329516548579880645689344, 0, 0, 0, 0, 138329516548579880645689344, 7110644060404893349620744192, 0, 0, 0, 0, 7112297177456527781463588864, 0, 0, 0, 0, 0, 0, 0, 136743803119542148062511104, 0, 781213107891110548737097728, 24759396207107484310455713792, 1280507303188014667178967040, 260235472039107921260801163264, 1129859385165895294569676800, 188309897527649215761612800, 1252260818558867284814725120, 1280507303188014667178967040, 1129859385165895294569676800, 22813744085474702489519390720, 1129859385165895294569676800, 24750223763640269035901288448, 1252260818558867284814725120, 188309897527649215761612800, 1129859385165895294569676800, 188309897527649215761612800, 1280507303188014667178967040, 1280507303188014667178967040, 781128150205440279168679936, 7316912376551444921297403904, 0, 260216416248913520511166709760, 0, 0, 260235472039107921260801163264, 0, 0, 0, 0, 0, 0, 7297984481309207445872050176, 0, 0, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30710646819373688542986240, 0, 1129858140010670319174942720, 0, 0, 1129859385165895294569676800, 0, 0, 0, 0, 0, 0, 30709401664148713148252160, 0, 0, 0, 7109001934958136343312465920, 0, 0, 24638313552364465860447830016, 0, 7110644060404893349620744192, 0, 0, 0, 0, 5118441136562281423831040, 0, 188309690001778386529157120, 0, 0, 188309897527649215761612800, 0, 0, 0, 0, 0, 0, 5118233610691452191375360, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 384, upper := 448, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

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
  { lower := 448, upper := 512, values := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34037633558139171468476416, 0, 1252259438511826270418894848, 0, 0, 1252260818558867284814725120, 0, 0, 0, 0, 0, 0, 34036253511098157072646144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34805399728623513682051072, 0, 1280505892012093028398268416, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent3
