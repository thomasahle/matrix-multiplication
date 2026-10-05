import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk23Parent0LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 1, for region 1, branch 1,
parent 94; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band4

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 256, upper := 320, values := [8704265901225330057884467200, 0, 8704265901225330057884467200, 0, 39389499674306337079344234496, 522255954073519803473068032, 0, 522255954073519803473068032, 0, 0, 76232276689249144626216960, 9010165675655485232995368960, 0, 85504676205801864574858690560, 0, 0, 0, 0, 0, 0, 0, 9010171855314749925695160320, 0, 0, 0, 0, 0, 0, 76232276689249144626216960, 5664264625500099449098076160, 0, 220936818016016845996252200960, 0, 0, 220936736977164287180978257920, 0, 0, 0, 0, 0, 0, 5664291638450952387522723840, 0, 0, 0, 6330666156354493551843737600, 0, 0, 23122874080788819990282240000, 0, 6330664023449710029176832000, 0, 0, 0, 0, 5664264625500099449098076160, 0, 220936818016016845996252200960, 0, 0, 220936736977164287180978257920, 0, 0, 0] }

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
  { lower := 320, upper := 384, values := [0, 0, 0, 5664291638450952387522723840, 0, 0, 0, 239196521259015729337230950400, 0, 0, 873669674728182982335528960000, 0, 239196440669802557318627328000, 0, 0, 0, 0, 13752740123936021491457458176, 0, 13752740123936021491457458176, 0, 6330666156354493551843737600, 0, 0, 23122874080788819990282240000, 0, 6330664023449710029176832000, 0, 0, 0, 0, 13665697464923768190878613504, 0, 13665697464923768190878613504, 0, 0, 4054191966267036609533706240, 0, 158135315327725245725870653440, 0, 0, 158135257324244348955399290880, 0, 0, 0, 0, 0, 0, 4054211300760668866357493760, 0, 0, 0, 73401507596650749560566579200, 0, 0, 268100350828605507454894080000, 0, 73401482866484475743698944000, 0, 0, 0, 0, 8704265901225330057884467200, 0] }

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
  { lower := 384, upper := 448, values := [8704265901225330057884467200, 0, 239196521259015729337230950400, 0, 0, 873669674728182982335528960000, 0, 239196440669802557318627328000, 0, 0, 0, 0, 210904362786689747302540640256, 0, 210904362786689747302540640256, 0, 0, 13491612146899261589720924160, 0, 13491612146899261589720924160, 0, 0, 6355871160267511777047085056, 3926081784397928586144645120, 203314949549178444639633408, 26150589769620727816563720192, 5468471056839971959272898560, 6355869085008803484722528256, 5475481917169253974605299712, 5475481917169253974605299712, 3919070924068646570812243968, 203314949549178444639633408, 16037130104747569372505047040, 9010171855314749925695160320, 16037130104747569372505047040, 9010171855314749925695160320, 39389504396672819948989448192, 13752740123936021491457458176, 0, 13752740123936021491457458176, 0, 0, 0, 210324806836751452015165440, 0, 8203799900722776611896688640, 0, 0, 8203796891597649588026081280, 0, 0, 0, 0, 0, 0, 210325809878460459972034560, 0, 0, 0, 6330666156354493551843737600, 0, 0, 23122874080788819990282240000, 0] }

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
  { lower := 448, upper := 512, values := [6330664023449710029176832000, 0, 0, 0, 0, 522255954073519803473068032, 0, 522255954073519803473068032, 0, 6330666156354493551843737600, 0, 0, 23122874080788819990282240000, 0, 6330664023449710029176832000, 0, 0, 0, 0, 13491612146899261589720924160, 0, 13491612146899261589720924160, 0, 0, 522255954073519803473068032, 0, 522255954073519803473068032, 0, 0, 7015062497582006368259276800, 0, 0, 25622644251684908637880320000, 0, 7015060134092921924222976000, 0, 0, 0, 0, 13752740123936021491457458176, 0, 13752740123936021491457458176, 0, 0, 13752740123936021491457458176, 0, 13752740123936021491457458176, 0, 0, 0, 591661459715970517237235712, 76232276689249144626216960, 591661459715970517237235712, 76232276689249144626216960, 224576860459348847782526976, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent0
