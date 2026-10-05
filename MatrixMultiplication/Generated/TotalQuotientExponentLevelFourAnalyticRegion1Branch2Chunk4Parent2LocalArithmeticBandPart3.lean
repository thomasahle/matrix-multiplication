import MatrixMultiplication.BetaFourDenseReflection
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent2LocalArithmeticRoutes

/-! Line-budgeted dense target-band certificates, part 3, for region 1, branch 2,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Band12

/-- Untrusted dense numerators and endpoints for this bounded output interval. -/
def raw : BetaFourRoutedContribution.RawDenseBand :=
  { lower := 768, upper := 832, values := [0, 194938091103876420210786304000, 0, 0, 0, 0, 0, 0, 0, 18702985605086592244488601600, 0, 0, 0, 0, 0, 0, 126632689902524256852377600, 2303561054738055711917342720, 0, 83481815105116030525232906240, 0, 0, 83481845784357268113430937600, 0, 0, 0, 0, 0, 0, 2303530375496818123719311360, 0, 0, 0, 119787679637522945671168000, 17692013410217046717759488000, 0, 184400896990153370469662720000, 0, 0, 0, 0, 0, 0, 0, 17692013410217046717759488000, 0, 0, 0, 0, 0, 0, 119787679637522945671168000, 44228372250970669668812980224, 0, 1602850850018227786084471799808, 0, 0, 1602851439059659547777874001920, 0, 0, 0, 0, 0, 0] }

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
  { lower := 832, upper := 896, values := [44227783209538907975410778112, 0, 0, 0, 57905738079342740339026821120, 0, 0, 196284813433027187064092753920, 0, 57905738079342740339026821120, 0, 0, 0, 0, 2303561054738055711917342720, 0, 83481815105116030525232906240, 0, 0, 83481845784357268113430937600, 0, 0, 0, 0, 0, 0, 2303530375496818123719311360, 0, 0, 0, 49633489782293777433451560960, 0, 0, 168244125799737588912079503360, 0, 49633489782293777433451560960, 0, 0, 0, 0, 1692496147460480844588646400, 0, 1692496147460480844588646400, 0, 160857741227530812758425600, 23757846579434319878134169600, 0, 247624061672491668916404224000, 0, 0, 0, 0, 0, 0, 0, 23757846579434319878134169600, 0, 0, 0, 0, 0, 0, 160857741227530812758425600, 70949680485932115927054155776] }

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
  { lower := 896, upper := 960, values := [0, 2571239905237573740177173512192, 0, 0, 2571240850158203857893672878080, 0, 0, 0, 0, 0, 0, 70948735565301998210554789888, 0, 0, 0, 57905738079342740339026821120, 0, 0, 196284813433027187064092753920, 0, 57905738079342740339026821120, 0, 0, 0, 0, 40081962352442169387361763328, 0, 1452583582829018931139052568576, 0, 0, 1452584116647816465173698314240, 0, 0, 0, 0, 0, 0, 40081428533644635352716017664, 0, 0, 0, 653507615466868069540445552640, 0, 0, 2215214323029878254009046794240, 0, 653507615466868069540445552640, 0, 0, 0, 0, 54633775640024321663321505792, 0, 54633775640024321663321505792, 0, 49633489782293777433451560960, 0, 0, 168244125799737588912079503360, 0, 49633489782293777433451560960, 0, 0, 0] }

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
  { lower := 960, upper := 1024, values := [0, 36490216939247967009331216384, 0, 36490216939247967009331216384, 0, 0, 4813230497702946190921826304, 163332475707954363723939840, 166177302322546724254481645568, 4041609984007466489594511360, 128580885131793860803952640, 166177371444641607766706749440, 132056044189409911095951360, 132056044189409911095951360, 2234527274047120337755176960, 121630567016561760219955200, 4041609984007466489594511360, 2234527274047120337755176960, 4813177529110761881890455552, 128580885131793860803952640, 121630567016561760219955200, 163332475707954363723939840, 67158179915822592941178748928, 518308867350580023294689280, 21141545905089448318599168, 228281679242149809859176955904, 426922830212451440240099328, 67158176934097929000183660544, 427604815564228519218118656, 383275767698718385646862336, 518308867350580023294689280, 21141545905089448318599168, 5150816546226545241962315776, 0, 5149283382921406892631654400, 0, 51287939441703570014566612992, 0, 0, 173852263326395508542482153472, 0, 51287939441703570014566612992, 0, 0, 0, 0, 33917622795108036125556473856, 0, 33917622795108036125556473856, 0, 0, 1624796301562061610805100544, 0, 1624796301562061610805100544, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- The named bounded checker validates endpoints, width, length, and every dense value. -/
theorem check_eq_true : raw.check partialRows = true := by
  unfold BetaFourRoutedContribution.RawDenseBand.check
    BetaFourRoutedContribution.RawDenseBand.IsValid raw partialRows
  decide +kernel

/-- Semantic band certificate obtained only through reflected checker soundness. -/
def certificate : BetaFourRoutedContribution.DenseBandCertificate partialRows :=
  raw.toCertificate partialRows check_eq_true

end Band15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent2
